"""Arity-3 falsifier on the GPU (GPU_SEARCH.md, section 4), via MLX custom Metal kernels.

One logical thread per triple (i, j, k) in I x J x K (index lists into the
current carrier).  For each test t the thread checks, in order:
  1. the cheap output test: (h_i, h_j, h_k) must lie outside R_t;
  2. relatedness: (T[i][a], T[j][b], T[k][c]) in R_t for every (a, b, c) in rel_t,
     where rel_t is R_t lifted to the previous carrier (never R lifted to T).
A thread that passes both claims the result slot of test t atomically.

The same kernel serves two levels:
  * T = D1 (11 x 3), rel = ground triples of R: candidates h : D1 -> B;
  * T = D2 (355 x 11), rel = rel1 (R lifted to D1): candidates h : D2 -> B.
"""
import time

import mlx.core as mx
import numpy as np

SOURCE = r"""
    uint tid = thread_position_in_grid.x;
    uint nI = dims[0], nJ = dims[1], nK = dims[2], m = dims[3], ntests = dims[4];
    if (tid >= nI * nJ * nK) return;
    uint i = I[tid / (nJ * nK)];
    uint j = J[(tid / nK) % nJ];
    uint k = K[tid % nK];
    uint out = 9u * h[i] + 3u * h[j] + h[k];
    for (uint t = 0; t < ntests; ++t) {
        if ((masks[t] >> out) & 1u) continue;                       // image in R_t
        if (atomic_load_explicit(&res[4 * t], memory_order_relaxed) != 0u) continue;
        uint mask = masks[t];
        bool related = true;
        for (uint r = rel_off[t]; r < rel_off[t + 1]; ++r) {
            uint a = rel[3 * r], b = rel[3 * r + 1], c = rel[3 * r + 2];
            uint v = 9u * T[m * i + a] + 3u * T[m * j + b] + T[m * k + c];
            if (!((mask >> v) & 1u)) { related = false; break; }
        }
        if (!related) continue;
        // Metal only has the weak CAS, which may fail spuriously: retry until the
        // slot is really taken, so a unique witness is never lost.
        uint expected = 0u;
        bool claimed = false;
        while (true) {
            expected = 0u;
            if (atomic_compare_exchange_weak_explicit(&res[4 * t], &expected, 1u,
                                                      memory_order_relaxed, memory_order_relaxed)) {
                claimed = true;
                break;
            }
            if (expected != 0u) break;
        }
        if (claimed) {
            atomic_store_explicit(&res[4 * t + 1], i, memory_order_relaxed);
            atomic_store_explicit(&res[4 * t + 2], j, memory_order_relaxed);
            atomic_store_explicit(&res[4 * t + 3], k, memory_order_relaxed);
        }
    }
"""

_kernel = None
COMPILE_SECONDS = None


def kernel():
    global _kernel, COMPILE_SECONDS
    if _kernel is None:
        t = time.perf_counter()
        _kernel = mx.fast.metal_kernel(
            name="sieber_arity3_falsifier",
            input_names=["T", "h", "rel", "rel_off", "masks", "I", "J", "K", "dims"],
            output_names=["res"],
            source=SOURCE,
            atomic_outputs=True,
        )
        COMPILE_SECONDS = time.perf_counter() - t
    return _kernel


class Level:
    """Device-resident data for one level: carrier table T and lifted tests."""

    def __init__(self, T, tests, rels):
        T = np.asarray(T, dtype=np.uint8)
        self.n, self.m = T.shape
        self.ntests = len(tests)
        self.masks_np = np.array(tests, dtype=np.uint32)
        offs = np.zeros(self.ntests + 1, dtype=np.uint32)
        offs[1:] = np.cumsum([len(r) for r in rels])
        flat = np.array([x for r in rels for t in r for x in t], dtype=np.uint16)
        self.T = mx.array(T.reshape(-1))
        self.rel = mx.array(flat if len(flat) else np.zeros(3, np.uint16))
        self.rel_off = mx.array(offs)
        self.masks = mx.array(self.masks_np)
        self.all_idx = mx.array(np.arange(self.n, dtype=np.uint16))

    def falsify(self, h, I=None, J=None, K=None, threadgroup=256):
        """Per test, a witness triple (i, j, k) or None.  Restrict to I x J x K."""
        I = self.all_idx if I is None else mx.array(np.asarray(I, dtype=np.uint16))
        J = self.all_idx if J is None else mx.array(np.asarray(J, dtype=np.uint16))
        K = self.all_idx if K is None else mx.array(np.asarray(K, dtype=np.uint16))
        total = I.size * J.size * K.size
        dims = mx.array(np.array([I.size, J.size, K.size, self.m, self.ntests], dtype=np.uint32))
        h = mx.array(np.asarray(h, dtype=np.uint8))
        res, = kernel()(
            inputs=[self.T, h, self.rel, self.rel_off, self.masks, I, J, K, dims],
            grid=(max(total, 1), 1, 1),
            threadgroup=(threadgroup, 1, 1),
            output_shapes=[(4 * self.ntests,)],
            output_dtypes=[mx.uint32],
            init_value=0,
        )
        res = np.array(res).reshape(self.ntests, 4)
        return [tuple(int(x) for x in r[1:]) if r[0] else None for r in res]


# ---------------------------------------------------------------------------
# M2: batched, output-bucketed falsification
# ---------------------------------------------------------------------------
# Work is a list of blocks, one per (candidate c, output pattern p = 9u + 3v + z)
# with p non-constant: the triples H_u x H_v x H_z of candidate c, where H_x are
# the inputs on which c takes value x.  Threads find their block by binary search
# over prefix offsets.  Only the tests that forbid pattern p are scanned, in the
# learned order given by pat_tests.  A candidate dies at its first witness.
BATCH_SOURCE = r"""
    uint tid = thread_position_in_grid.x;
    uint nblk = dims[0], m = dims[1], n = dims[2];
    if (tid >= blk_off[nblk]) return;
    uint lo = 0, hi = nblk;                       // largest b with blk_off[b] <= tid
    while (hi - lo > 1) { uint mid = (lo + hi) / 2; if (blk_off[mid] <= tid) lo = mid; else hi = mid; }
    uint b = lo;
    uint c = blk_desc[2 * b], p = blk_desc[2 * b + 1];
    if (atomic_load_explicit(&res[5 * c], memory_order_relaxed) != 0u) return;
    uint u = p / 9u, v = (p / 3u) % 3u, z = p % 3u;
    uint su = BS[4 * c + u], sv = BS[4 * c + v], sz = BS[4 * c + z];
    uint nv = BS[4 * c + v + 1] - sv, nz = BS[4 * c + z + 1] - sz;
    uint local = tid - blk_off[b];
    uint i = BI[n * c + su + local / (nv * nz)];
    uint j = BI[n * c + sv + (local / nz) % nv];
    uint k = BI[n * c + sz + local % nz];
    for (uint q = pat_off[p]; q < pat_off[p + 1]; ++q) {
        uint t = pat_tests[q];
        uint mask = masks[t];
        bool related = true;
        for (uint r = rel_off[t]; r < rel_off[t + 1]; ++r) {
            uint a = rel[3 * r], bb = rel[3 * r + 1], cc = rel[3 * r + 2];
            uint val = 9u * T[m * i + a] + 3u * T[m * j + bb] + T[m * k + cc];
            if (!((mask >> val) & 1u)) { related = false; break; }
        }
        if (!related) continue;
        uint expected = 0u;
        bool claimed = false;
        while (true) {
            expected = 0u;
            if (atomic_compare_exchange_weak_explicit(&res[5 * c], &expected, 1u,
                                                      memory_order_relaxed, memory_order_relaxed)) {
                claimed = true; break;
            }
            if (expected != 0u) break;
        }
        if (claimed) {
            atomic_store_explicit(&res[5 * c + 1], i, memory_order_relaxed);
            atomic_store_explicit(&res[5 * c + 2], j, memory_order_relaxed);
            atomic_store_explicit(&res[5 * c + 3], k, memory_order_relaxed);
            atomic_store_explicit(&res[5 * c + 4], t, memory_order_relaxed);
        }
        return;
    }
"""

_batch_kernel = None


def batch_kernel():
    global _batch_kernel
    if _batch_kernel is None:
        _batch_kernel = mx.fast.metal_kernel(
            name="sieber_arity3_batch_falsifier",
            input_names=["T", "rel", "rel_off", "masks", "BI", "BS", "blk_off", "blk_desc",
                         "pat_tests", "pat_off", "dims"],
            output_names=["res"],
            source=BATCH_SOURCE,
            atomic_outputs=True,
        )
    return _batch_kernel


def pattern_tests(masks, order):
    """For each output pattern p (0..26), the tests (in `order`) that forbid it."""
    lists = [[t for t in order if not (int(masks[t]) >> p) & 1] for p in range(27)]
    off = np.zeros(28, dtype=np.uint32)
    off[1:] = np.cumsum([len(l) for l in lists])
    return np.array([t for l in lists for t in l], dtype=np.uint16), off


def batch_falsify(level, H, order, threadgroup=256, max_threads=1 << 30):
    """H: (batch, n) uint8 candidate tables.  Returns per candidate None or
    (i, j, k, test).  Chunks the batch so one dispatch has <= max_threads threads."""
    H = np.asarray(H, dtype=np.uint8)
    batch, n = H.shape
    pt, po = pattern_tests(level.masks_np, order)
    pt, po = mx.array(pt), mx.array(po)
    BI = np.argsort(H, axis=1, kind="stable").astype(np.uint16)
    counts = np.stack([(H == x).sum(axis=1) for x in range(3)], axis=1)
    BS = np.zeros((batch, 4), dtype=np.uint32)
    BS[:, 1:] = np.cumsum(counts, axis=1)
    pats = [p for p in range(27) if len({p // 9, (p // 3) % 3, p % 3}) > 1]
    sizes = np.stack([counts[:, p // 9] * counts[:, (p // 3) % 3] * counts[:, p % 3] for p in pats], axis=1)
    out = [None] * batch
    start = 0
    while start < batch:
        # grow the chunk while it fits
        end, total = start, 0
        while end < batch and (total + int(sizes[end].sum()) <= max_threads or end == start):
            total += int(sizes[end].sum())
            end += 1
        cs = range(start, end)
        desc, offs = [], [0]
        for c in cs:
            for pi, p in enumerate(pats):
                s = int(sizes[c, pi])
                if s:
                    desc += [c - start, p]
                    offs.append(offs[-1] + s)
        nblk = len(offs) - 1
        if nblk:
            dims = mx.array(np.array([nblk, level.m, n], dtype=np.uint32))
            res, = batch_kernel()(
                inputs=[level.T, level.rel, level.rel_off, level.masks,
                        mx.array(BI[start:end].reshape(-1)), mx.array(BS[start:end].reshape(-1)),
                        mx.array(np.array(offs, dtype=np.uint32)), mx.array(np.array(desc, dtype=np.uint32)),
                        pt, po, dims],
                grid=(offs[-1], 1, 1),
                threadgroup=(threadgroup, 1, 1),
                output_shapes=[(5 * (end - start),)],
                output_dtypes=[mx.uint32],
                init_value=0,
            )
            res = np.array(res).reshape(-1, 5)
            for c in cs:
                r = res[c - start]
                if r[0]:
                    out[c] = tuple(int(x) for x in r[1:])
        start = end
    return out
