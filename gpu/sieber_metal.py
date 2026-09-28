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
