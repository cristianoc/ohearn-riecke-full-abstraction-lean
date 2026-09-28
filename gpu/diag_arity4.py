#!/usr/bin/env python3
"""Diagnostic: does arity 4 reject the M2 survivors?

Tests: the elementary relations S^4_{A,B} with A nonempty (A empty only says
"constant on B", which every monotone h preserves).  Intersections of
generators are not included, so the kill rate is a lower bound for arity 4.

For each candidate and test, only the output patterns the test forbids are
dispatched: blocks H_p0 x H_p1 x H_p2 x H_p3.  Each thread scans the test's
relation lifted to D1 (4-tuples of D1 indices), most frequently failing entries
first.  Witnesses are re-verified on the CPU.
"""
import json, os, random, sys, time
from itertools import product

import mlx.core as mx
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sieber_cpu as C

HERE = os.path.dirname(os.path.abspath(__file__))
rng = random.Random(4)

D1 = C.carrier_D1()
D2 = sorted(C.definable_D2(D1))
A = np.array(D2, dtype=np.uint8)
N = len(D2)
B1A = np.array(D1, dtype=np.uint8)
ALL4 = list(product(range(3), repeat=4))


def gen4():
    subsets = [frozenset(i for i in range(4) if s >> i & 1) for s in range(16)]
    out = {}
    for Aset in subsets:
        for Bset in subsets:
            if Aset and Aset <= Bset:
                R = np.array([any(g[i] == 0 for i in Aset) or len({g[i] for i in Bset}) <= 1
                              for g in ALL4])
                if not R.all():
                    out.setdefault(R.tobytes(), (R, sorted(Aset), sorted(Bset)))
    return list(out.values())


tests = gen4()
Phis = np.array(list(product(range(len(D1)), repeat=4)))
samp = np.array([[rng.randrange(N) for _ in range(4)] for _ in range(20000)])
rels, masks = [], []
for R, _, _ in tests:
    gt = np.array([g for g, ok in zip(ALL4, R) if ok])
    vals = sum((3 ** (3 - k)) * B1A[Phis[:, None, k], gt[None, :, k]] for k in range(4))
    ok = R[vals].all(axis=1)
    rel = Phis[ok]
    v = sum((3 ** (3 - k)) * A[samp[:, k]][:, rel[:, k]] for k in range(4))
    fails = (~R[v]).sum(axis=0)
    rels.append(rel[np.argsort(-fails, kind="stable")].astype(np.uint16))
    m = np.zeros(3, dtype=np.uint32)
    for x in range(81):
        if R[x]:
            m[x // 32] |= np.uint32(1 << (x % 32))
    masks.append(m)
print(f"{len(tests)} arity-4 generators; lifted relation sizes {min(map(len, rels))}..{max(map(len, rels))}")

SOURCE = r"""
    uint tid = thread_position_in_grid.x;
    uint nblk = dims[0], m = dims[1];
    if (tid >= blk_off[nblk]) return;
    uint lo = 0, hi = nblk;
    while (hi - lo > 1) { uint mid = (lo + hi) / 2; if (blk_off[mid] <= tid) lo = mid; else hi = mid; }
    uint b = lo;
    uint c = desc[6 * b], t = desc[6 * b + 1];
    if (atomic_load_explicit(&res[6 * c], memory_order_relaxed) != 0u) return;
    uint s0 = desc[6 * b + 2], s1 = desc[6 * b + 3], s2 = desc[6 * b + 4], s3 = desc[6 * b + 5];
    uint n0 = BL[4 * b], n1 = BL[4 * b + 1], n2 = BL[4 * b + 2], n3 = BL[4 * b + 3];
    uint local = tid - blk_off[b];
    uint x3 = local % n3; local /= n3;
    uint x2 = local % n2; local /= n2;
    uint x1 = local % n1; local /= n1;
    uint x0 = local;
    uint i = IDX[s0 + x0], j = IDX[s1 + x1], k = IDX[s2 + x2], l = IDX[s3 + x3];
    for (uint r = rel_off[t]; r < rel_off[t + 1]; ++r) {
        uint v = 27u * T[m * i + rel[4 * r]] + 9u * T[m * j + rel[4 * r + 1]]
               + 3u * T[m * k + rel[4 * r + 2]] + T[m * l + rel[4 * r + 3]];
        if (!((masks[3 * t + v / 32u] >> (v % 32u)) & 1u)) return;
    }
    uint expected = 0u;
    while (true) {
        expected = 0u;
        if (atomic_compare_exchange_weak_explicit(&res[6 * c], &expected, 1u,
                                                  memory_order_relaxed, memory_order_relaxed)) {
            atomic_store_explicit(&res[6 * c + 1], i, memory_order_relaxed);
            atomic_store_explicit(&res[6 * c + 2], j, memory_order_relaxed);
            atomic_store_explicit(&res[6 * c + 3], k, memory_order_relaxed);
            atomic_store_explicit(&res[6 * c + 4], l, memory_order_relaxed);
            atomic_store_explicit(&res[6 * c + 5], t, memory_order_relaxed);
            break;
        }
        if (expected != 0u) break;
    }
"""
kernel = mx.fast.metal_kernel(name="sieber_arity4_diag",
                              input_names=["T", "rel", "rel_off", "masks", "IDX", "BL", "blk_off", "desc", "dims"],
                              output_names=["res"], source=SOURCE, atomic_outputs=True)
Tm = mx.array(A.reshape(-1))
rel_off = np.zeros(len(tests) + 1, dtype=np.uint32)
rel_off[1:] = np.cumsum([len(r) for r in rels])
REL = mx.array(np.concatenate(rels).reshape(-1))
REL_OFF = mx.array(rel_off)
MASKS = mx.array(np.concatenate(masks))


def falsify4(h, max_threads=1 << 31):
    """None or (i, j, k, l, test) for one candidate."""
    buckets = [np.nonzero(h == x)[0].astype(np.uint16) for x in range(3)]
    IDX = np.concatenate(buckets)
    start = np.cumsum([0] + [len(b) for b in buckets])
    blocks = []
    for t, (R, _, _) in enumerate(tests):
        for p, g in enumerate(ALL4):
            if not R[p]:
                ns = [len(buckets[x]) for x in g]
                if all(ns):
                    blocks.append((t, [int(start[x]) for x in g], ns))
    blocks.sort(key=lambda b: int(np.prod(b[2], dtype=np.int64)))
    Ti = mx.array(IDX)
    b0 = 0
    while b0 < len(blocks):
        chunk, total = [], 0
        while b0 < len(blocks) and (total + int(np.prod(blocks[b0][2], dtype=np.int64)) <= max_threads or not chunk):
            total += int(np.prod(blocks[b0][2], dtype=np.int64))
            chunk.append(blocks[b0]); b0 += 1
        offs = np.zeros(len(chunk) + 1, dtype=np.uint64)
        offs[1:] = np.cumsum([int(np.prod(b[2], dtype=np.int64)) for b in chunk])
        assert offs[-1] < 2 ** 32
        desc = np.array([[0, t] + s for t, s, _ in chunk], dtype=np.uint32)
        BL = np.array([ns for _, _, ns in chunk], dtype=np.uint32)
        res, = kernel(inputs=[Tm, REL, REL_OFF, MASKS, Ti, mx.array(BL.reshape(-1)),
                              mx.array(offs.astype(np.uint32)), mx.array(desc.reshape(-1)),
                              mx.array(np.array([len(chunk), len(D1)], dtype=np.uint32))],
                      grid=(int(offs[-1]), 1, 1), threadgroup=(256, 1, 1),
                      output_shapes=[(6,)], output_dtypes=[mx.uint32], init_value=0)
        res = np.array(res)
        if res[0]:
            return tuple(int(x) for x in res[1:])
    return None


def verify(h, w):
    i, j, k, l, t = w
    R, _, _ = tests[t]
    rel = rels[t]
    v = 27 * A[i][rel[:, 0]] + 9 * A[j][rel[:, 1]] + 3 * A[k][rel[:, 2]] + A[l][rel[:, 3]]
    out = 27 * h[i] + 9 * h[j] + 3 * h[k] + h[l]
    return bool(R[v].all()) and not R[out]


classes = json.load(open(os.path.join(HERE, "data", "m2_survivor_classes.json")))


def table(row):
    h = np.zeros(N, dtype=np.uint8)
    LE = ((A[:, None, :] == 0) | (A[:, None, :] == A[None, :, :])).all(axis=2)
    for x in row["minT"]:
        h[LE[x]] = 1
    for x in row["minF"]:
        h[LE[x]] = 2
    return h


n = int(sys.argv[1]) if len(sys.argv) > 1 else 100
pick = classes[:n] + rng.sample(classes, n) + classes[-n:]
killed = 0
t0 = time.perf_counter()
report = []
for q, row in enumerate(pick):
    h = table(row)
    s = time.perf_counter()
    w = falsify4(h)
    if w is not None:
        assert verify(h, w), "unverified arity-4 witness"
        killed += 1
    report.append({"minT": row["minT"], "minF": row["minF"], "witness": w})
    print(f"{q:3d} |min|={len(row['minT']) + len(row['minF'])} killed={w is not None} "
          f"({time.perf_counter() - s:.1f}s)", flush=True)
print(f"arity-4 generators kill {killed}/{len(pick)} sampled survivor classes "
      f"in {time.perf_counter() - t0:.0f}s (all witnesses CPU-verified)")
json.dump(report, open(os.path.join(HERE, "data", "arity4_diagnostic.json"), "w"))
