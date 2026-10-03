#!/usr/bin/env python3
"""Does the 3-cone candidate h3 violate any arity-4 Sieber test?

All 17,240 distinct intersections of S^4_{A,B}, taken up to permutation of the
four coordinates.  For each test R: lift R to D1 (numpy), then ask z3 for a
tuple F_0..F_3 of D2 that is R-related (every related D1-tuple phi gives
(F_0(phi_0), ..., F_3(phi_3)) in R) and whose image under h3 lies outside R.
h3 takes only the values bot and ff, so its output pattern is determined by
membership of each F_i in U = supp(h3).  Every witness is re-verified directly.

h3 preserves all tests of arity <= 3, so any witness here is genuinely 4-ary.
Usage: arity4_h3.py [candidate.npy] [--control]
"""
import json, os, sys, time
from itertools import permutations, product
from multiprocessing import Pool

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

W = 4
T = list(product(range(3), repeat=W))
IDX4 = {t: k for k, t in enumerate(T)}


def all_tests():
    subs = [frozenset(i for i in range(W) if s >> i & 1) for s in range(1 << W)]
    gens = set()
    for A_ in subs:
        for B_ in subs:
            if A_ <= B_:
                m = 0
                for k, g in enumerate(T):
                    if any(g[i] == 0 for i in A_) or len({g[i] for i in B_}) <= 1:
                        m |= 1 << k
                gens.add(m)
    full = (1 << len(T)) - 1
    cl = {full}
    for g in gens:
        cl |= {r & g for r in cl}
    cl.discard(full)
    return cl


def permute(m, pi):
    out = 0
    for k, g in enumerate(T):
        if m >> k & 1:
            out |= 1 << IDX4[tuple(g[pi[i]] for i in range(W))]
    return out


def canonical_tests():
    seen, reps = set(), []
    for m in sorted(all_tests()):
        if m in seen:
            continue
        orbit = {permute(m, pi) for pi in permutations(range(W))}
        seen |= orbit
        reps.append(min(orbit))
    return reps


# worker state
_A = _D1 = _U = None


def init(path):
    global _A, _D1, _U
    import m4
    _A, _D1 = m4.A, np.array(m4.D1, dtype=np.uint8)
    _U = np.load(path) != 0


def solve(mask):
    import z3
    A, D1, U = _A, _D1, _U
    N, M = A.shape
    Rarr = np.array([(mask >> k) & 1 for k in range(len(T))], dtype=bool).reshape((3,) * W)
    # lift to D1: phi-tuples with (phi_i(g_i)) in R for all g in R
    gt = np.argwhere(Rarr)
    Phis = np.array(list(product(range(M), repeat=W)))
    ok = Rarr[tuple(D1[Phis[:, None, i], gt[None, :, i]] for i in range(W))].all(axis=1)
    rel1 = Phis[ok]
    # forbidden output patterns of h3 (values in {bot, ff})
    pats = [p for p in product((0, 2), repeat=W) if not Rarr[p]]
    if not pats:
        return None
    s = z3.SolverFor("QF_FD")
    sel = [[z3.Bool(f"x{i}_{F}") for F in range(N)] for i in range(W)]
    val = [[[z3.Bool(f"v{i}_{a}_{v}") for v in range(3)] for a in range(M)] for i in range(W)]
    for i in range(W):
        s.add(z3.PbEq([(b, 1) for b in sel[i]], 1))
        for a in range(M):
            for v in range(3):
                Fs = np.nonzero(A[:, a] == v)[0]
                s.add(val[i][a][v] == z3.Or([sel[i][F] for F in Fs]))
    forbidden = [g for g in T if not Rarr[g]]
    for phi in rel1:
        for g in forbidden:
            s.add(z3.Or([z3.Not(val[i][phi[i]][g[i]]) for i in range(W)]))
    inU = [z3.Or([sel[i][F] for F in np.nonzero(U)[0]]) for i in range(W)]
    s.add(z3.Or([z3.And([inU[i] if p[i] == 2 else z3.Not(inU[i]) for i in range(W)]) for p in pats]))
    if s.check() != z3.sat:
        return None
    m = s.model()
    tup = [next(F for F in range(N) if z3.is_true(m.eval(sel[i][F], True))) for i in range(W)]
    # independent verification
    vals = A[np.array(tup)[None, :], rel1]                 # (|rel1|, W)
    assert Rarr[tuple(vals.T)].all(), "witness not related"
    out = tuple(2 if U[F] else 0 for F in tup)
    assert not Rarr[out], "witness not violating"
    return mask, tup


if __name__ == "__main__":
    import m4
    path = next((a for a in sys.argv[1:] if a.endswith(".npy")),
                os.path.join(m4.HERE, "data", "candidate_3cone_h.npy"))
    if "--control" in sys.argv:
        rng = np.random.default_rng(0)
        path = os.path.join(m4.HERE, "data", "control_random.npy")
        np.save(path, (rng.integers(0, 2, m4.N) * 2).astype(np.uint8))
    t0 = time.perf_counter()
    reps = canonical_tests()
    print(f"{len(reps)} arity-4 tests up to coordinate permutation ({time.perf_counter() - t0:.0f}s)", flush=True)
    found = []
    with Pool(10, initializer=init, initargs=(path,)) as pool:
        for k, r in enumerate(pool.imap_unordered(solve, reps, chunksize=4)):
            if r is not None:
                found.append(r)
                print(f"  VIOLATION: test {r[0]:#x}, tuple {r[1]}", flush=True)
                if "--control" in sys.argv or "--first" in sys.argv:
                    pool.terminate()
                    break
            if (k + 1) % 100 == 0:
                print(f"  {k + 1}/{len(reps)} tests ({time.perf_counter() - t0:.0f}s), "
                      f"{len(found)} violations", flush=True)
    print(f"done: {len(found)} violating tests out of {len(reps)} ({time.perf_counter() - t0:.0f}s)")
    if "--control" not in sys.argv:
        json.dump([[hex(m), t] for m, t in found],
                  open(os.path.join(m4.HERE, "data", "arity4_h3.json"), "w"))
