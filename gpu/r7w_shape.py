"""Shape of the R7' witnesses at the R7 failures of r7_lift_search.py: for each
failure (R, pi, x) and each v outside T = pi*R, is there an arity-3 test
T' containing T with x in T'_{D2} and v not in T'?
Usage: r7w_shape.py SAMPLE SECONDS"""
import sys, os, time
sys.argv = sys.argv[:3]
import r7_lift_search as S
import numpy as np, arity_lib as L
from itertools import permutations
if __name__ == "__main__":
    import multiprocessing as mp
    chunks = [list(range(i, len(S.tests4), 400)) for i in range(400)]
    H = []
    with mp.get_context("fork").Pool(os.cpu_count()) as pool:
        for p, c, h, full in pool.imap_unordered(S.work, chunks): H += h
    xs = np.unique(np.array([x for (_, _, x) in H]), axis=0)
    rel = {tuple(x): [] for x in xs}
    seen = set()
    for m in L.all_tests(3):
        T = L.from_mask(m, 3)
        for perm in permutations(range(3)):
            Tp = np.transpose(T, perm)
            if Tp.tobytes() in seen: continue
            seen.add(Tp.tobytes())
            ok = L.related(S.E2, S.D1lev.lifted(Tp), Tp, xs)
            for x in xs[ok]: rel[tuple(x)].append(Tp)
    pairs = sup_ok = 0; bad = []
    for (r, pi, x) in H:
        T = L.pullback(S.tests4[r], pi, 3)
        for v in zip(*np.nonzero(~T)):
            pairs += 1
            if any(Tp[v] == False and (T <= Tp).all() for Tp in rel[tuple(x)]): sup_ok += 1
            elif len(bad) < 3: bad.append((r, pi, x, v))
    print(f"failures {len(H)}, (failure, v) pairs {pairs}, witnessed by a superset of pi*R: {sup_ok}")
    for b in bad: print("no superset witness:", b)
