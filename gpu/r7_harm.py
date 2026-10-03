"""Are the R7 failures harmless for the arity bound?  For each failure
(R, pi, x) found by r7_lift_search.py (x o pi in R_{D2}, x not in (pi*R)_{D2}),
compute C_3(x) = intersection of the arity-3 tests T' (in all coordinate
orders) with x in T'_{D2}, and ask whether C_3(x) is inside T = pi*R.
If it is, every output pattern T excludes is already excluded at arity 3.
Usage: r7_harm.py SAMPLE SECONDS"""
import sys, os, time
sys.argv = [sys.argv[0], sys.argv[1], sys.argv[2]]
import r7_lift_search as S
import numpy as np, arity_lib as L
from itertools import permutations
if __name__ == "__main__":
    import multiprocessing as mp
    chunks = [list(range(i, len(S.tests4), 400)) for i in range(400)]
    H = []
    with mp.get_context("fork").Pool(os.cpu_count()) as pool:
        for p, c, h, full in pool.imap_unordered(S.work, chunks): H += h
    print(f"failures: {len(H)} ({time.time()-S.t0:.1f}s)", flush=True)
    xs = np.unique(np.array([x for (_, _, x) in H]), axis=0)
    C3 = {tuple(x): np.ones(27, bool) for x in xs}
    for m in L.all_tests(3):
        T = L.from_mask(m, 3); TD1 = S.D1lev.lifted(T)
        for perm in permutations(range(3)):
            Tp = np.transpose(T, perm)          # Tp[u] = T[u o perm^-1]; covers all orders
            TpD1 = S.D1lev.lifted(Tp)
            ok = L.related(S.E2, TpD1, Tp, xs)
            for x in xs[ok]: C3[tuple(x)] &= Tp.ravel()
    harmful = []
    for (r, pi, x) in H:
        T = L.pullback(S.tests4[r], pi, 3).ravel()
        if (C3[tuple(x)] & ~T).any(): harmful.append((r, pi, x))
    print(f"distinct x: {len(xs)}; failures where C_3(x) is not inside pi*R: {len(harmful)}")
    for h in harmful[:3]: print("HARMFUL:", h)
    print(f"elapsed {time.time()-S.t0:.1f}s")
