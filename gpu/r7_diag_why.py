"""For M4-failing arity-4 instances, find the single diagonal tuples (g,...,g)
that alone exclude the output pattern u, and record whether g is a component of y.
Usage: r7_diag_why.py SECONDS"""
import sys, os, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, arity_lib as L
import r7_diag as T

budget = float(sys.argv[1]); t0 = time.time(); import random; random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
tests = [L.from_mask(m, T.w) for m in L.all_tests(T.w)]; random.shuffle(tests)
kinds = collections.Counter(); samples = []
for R in tests:
    RD1 = T.D1lev.lifted(R)
    for k in (3, 2):
        for pi in L.surjections(T.w, k):
            Ys = T.D1lev.lifted(L.pullback(R, pi, k))
            for y, u in T.m4_failures(R, pi, k, RD1, Ys):
                single = [g for g in range(len(T.D1))
                          if not T.realisable(R, pi, k, np.array([[g] * T.w]), y, u)]
                comp = [g for g in single if g in y]
                kind = "single g in y" if comp else ("single g not in y" if single else "needs several g")
                kinds[kind] += 1
                if len(samples) < 6 and (kind != "single g in y" or len(samples) < 2):
                    samples.append((kind, int(R.sum()), pi, [T.D1[f] for f in y], u, [T.D1[g] for g in single]))
                if time.time() - t0 > budget: break
            if time.time() - t0 > budget: break
        if time.time() - t0 > budget: break
    if time.time() - t0 > budget: break
print(dict(kinds), f"elapsed={time.time()-t0:.1f}s")
for s in samples: print(s)
