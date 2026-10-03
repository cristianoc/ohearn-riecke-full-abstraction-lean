"""Lemma C check: for a test T of arity k and x in D2^k,
   (forall g in D1: (x_j(g))_j in T)  ==>  x in T_{D2}?
Compares the diagonal-tested set with the lifted relation T_{D2}.
Usage: r7_lemmaC.py K SECONDS [sample]"""
import sys, os, time, itertools, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, arity_lib as L
k = int(sys.argv[1]); budget = float(sys.argv[2]); sample = int(sys.argv[3]) if len(sys.argv) > 3 else 0
t0 = time.time(); random.seed(1)
D1lev, _ = L.level_D1(); D2lev = L.level_D2(D1lev); D2 = D2lev.elems.astype(np.int64); n = len(D2)
diag = np.array([[g] * k for g in range(D2.shape[1])])
X = L.all_tuples(n, k) if not sample else np.array([[random.randrange(n) for _ in range(k)] for _ in range(sample)])
tests = [L.from_mask(m, k) for m in L.all_tests(k)]
viol = 0; total = 0
for T in tests:
    # diagonal-tested: rows of diag as argument tuples
    A = L.related(D2lev.elems, diag, T, X)
    B = L.related(D2lev.elems, D1lev.lifted(T), T, X)
    bad = A & ~B
    total += int(A.sum()); viol += int(bad.sum())
    if bad.any():
        i = np.argmax(bad); print("LEMMA C FAILS: |T|", int(T.sum()), "x =", X[i].tolist()); break
    if time.time() - t0 > budget: print("deadline"); break
print(f"k={k} tests={len(tests)} diag-related tuples checked={total} failures={viol} elapsed={time.time()-t0:.1f}s")
