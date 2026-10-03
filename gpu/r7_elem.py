"""R7'' check: if x o pi in R_{D2} then x in (pi*S)_{D2} for every elementary
S = S^w_{A,B} containing R.  pi = identity when W == K.
Usage: r7_elem.py W K SAMPLE SECONDS [SEED]"""
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, arity_lib as L
w, k, sample, budget = map(int, sys.argv[1:5]); seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
random.seed(seed); t0 = time.time()
D1lev, _ = L.level_D1(); E2 = L.level_D2(D1lev).elems; n = len(E2)
X = np.array([[random.randrange(n) for _ in range(k)] for _ in range(sample)])
subs = [frozenset(i for i in range(w) if s >> i & 1) for s in range(1 << w)]
pis = L.surjections(w, k) if w > k else [tuple(range(w))]
if w == 4:
    import arity4_h3; masks = sorted(arity4_h3.canonical_tests())
else:
    masks = L.all_tests(w)
elemcache = {}
def lift_ok(T, Xs):
    key = T.tobytes()
    if key not in elemcache: elemcache[key] = D1lev.lifted(T)
    return L.related(E2, elemcache[key], T, Xs)
checked = bad = done = 0
for m in masks:
    R = L.from_mask(m, w); RD1 = D1lev.lifted(R)
    sups = [(A, B) for A in subs for B in subs if A <= B and len(B) >= 2 and (R <= L.elementary(w, A, B)).all()]
    for pi in pis:
        ok = L.related(E2, RD1, R, X[:, list(pi)])
        if not ok.any(): continue
        Xs = X[ok]
        for (A, B) in sups:
            S = L.pullback(L.elementary(w, A, B), pi, k)
            good = lift_ok(S, Xs)
            checked += len(Xs); bad += int((~good).sum())
            if (~good).any():
                print("R7'' FAILS: |R|", int(R.sum()), "pi", pi, "S", sorted(A), sorted(B), "x", Xs[~good][0].tolist()); break
    D1lev._cache.clear(); done += 1
    if bad or time.time() - t0 > budget: break
print(f"w={w} k={k}: tests {done}/{len(masks)}, (x, S) pairs checked {checked}, failures {bad}, {time.time()-t0:.1f}s")
