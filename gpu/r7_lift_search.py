"""Search for an R7 counterexample from failures of the diagonal criterion.

Step 1: sample x in D2^3; for each arity-3 test T, keep x that are related on
every diagonal tuple (g,g,g) but not in T_{D2} ("diagonal failures").
Step 2: for every arity-4 test R and single merge pi: 4 -> 3 with pi*R = T,
check x o pi in R_{D2}.  A hit is an R7 counterexample (x o pi in R_{D2},
x not in (pi*R)_{D2}).
Usage: r7_lift_search.py SAMPLE SECONDS [SEED]"""
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, arity_lib as L
sample, budget = int(sys.argv[1]), float(sys.argv[2])
random.seed(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
t0 = time.time()
D1lev, _ = L.level_D1(); D2lev = L.level_D2(D1lev); E2 = D2lev.elems; n = len(E2)
diag3 = np.array([[g] * 3 for g in range(E2.shape[1])])
X = np.array([[random.randrange(n) for _ in range(3)] for _ in range(sample)])
fails = {}                                   # T bytes -> (T, xs)
for m in L.all_tests(3):
    T = L.from_mask(m, 3)
    bad = L.related(E2, diag3, T, X) & ~L.related(E2, D1lev.lifted(T), T, X)
    if bad.any(): fails[T.tobytes()] = (T, np.unique(X[bad], axis=0))
print(f"step1: {sum(len(v[1]) for v in fails.values())} diagonal failures over {len(fails)} tests ({time.time()-t0:.1f}s)", flush=True)
tests4 = [L.from_mask(m, 4) for m in L.all_tests(4)]
pis = L.surjections(4, 3)
from itertools import product
pw4 = np.array([27, 9, 3, 1])
pidx = {pi: np.array([sum(x[pi[i]] * pw4[i] for i in range(4)) for x in product(range(3), repeat=3)]) for pi in pis}
print(f"arity-4 tests: {len(tests4)}, merges: {len(pis)} ({time.time()-t0:.1f}s)", flush=True)
def work(chunk):
    pairs = checked = 0; hits = []
    for r in chunk:
        R = tests4[r]
        for pi in pis:
            key = R.ravel()[pidx[pi]].reshape(3, 3, 3).tobytes()
            if key not in fails: continue
            T, xs = fails[key]; pairs += 1
            ok = L.related(E2, D1lev.lifted(R), R, xs[:, list(pi)])
            checked += len(xs)
            for x in xs[ok]: hits.append((r, pi, x.tolist()))
        D1lev._cache.clear()
        if time.time() - t0 > budget: return pairs, checked, hits, False
    return pairs, checked, hits, True

if __name__ == "__main__":
    import multiprocessing as mp
    ctx = mp.get_context("fork")
    chunks = [list(range(i, len(tests4), 400)) for i in range(400)]
    P = C = 0; H = []; complete = True
    with ctx.Pool(os.cpu_count()) as pool:
        for p, c, h, full in pool.imap_unordered(work, chunks):
            P += p; C += c; H += h; complete &= full
    for (r, pi, x) in H[:5]:
        print("R7 COUNTEREXAMPLE: R index", r, "|R| =", int(tests4[r].sum()), "pi =", pi, "x =", x)
    print(f"cores {os.cpu_count()}; complete={complete}; pairs (R,pi) with pi*R a failing T: {P}; x o pi checked: {C}; hits: {len(H)}; elapsed {time.time()-t0:.1f}s")
