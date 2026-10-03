"""Does repeating columns keep adding constraints?  For y in D2^k (distinct
entries) let C_w(y) = intersection of pi*R over tests R of arity w and maps
pi: w -> k with y o pi in R_{D2} (a set of k-tuples over V).  C_w shrinks with
w; report how often C_{w+1}(y) is strictly smaller than C_w(y).
Usage: mult_bound.py K WMAX SAMPLE SECONDS [SEED]"""
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, arity_lib as L
from itertools import product
k, wmax, sample, budget = map(int, sys.argv[1:5]); seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
random.seed(seed); t0 = time.time()
D1lev, _ = L.level_D1(); E2 = L.level_D2(D1lev).elems; n = len(E2)
Y = np.array([random.sample(range(n), k) for _ in range(sample)])
gk = list(product(range(3), repeat=k))

def work(args):
    w, rs = args
    pis = L.surjections(w, k)
    pw = 3 ** np.arange(w - 1, -1, -1)
    pidx = {pi: np.array([sum(x[pi[i]] * pw[i] for i in range(w)) for x in gk]) for pi in pis}
    C = np.ones((sample, 3 ** k), bool); done = 0
    for m in rs:
        R = L.from_mask(m, w); RD1 = D1lev.lifted(R)
        X = np.concatenate([Y[:, list(pi)] for pi in pis])
        ok = L.related(E2, RD1, R, X).reshape(len(pis), sample)
        Rf = R.ravel()
        for a, pi in enumerate(pis):
            if ok[a].any(): C[ok[a]] &= Rf[pidx[pi]][None, :]
        D1lev._cache.clear(); done += 1
        if time.time() - t0 > budget: break
    return w, C, done, len(rs)

if __name__ == "__main__":
    import multiprocessing as mp
    jobs = []
    for w in range(k, wmax + 1):
        if w == 4:
            import arity4_h3; ms = sorted(arity4_h3.canonical_tests())   # one test per permutation class suffices: pi ranges over all maps
        else:
            ms = L.all_tests(w)
        P = os.cpu_count()
        jobs += [(w, ms[i::P]) for i in range(P)]
    Cw = {w: np.ones((sample, 3 ** k), bool) for w in range(k, wmax + 1)}
    stat = {w: [0, 0] for w in Cw}
    with mp.get_context("fork").Pool(os.cpu_count()) as pool:
        for w, C, d, tot in pool.imap_unordered(work, jobs):
            Cw[w] &= C; stat[w][0] += d; stat[w][1] += tot
    for w in range(k + 1, wmax + 1): Cw[w] &= Cw[w - 1]
    for w in Cw: print(f"w={w}: tests done {stat[w][0]}/{stat[w][1]}, mean |C_w| = {Cw[w].sum(1).mean():.3f}")
    for w in range(k + 1, wmax + 1):
        s = (Cw[w] != Cw[w - 1]).any(1)
        print(f"C_{w} strictly smaller than C_{w-1} for {s.sum()}/{sample} sampled y")
    print(f"elapsed {time.time()-t0:.1f}s")
