"""For arity-4 instances where the monotone condition M4 fails, test which
related argument tuples exclude the violating output pattern u.

For each failing (R, pi, y, u): is there x in D2^k with x_j(y_j) = u_j for all j
and (x_{pi i}(G_i))_i in R for every G in a family of related tuples?
  level 'diag': G ranges over the diagonal tuples (g,...,g), g in D1;
  level 'full': G ranges over all of R_{D1}.
If no x exists at level 'diag', the diagonal tuples alone exclude u.
Usage: r7_diag.py SECONDS
"""
import sys, os, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import sieber_cpu as C
import arity_lib as L

w = 4
D1lev, _ = L.level_D1()
D1 = [tuple(f) for f in C.carrier_D1()]
D2 = L.level_D2(D1lev).elems.astype(np.int64)        # D2[x, f]
n = len(D2)
LE = np.array([[all(a == 0 or a == b for a, b in zip(f, g)) for g in D1] for f in D1])
diagG = np.array([[g] * w for g in range(len(D1))])

def m4_failures(R, pi, k, RD1, Ys):
    """Yield (y, u) where M4 fails for some elementary S containing R."""
    subs = [frozenset(i for i in range(w) if s >> i & 1) for s in range(1 << w)]
    sups = [(A, B) for A in subs for B in subs if A <= B and len(B) >= 2 and (R <= L.elementary(w, A, B)).all()]
    seen = set()
    for (A, B) in sups:
        piA = {pi[i] for i in A}; piB = sorted({pi[i] for i in B})
        for u in itertools.product(range(3), repeat=k):
            if any(u[j] == 0 for j in piA): continue
            pairs = [(j1, j2) for j1 in piB for j2 in piB if j1 < j2 and u[j1] != u[j2]]
            if not pairs: continue
            for y in Ys:
                ok = False
                for (j1, j2) in pairs:
                    for p in [i for i in B if pi[i] == j1]:
                        for q in [i for i in B if pi[i] == j2]:
                            m = np.ones(len(RD1), bool)
                            for i in A: m &= LE[y[pi[i]], RD1[:, i]]
                            for (c, j) in ((p, j1), (q, j2)):
                                m &= LE[y[j], RD1[:, c]] if u[j] != 0 else LE[RD1[:, c], y[j]]
                            if m.any(): ok = True; break
                        if ok: break
                    if ok: break
                if not ok and (tuple(y), u) not in seen:
                    seen.add((tuple(y), u)); yield tuple(y), u

def realisable(R, pi, k, Gs, y, u):
    """Is there x in D2^k with x_j(y_j)=u_j and (x_{pi i}(G_i))_i in R for all G in Gs?"""
    Rflat = R.ravel(); pw = [27, 9, 3, 1]
    cand = [np.nonzero(D2[:, y[j]] == u[j])[0] for j in range(k)]
    if any(len(c) == 0 for c in cand): return False
    blocks = [[i for i in range(w) if pi[i] == j] for j in range(k)]
    contrib = []
    for j in range(k):
        c = np.zeros((len(cand[j]), len(Gs)), dtype=np.int64)
        for i in blocks[j]: c += D2[cand[j]][:, Gs[:, i]] * pw[i]
        contrib.append(c)
    # join blocks 0..k-2 by enumeration, last block vectorised
    for pre in itertools.product(*[range(len(cand[j])) for j in range(k - 1)]):
        base = sum(contrib[j][pre[j]] for j in range(k - 1))
        if Rflat[base[None, :] + contrib[k - 1]].all(axis=1).any(): return True
    return False

def main(budget):
    t0 = time.time()
    tests = [L.from_mask(m, w) for m in L.all_tests(w)]
    stats = {"instances": 0, "diag_excludes": 0, "diag_misses": 0, "full_excludes": 0, "full_misses": 0}
    examples = []
    done_tests = 0
    for R in tests:
        RD1 = D1lev.lifted(R)
        for k in (3, 2):
            for pi in L.surjections(w, k):
                Ys = D1lev.lifted(L.pullback(R, pi, k))
                for y, u in m4_failures(R, pi, k, RD1, Ys):
                    stats["instances"] += 1
                    if not realisable(R, pi, k, diagG, y, u):
                        stats["diag_excludes"] += 1; continue
                    stats["diag_misses"] += 1
                    if realisable(R, pi, k, RD1, y, u):
                        stats["full_misses"] += 1
                        examples.append(("R7 COUNTEREXAMPLE", int(R.sum()), pi, [D1[f] for f in y], u))
                    else:
                        stats["full_excludes"] += 1
                        if len(examples) < 4:
                            examples.append(("needs non-diagonal G", int(R.sum()), pi, [D1[f] for f in y], u))
                    if time.time() - t0 > budget: break
                if time.time() - t0 > budget: break
            if time.time() - t0 > budget: break
        if time.time() - t0 > budget: break
        done_tests += 1
    print(f"tests_done={done_tests}/{len(tests)} elapsed={time.time()-t0:.1f}s", stats)
    for e in examples: print(e)


if __name__ == "__main__":
    main(float(sys.argv[1]))
