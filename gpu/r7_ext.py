"""Check the first-order extension property behind R7.

For a test R (arity w), a map pi: w -> k, y in (pi*R)_{D1}, an elementary
S_{A,B} containing R and u in V^k with u o pi not in S_{A,B}: is there
G in R_{D1} with G_i >= y_{pi i} (i in A, and at p,q where u is defined) and
G_q <= y_{pi q} where u is undefined, for some p,q in B realising the
non-constancy of u on pi(B)?
"""
import sys, time, itertools
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import sieber_cpu as C
import arity_lib as L

w = int(sys.argv[1]); deadline = time.time() + float(sys.argv[2])
D1 = [tuple(f) for f in C.carrier_D1()]
n = len(D1)
E = np.array(D1)                                 # E[f, v]
le = lambda a, b: a == 0 or a == b
LE = np.array([[all(le(f[v], g[v]) for v in range(3)) for g in D1] for f in D1])  # LE[f,g]: f <= g
D1lev, _ = L.level_D1()

def elementary_supersets(R):
    out = []
    subs = [frozenset(i for i in range(w) if s >> i & 1) for s in range(1 << w)]
    for A in subs:
        for B in subs:
            if A <= B and len(B) >= 2:
                S = L.elementary(w, A, B)
                if (R <= S).all():
                    out.append((A, B))
    return out

tests = [L.from_mask(m, w) for m in L.all_tests(w)]
checked = fails = 0
report = []
failing_cases = set(); tests_done = 0
for R in tests:
    RD1 = D1lev.lifted(R)                       # all related w-tuples (indices)
    sups = elementary_supersets(R)
    for k in range(2, w):
        for pi in L.surjections(w, k):
            S = L.pullback(R, pi, k)
            Ys = D1lev.lifted(S)                # y in (pi*R)_{D1}
            for (A, B) in sups:
                piA = {pi[i] for i in A}; piB = sorted({pi[i] for i in B})
                for u in itertools.product(range(3), repeat=k):
                    if any(u[j] == 0 for j in piA):
                        continue
                    pairs = [(j1, j2) for j1 in piB for j2 in piB if j1 < j2 and u[j1] != u[j2]]
                    if not pairs:
                        continue
                    for y in Ys:
                        ok = False
                        for (j1, j2) in pairs:
                            for p in [i for i in B if pi[i] == j1]:
                                for q in [i for i in B if pi[i] == j2]:
                                    m = np.ones(len(RD1), bool)
                                    for i in range(w):
                                        f = y[pi[i]]
                                        if i in A:
                                            m &= LE[f, RD1[:, i]]
                                    for (c, j) in ((p, j1), (q, j2)):
                                        f = y[j]
                                        m &= LE[f, RD1[:, c]] if u[j] != 0 else LE[RD1[:, c], f]
                                    if m.any():
                                        ok = True; break
                                if ok: break
                            if ok: break
                        checked += 1
                        if not ok:
                            failing_cases.add((int(L.all_tests(w).index(0) if False else 0), tuple(pi), R.tobytes()))
                            fails += 1
                            if len(report) < 5:
                                report.append((R.sum(), pi, sorted(A), sorted(B), u, [D1[f] for f in y]))
                if time.time() > deadline:
                    print(f"DEADLINE: tests_done={tests_done}/{len(tests)} checked={checked} fails={fails} failing_cases={len(failing_cases)}"); sys.exit()
    tests_done += 1
print(f"done w={w}: checked={checked} fails={fails} failing_cases={len(failing_cases)}")
for r in report: print(r)
