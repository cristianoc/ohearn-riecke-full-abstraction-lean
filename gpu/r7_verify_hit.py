"""Independent check of an R7 counterexample (R, pi, x), by direct loops.
Usage: r7_verify_hit.py R_INDEX PI X0 X1 X2   (PI as e.g. 0212)"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, sieber_cpu as C, arity_lib as L
r = int(sys.argv[1]); pi = [int(c) for c in sys.argv[2]]; x = [int(a) for a in sys.argv[3:6]]
R = L.from_mask(L.all_tests(4)[r], 4)
D1 = [tuple(f) for f in C.carrier_D1()]            # f = (f(bot), f(t), f(f))
D1lev, _ = L.level_D1(); E2 = L.level_D2(D1lev).elems
assert len(D1) == 11 and len(E2) == 355
Rg = [v for v in itertools.product(range(3), repeat=4) if R[v]]
T = np.zeros((3,) * 3, bool)
for u in itertools.product(range(3), repeat=3): T[u] = R[tuple(u[pi[i]] for i in range(4))]
Tg = [u for u in itertools.product(range(3), repeat=3) if T[u]]
# R_{D1}: G with (G_i(v_i))_i in R for all v in R
RD1 = [G for G in itertools.product(range(11), repeat=4) if all(R[tuple(D1[G[i]][v[i]] for i in range(4))] for v in Rg)]
TD1 = [y for y in itertools.product(range(11), repeat=3) if all(T[tuple(D1[y[j]][u[j]] for j in range(3))] for u in Tg)]
# check that every element of D2 used is monotone over D1's pointwise order
le = lambda f, g: all(a == 0 or a == b for a, b in zip(D1[f], D1[g]))
for e in x:
    assert all(E2[e, f] == 0 or E2[e, f] == E2[e, g] for f in range(11) for g in range(11) if le(f, g))
lhs = all(R[tuple(int(E2[x[pi[i]], G[i]]) for i in range(4))] for G in RD1)
bad = [y for y in TD1 if not T[tuple(int(E2[x[j], y[j]]) for j in range(3))]]
print(f"|R|={len(Rg)} |R_D1|={len(RD1)} |T|={len(Tg)} |T_D1|={len(TD1)}")
print("x o pi in R_D2:", lhs)
print("x in (pi*R)_D2:", not bad)
if bad:
    y = bad[0]
    print("witness y:", [D1[f] for f in y], "-> x(y) =", [int(E2[x[j], y[j]]) for j in range(3)])
print("x as tables over D1:", [[int(E2[e, f]) for f in range(11)] for e in x])
print("D1 order:", D1)
print("R ground tuples:", Rg)
