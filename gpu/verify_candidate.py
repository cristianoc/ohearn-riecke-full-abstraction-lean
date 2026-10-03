#!/usr/bin/env python3
"""Independent check of the candidates (numpy only): gpu/data/candidate_3cone_h.npy
(ff on up(129) u up(272) u up(321)) and gpu/data/bad_state_h.npy (20 cones).

h : D2 -> B at tau0 = ((B -> B) -> B) -> B.  Checks:
  1. h is monotone;
  2. h preserves every arity-3 test (all 107M related triples of D2);
  3. h is not PCF-definable, by the three-point argument below.

Argument for 3.  If h is definable and not constant, its normal form starts with
case F(ψ), where F |-> ψ_F is definable, hence monotone D2 -> D1.  As case is
strict, m(ψ_m) ≠ ⊥ for every m in supp(h).  If m, m' in supp(h) have a common
upper bound u in D2, then ψ_m, ψ_m' ≤ ψ_u, so ψ_m and ψ_m' are compatible in D1
(no argument where both are defined and differ).  For m0 = 129, m1 = 272,
m2 = 321, with common upper bounds 281 (of 129, 272) and 333 (of 129, 321),
no choice of ψ_m0, ψ_m1, ψ_m2 among the arguments on which each converges is
pairwise compatible on both bounded pairs.
"""
import os, sys
from itertools import product

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sieber_cpu as C
from root_obstruction import lifted_triples
import m4

A, N, LE, D1, BOT = m4.A, m4.N, m4.LE, m4.D1, m4.BOT

def check(h):
    # 1
    assert all(h[i] == BOT or h[i] == h[j] for i in range(N) for j in range(N) if LE[i, j])
    print("1. monotone")

    # 2
    tests = [R for R in C.arity3_tests() if R != (1 << 27) - 1]
    total = 0
    for R, (_, tri) in zip(tests, lifted_triples()):
        Rarr = np.array([(R >> x) & 1 for x in range(27)], dtype=bool).reshape(3, 3, 3)
        assert Rarr[h[tri[:, 0]], h[tri[:, 1]], h[tri[:, 2]]].all()
        total += len(tri)
    print(f"2. preserves all {len(tests)} non-trivial arity-3 tests ({total} related triples)")

    # 3
    m0, m1, m2, u01, u02 = 129, 272, 321, 281, 333
    assert all(h[x] != BOT for x in (m0, m1, m2))
    assert LE[m0, u01] and LE[m1, u01] and LE[m0, u02] and LE[m2, u02]


    def compatible(a, b):
        return all(x == BOT or y == BOT or x == y for x, y in zip(D1[a], D1[b]))


    allowed = {m: [a for a in range(len(D1)) if A[m, a] != BOT] for m in (m0, m1, m2)}
    choices = [(a, b, c) for a, b, c in product(allowed[m0], allowed[m1], allowed[m2])
               if compatible(a, b) and compatible(a, c)]
    assert not choices
    print("3. not definable: no ψ_129, ψ_272, ψ_321 in their allowed sets are compatible "
          "along the upper bounds 281 and 333")


for name in ("candidate_3cone_h.npy", "bad_state_h.npy"):
    print(name)
    check(np.load(os.path.join(m4.HERE, "data", name)))
