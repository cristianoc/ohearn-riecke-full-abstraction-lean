"""Two-world Kripke relations at tau0, for m4.py.

Worlds w (arity 2) and w+ (arity 3), morphisms: identities and a set P of maps
p : w+ -> w.  Ground relations R(w) (an arity-2 test) and R(w+) (an arity-3
test) with g in R(w) => g o p in R(w+).  Lifting (Kripke, as in O'Hearn--Riecke):

  X in R_{s->t}(v) iff for every morphism u : v' -> v and Y in R_s(v'),
                       (X_{u j}(Y_j))_j in R_t(v').

Only identities map into w+, so relations at w+ are the ordinary lifts.  A
candidate h : D2 -> B is rejected when some G in R_D2(w) has (h G_0, h G_1)
outside R(w); definable h are never rejected (fundamental lemma).

relations() yields (description, R(w) as a 3x3 bool array, R_D2(w) as an
N x N bool array).  Every D2 element is definable, so each yielded R_D2(w)
contains the diagonal; this is asserted as a soundness check.
"""
import itertools

import numpy as np

import sieber_cpu as C

D1 = C.carrier_D1()
D2 = sorted(C.definable_D2(D1))
A = np.array(D2, dtype=np.uint8)
N = len(D2)
B1A = np.array(D1, dtype=np.uint8)
NB1 = len(D1)


def ground3(R):
    return np.array([[[C.ground_member(R, (x, y, z)) for z in range(3)] for y in range(3)]
                     for x in range(3)])


def tests2():
    """Distinct arity-2 tests, as 3x3 arrays (S^3 tests constant in the last coordinate)."""
    out = {}
    for R in C.arity3_tests():
        g = ground3(R)
        if (g == g[:, :, :1]).all():
            r2 = g[:, :, 0]
            if not r2.all():
                out.setdefault(r2.tobytes(), r2)
    return list(out.values())


def lift_D1_ordinary(R3):
    gt = np.argwhere(R3)
    Phis = np.array(list(itertools.product(range(NB1), repeat=3)))
    ok = R3[B1A[Phis[:, None, 0], gt[None, :, 0]], B1A[Phis[:, None, 1], gt[None, :, 1]],
            B1A[Phis[:, None, 2], gt[None, :, 2]]].all(axis=1)
    return [tuple(x) for x in Phis[ok]]


def lift_D1_at_w(Rw, Rwp, P):
    gw, gwp = np.argwhere(Rw), np.argwhere(Rwp)
    out = []
    for Phi in itertools.product(range(NB1), repeat=2):
        if not all(Rw[B1A[Phi[0], g[0]], B1A[Phi[1], g[1]]] for g in gw):
            continue
        if all(Rwp[tuple(B1A[Phi[p[k]], g[k]] for k in range(3))] for p in P for g in gwp):
            out.append(Phi)
    return out


def lift_D2_at_w(Rw, Rwp, P, D1w, D1wp):
    rel = np.ones((N, N), dtype=bool)
    for f, g in D1w:
        rel &= Rw[A[:, f][:, None], A[:, g][None, :]]
    for p in P:
        for Phi in D1wp:
            idx = [A[:, Phi[k]][:, None] if p[k] == 0 else A[:, Phi[k]][None, :] for k in range(3)]
            rel &= Rwp[tuple(np.broadcast_arrays(*idx))]
    return rel


def relations():
    T2 = tests2()
    T3 = [ground3(R) for R in C.arity3_tests() if R != (1 << 27) - 1]
    maps = list(itertools.product(range(2), repeat=3))
    map_sets = [[(0, 0, 0)], [(0, 0, 1)], [p for p in maps if len(set(p)) == 2]]
    lift_cache = {}
    for i, Rw in enumerate(T2):
        gw = np.argwhere(Rw)
        for j, Rwp in enumerate(T3):
            for P in map_sets:
                if not all(Rwp[tuple(g[p[k]] for k in range(3))] for p in P for g in gw):
                    continue
                if j not in lift_cache:
                    lift_cache[j] = lift_D1_ordinary(Rwp)
                D1w = lift_D1_at_w(Rw, Rwp, P)
                rel = lift_D2_at_w(Rw, Rwp, P, D1w, lift_cache[j])
                assert rel.diagonal().all(), "a definable element of D2 fell outside R_D2(w)"
                yield (f"R(w)=arity-2 test {i}, R(w+)=arity-3 test {j}, P={P}", Rw, rel)
