"""CPU reference for the ordinary Boolean Sieber model (GPU_SEARCH.md, sections 2-3).

Values: BOT=0, TT=1, FF=2, flat order.  An arity-3 test is a set of ground
triples, stored as a 27-bit mask indexed by 9*a + 3*b + c.

The functions in the "oracle" section are deliberately direct transcriptions of
the definitions; they are slow and only used to check faster code.
"""
from itertools import product

import numpy as np

BOT, TT, FF = 0, 1, 2
V = (BOT, TT, FF)


def flat_le(a, b):
    return a == BOT or a == b


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

def elementary_mask(A, B):
    """S^3_{A,B} = {g | (exists i in A. g_i = BOT) or g constant on B}."""
    m = 0
    for g in product(V, repeat=3):
        if any(g[i] == BOT for i in A) or len({g[i] for i in B}) <= 1:
            m |= 1 << (9 * g[0] + 3 * g[1] + g[2])
    return m


def arity3_tests():
    """All distinct finite intersections of S^3_{A,B} (A subset B), including the
    full relation, as sorted 27-bit masks.  They include every arity-1 and
    arity-2 test, since S^2_{A,B} x V = S^3_{A,B}."""
    subsets = [frozenset(i for i in range(3) if s >> i & 1) for s in range(8)]
    gens = {elementary_mask(A, B) for A in subsets for B in subsets if A <= B}
    closure = {(1 << 27) - 1}
    for g in gens:
        closure |= {r & g for r in closure}
    return sorted(closure)


def ground_member(R, values):
    a, b, c = values
    return bool(R >> (9 * a + 3 * b + c) & 1)


# ---------------------------------------------------------------------------
# Carriers
# ---------------------------------------------------------------------------

def carrier_D1():
    """Monotone maps B -> B as value tables (f(BOT), f(TT), f(FF)): 11 of them.
    All preserve every test (first-order sequential), so this is D_(B->B)."""
    return [f for f in product(V, repeat=3)
            if all(not flat_le(x, y) or flat_le(f[x], f[y]) for x in V for y in V)]


def lift_ground_to_D1(R, D1):
    """rel1: triples (a,b,c) of D1 indices with (f_a x, f_b y, f_c z) in R for all
    (x,y,z) in R."""
    ground = [g for g in product(V, repeat=3) if ground_member(R, g)]
    return [(a, b, c) for a, b, c in product(range(len(D1)), repeat=3)
            if all(ground_member(R, (D1[a][x], D1[b][y], D1[c][z])) for x, y, z in ground)]


def monotone_over(carrier):
    """All monotone maps carrier -> B, as tuples (pointwise order on carrier)."""
    n = len(carrier)
    les = [(i, j) for i in range(n) for j in range(n)
           if i != j and all(flat_le(x, y) for x, y in zip(carrier[i], carrier[j]))]
    out = []
    for h in product(V, repeat=n):
        if all(flat_le(h[i], h[j]) for i, j in les):
            out.append(h)
    return out


def definable_D2(D1):
    """All denotations of closed terms of type (B->B)->B, as tables on D1.

    lambda f. M with M : B built from BOT/TT/FF, the strict conditional and
    application of f.  Semantically: the least set of tables containing the
    constants and closed under pointwise conditional and g |-> (f |-> f(g(f))).
    """
    n = len(D1)
    D1a = np.array(D1, dtype=np.int8)
    S = {tuple([v] * n) for v in V}
    while True:
        arr = np.array(sorted(S), dtype=np.int8)                  # (s, n)
        new = set(S)
        # application of f to g: position i gives D1[i][g[i]]
        app = D1a[np.arange(n)[None, :], arr]                     # (s, n)
        new |= {tuple(r) for r in app.tolist()}
        # strict conditional if(c, a, b), vectorised over (a, b) for each c
        for c in arr:
            res = np.where(c[None, None, :] == BOT, BOT,
                           np.where(c[None, None, :] == TT, arr[:, None, :], arr[None, :, :]))
            new |= {tuple(r) for r in res.reshape(-1, n).tolist()}
        if new == S:
            return S
        S = new


# ---------------------------------------------------------------------------
# Oracle (slow, direct)
# ---------------------------------------------------------------------------

def related_D1_tuple(R, D1, indices):
    ground = [g for g in product(V, repeat=3) if ground_member(R, g)]
    a, b, c = indices
    return all(ground_member(R, (D1[a][x], D1[b][y], D1[c][z])) for x, y, z in ground)


def related_D2_tuple(R, D1, D2, indices):
    """(F_i, F_j, F_k) related at (B->B)->B: for every related triple of D1."""
    i, j, k = indices
    for a, b, c in product(range(len(D1)), repeat=3):
        if related_D1_tuple(R, D1, (a, b, c)):
            if not ground_member(R, (D2[i][a], D2[j][b], D2[k][c])):
                return False
    return True


def related_level_tuple(R, T, rel, indices):
    """Generic: related at a level whose elements are tables T over the previous
    carrier, given the previous level's lifted relation `rel` (index triples)."""
    i, j, k = indices
    return all(ground_member(R, (T[i][a], T[j][b], T[k][c])) for a, b, c in rel)


def candidate_witnesses(R, T, rel, h, I=None, J=None, K=None):
    """All triples (i,j,k) in I x J x K that are related but whose image under h
    is not in R.  Exhaustive, for restricted grids."""
    n = len(T)
    I = range(n) if I is None else I
    J = range(n) if J is None else J
    K = range(n) if K is None else K
    return [(i, j, k) for i in I for j in J for k in K
            if not ground_member(R, (h[i], h[j], h[k]))
            and related_level_tuple(R, T, rel, (i, j, k))]


def candidate_preserves(R, T, rel, h):
    return not candidate_witnesses(R, T, rel, h)
