#!/usr/bin/env python3
"""Finite search scaffolding for a concrete Sieber counterexample.

Exact for the ordinary Boolean Sieber model at the types currently implemented.
It canonicalises a test by its ground relation (so all finite intersections are
covered, not merely elementary generators).

Current exact results (tests through arity 3):
  B -> B:                  11 elements
  (B -> B) -> B:
      monotone candidates 397
      after arity <= 2     397
      after arity <= 3     355

The next target is an order-4 type.  Do not enumerate 3^355 tables: encode
monotonicity + preservation as SAT/SMT constraints.
"""
from itertools import product

BOT, TT, FF = 0, 1, 2
VALS = range(3)

def flat_le(a, b):
    return a == BOT or a == b

def elementary(w, A, B, tup):
    return any(tup[i] == BOT for i in A) or all(tup[i] == tup[j] for i in B for j in B)

def tests(w):
    """All distinct finite intersections of elementary relations at arity w."""
    tuples = list(product(VALS, repeat=w))
    subs = [{i for i in range(w) if mask >> i & 1} for mask in range(1 << w)]
    gens = []
    for A in subs:
        for B in subs:
            if A <= B:
                r = tuple(elementary(w, A, B, t) for t in tuples)
                if r not in gens:
                    gens.append(r)
    closure = {tuple(True for _ in tuples)}
    for g in gens:
        closure |= {tuple(a and b for a, b in zip(r, g)) for r in list(closure)}
    return tuples, list(closure)

def monotone_B_B():
    return [f for f in product(VALS, repeat=3)
            if all(not flat_le(a,b) or flat_le(f[a],f[b]) for a in VALS for b in VALS)]

B1 = monotone_B_B()

def pointwise_le(f, g):
    return all(flat_le(a,b) for a,b in zip(f,g))

def monotone_B1_B():
    les = [(i,j) for i,f in enumerate(B1) for j,g in enumerate(B1) if pointwise_le(f,g)]
    return [h for h in product(VALS, repeat=len(B1))
            if all(flat_le(h[i],h[j]) for i,j in les)]

def related_B1_tuple(F, ground, R, index):
    for n,t in enumerate(ground):
        if R[n]:
            out = tuple(B1[F[k]][t[k]] for k in range(len(F)))
            if not R[index[out]]:
                return False
    return True

def filter_B2(candidates, max_arity=3):
    cur = candidates
    for w in range(1, max_arity+1):
        ground, rs = tests(w)
        index = {t:i for i,t in enumerate(ground)}
        for R in rs:
            related = [F for F in product(range(len(B1)), repeat=w)
                       if related_B1_tuple(F, ground, R, index)]
            cur = [h for h in cur
                   if all(R[index[tuple(h[i] for i in F)]] for F in related)]
        print(f"arity {w}: {len(rs)} distinct tests; {len(cur)} elements remain")
    return cur

if __name__ == "__main__":
    print("B->B:", len(B1))
    B2mono = monotone_B1_B()
    print("(B->B)->B monotone:", len(B2mono))
    B2 = filter_B2(B2mono, 3)
    print("(B->B)->B ordinary-Sieber through arity 3:", len(B2))\n    defs = definable_B2()\n    print("(B->B)->B definable:", len(defs))\n    assert len(defs) == len(B2) == 355
    print()
    print("NEXT: formulate the first order-4 carrier as SAT/SMT.")
    print("Use one 3-valued variable per input element; impose monotonicity and")
    print("ordinary-relation preservation lazily. Search simultaneously for a")
    print("finite Kripke/world-extension witness rejecting the candidate.")


# ---------------------------------------------------------------------------
# Exact definability check for (B -> B) -> B
# ---------------------------------------------------------------------------

def definable_B2():
    """All denotations of closed terms (B->B)->B, represented as tables on B1.

    A beta-normal closed term is lambda f. M with f:B->B and M:B.  Semantically
    the ground tables M(f) form the least set containing bottom/tt/ff and closed
    under:
      * strict conditional, pointwise; and
      * application of f: g |-> (f |-> f(g(f))).

    Tables are represented by two bitmasks: positions returning tt and ff.
    The remaining positions return bottom.  This is exact, not a depth-bounded
    term enumeration.
    """
    n = len(B1)
    full = (1 << n) - 1
    S = {(0, 0), (full, 0), (0, full)}

    def fapp(g):
        ones = twos = 0
        for i, fi in enumerate(B1):
            v = 1 if (g[0] >> i) & 1 else 2 if (g[1] >> i) & 1 else 0
            out = fi[v]
            if out == 1:
                ones |= 1 << i
            elif out == 2:
                twos |= 1 << i
        return ones, twos

    while True:
        old = list(S)
        T = set(S)
        T.update(fapp(g) for g in old)
        for c1, c2 in old:
            for a1, a2 in old:
                for b1, b2 in old:
                    T.add(((c1 & a1) | (c2 & b1),
                           (c1 & a2) | (c2 & b2)))
        if T == S:
            return S
        print("definable closure:", len(S), "->", len(T))
        S = T
