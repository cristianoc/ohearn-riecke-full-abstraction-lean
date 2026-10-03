#!/usr/bin/env python3
"""A finite certificate that a table h : D2 -> B is not PCF-definable.

If h is definable and not constant, a normal form for it is
    λF. case F(ψ) of tt -> M1, ff -> M2      (or F(ψ) itself)
with ψ = λz.M a term of type B -> B that may use F.  Since case is strict,
    F(ψ_F) ≠ ⊥ for every F in supp(h).
The map F |-> ψ_F is the denotation of λF.ψ, a definable element of type
((B -> B) -> B) -> (B -> B): it is monotone and preserves every Sieber relation,
in particular every arity-3 test (lifted to D2 on the input side, to D1 on the
output side).  By monotonicity it suffices to impose the condition at the
minimal elements of supp(h).

So: if NO monotone ψ : D2 -> D1 preserving all arity-3 tests has m(ψ(m)) ≠ ⊥ at
every minimal m of supp(h), then h is not definable.  The solver decides this;
arity-3 constraints are added lazily (UNSAT of a relaxation is UNSAT).

Usage: root_obstruction.py [h.npy]   (default: gpu/data/bad_state_h.npy)
"""
import os, sys, time

import numpy as np
import z3

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sieber_cpu as C
import m4

A, N, LE, BOT = m4.A, m4.N, m4.LE, m4.BOT
D1 = m4.D1
M = len(D1)
LE1 = np.array([[all(C.flat_le(x, y) for x, y in zip(D1[i], D1[j])) for j in range(M)] for i in range(M)])


def lifted_triples():
    """For each arity-3 test R (not full): R as a 27-bit mask, rel1 (D1 triples,
    as a membership array 11x11x11) and the related triples of D2 (numpy array)."""
    out = []
    for R in C.arity3_tests():
        if R == (1 << 27) - 1:
            continue
        Rarr = np.array([(R >> x) & 1 for x in range(27)], dtype=bool).reshape(3, 3, 3)
        r1 = C.lift_ground_to_D1(R, D1)
        mem1 = np.zeros((M, M, M), dtype=bool)
        for a, b, c in r1:
            mem1[a, b, c] = True
        by = {}
        for a, b, c in r1:
            by.setdefault((a, b), []).append(c)
        rel = np.ones((N, N, N), dtype=bool)
        for (a, b), cs in by.items():
            mk = np.ones((3, 3, N), dtype=bool)
            for c in cs:
                mk &= Rarr[:, :, A[:, c]]
            rel &= mk[A[:, a][:, None], A[:, b][None, :], :]
        out.append((mem1, np.argwhere(rel).astype(np.int16)))
    return out


if __name__ == "__main__":
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(m4.HERE, "data", "bad_state_h.npy")
    h = np.load(path)
    supp = np.nonzero(h != BOT)[0]
    minimal = [int(x) for x in supp if not any(LE[y, x] and y != x for y in supp)]
    print(f"h: support {len(supp)}, {len(minimal)} minimal elements", flush=True)
    t0 = time.perf_counter()
    rels = lifted_triples()
    print(f"lifted arity-3 relations: {len(rels)} tests, {sum(len(r[1]) for r in rels)} related "
          f"triples ({time.perf_counter() - t0:.0f}s)", flush=True)

    s = z3.SolverFor("QF_FD")
    p = [[z3.Bool(f"p{x}_{a}") for a in range(M)] for x in range(N)]
    for x in range(N):
        s.add(z3.PbEq([(v, 1) for v in p[x]], 1))
    hasse = [(i, j) for i in range(N) for j in range(N)
             if i != j and LE[i, j] and (LE[i] & LE[:, j]).sum() == 2]
    for i, j in hasse:
        for a in range(M):
            s.add(z3.Implies(p[i][a], z3.Or([p[j][b] for b in range(M) if LE1[a, b]])))
    for m in minimal:
        s.add(z3.Or([p[m][a] for a in range(M) if A[m, a] != BOT]))

    rounds = 0
    while True:
        r = s.check()
        rounds += 1
        if r == z3.unsat:
            print(f"UNSAT after {rounds} rounds ({time.perf_counter() - t0:.0f}s): no monotone "
                  f"arity-3-preserving ψ makes F(ψ_F) total on supp(h), so h is NOT definable.")
            break
        mdl = s.model()
        psi = np.array([next(a for a in range(M) if z3.is_true(mdl.eval(p[x][a], True))) for x in range(N)])
        added = 0
        for mem1, tri in rels:
            v = psi[tri]
            bad = ~mem1[v[:, 0], v[:, 1], v[:, 2]]
            for a, b, c in tri[bad][:200]:
                s.add(z3.Not(z3.And(p[a][psi[a]], p[b][psi[b]], p[c][psi[c]])))
                added += 1
        if added == 0:
            print(f"SAT after {rounds} rounds: a monotone arity-3-preserving ψ exists "
                  f"(root test inconclusive for this h)")
            np.save(path.replace(".npy", "_psi.npy"), psi)
            break
        if rounds % 10 == 0:
            print(f"  round {rounds}: {added} constraints added ({time.perf_counter() - t0:.0f}s)", flush=True)
