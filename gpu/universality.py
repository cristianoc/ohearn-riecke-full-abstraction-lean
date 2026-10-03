#!/usr/bin/env python3
"""Try to prove that tau0 = ((B -> B) -> B) -> B is universal, by SAT.

Let Q be a finite set of definable query columns q : D2 -> B (m4.py: the 11
closed calls and one round of nested calls).  A *state* is (h, S):
  * h : D2 -> B monotone, preserving every arity-3 test;
  * S an intersection of sets q^-1(v) (q in Q, v in {tt, ff}); initially S = D2.
q is a progressing splitter at (h, S) when q is total on supp(h) n S and neither
S subset q^-1(tt) nor S subset q^-1(ff).  Then h = case q of tt -> ..., ff -> ...
on S, and both children (h, S n q^-1(v)) are states with smaller S.  States where
h is constant on S are leaves.

Hence if no state is non-constant without a progressing splitter, every h that
preserves the arity-3 tests is definable (induction on |S|), and in particular
every element of the Sieber carrier: tau0 is universal.

The solver searches for such a bad state.  The arity-3 constraints are added
lazily (CEGAR) using the M1 kernel as the violation oracle; UNSAT of a relaxation
is UNSAT.  If a bad state is found, the script reports it.
"""
import os, sys, time

import numpy as np
import z3

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sieber_cpu as C
import sieber_metal as G
import m4

A, N, LE, BOT, TT, FF = m4.A, m4.N, m4.LE, m4.BOT, m4.TT, m4.FF

# ---------------------------------------------------------------------------
# Columns and the arity-3 oracle
# ---------------------------------------------------------------------------
cols, prov = m4.columns_closed()
new, nprov = m4.columns_nested(cols, prov, None)
Q = np.array(cols + new, dtype=np.uint8)
prov = prov + nprov
# drop columns that can never split (constant on D2)
useful = [i for i in range(len(Q)) if len(set(Q[i].tolist())) > 1]
Q, prov = Q[useful], [prov[i] for i in useful]
print(f"{len(Q)} non-constant columns")

tests = C.arity3_tests()
D1 = C.carrier_D1()
D2 = [tuple(r) for r in A.tolist()]
rel1 = [C.lift_ground_to_D1(R, D1) for R in tests]
L2 = G.Level(D2, tests, rel1)

# ---------------------------------------------------------------------------
# Encoding
# ---------------------------------------------------------------------------
s = z3.SolverFor("QF_FD")
t = [z3.Bool(f"t{x}") for x in range(N)]
f = [z3.Bool(f"f{x}") for x in range(N)]
inS = [z3.Bool(f"s{x}") for x in range(N)]
E = [z3.Bool(f"e{x}") for x in range(N)]          # x in S and h(x) defined

hasse = [(i, j) for i in range(N) for j in range(N)
         if i != j and LE[i, j] and (LE[i] & LE[:, j]).sum() == 2]
for x in range(N):
    s.add(z3.Not(z3.And(t[x], f[x])))
    s.add(E[x] == z3.And(inS[x], z3.Or(t[x], f[x])))
for i, j in hasse:                                   # h monotone, S upward closed
    s.add(z3.Implies(t[i], t[j]), z3.Implies(f[i], f[j]), z3.Implies(inS[i], inS[j]))

# a[q][v]: S subset q^-1(v)
a = {}
for qi in range(len(Q)):
    for v in (TT, FF):
        av = z3.Bool(f"a{qi}_{v}")
        a[qi, v] = av
        outside = np.nonzero(Q[qi] != v)[0]
        for y in outside:
            s.add(z3.Implies(av, z3.Not(inS[y])))
# S has the reachable form: every x outside S is excluded by some q^-1(v) containing S
for x in range(N):
    ex = [a[qi, v] for qi in range(len(Q)) for v in (TT, FF) if Q[qi, x] != v]
    s.add(z3.Or([inS[x]] + ex))
# h is not constant on S: at least two of the three values occur in S
occ = [z3.Or([z3.And(inS[x], z3.Not(t[x]), z3.Not(f[x])) for x in range(N)]),
       z3.Or([z3.And(inS[x], t[x]) for x in range(N)]),
       z3.Or([z3.And(inS[x], f[x]) for x in range(N)])]
s.add(z3.PbGe([(o, 1) for o in occ], 2))
# no progressing splitter
for qi in range(len(Q)):
    undefined_on_support = z3.Or([E[x] for x in np.nonzero(Q[qi] == BOT)[0]] or [z3.BoolVal(False)])
    s.add(z3.Or(undefined_on_support, a[qi, TT], a[qi, FF]))
print(f"encoding built: {len(s.assertions())} assertions", flush=True)

# ---------------------------------------------------------------------------
# CEGAR on the arity-3 tests
# ---------------------------------------------------------------------------
def neq(x, u):
    return z3.Not(t[x]) if u == TT else z3.Not(f[x]) if u == FF else z3.Or(t[x], f[x])


rounds = 0
t0 = time.perf_counter()
while True:
    r = s.check()
    rounds += 1
    if r == z3.unsat:
        print(f"UNSAT after {rounds} rounds ({time.perf_counter() - t0:.0f}s): every state has a "
              f"progressing splitter, so every h preserving the arity-3 tests is definable "
              f"over these {len(Q)} columns -- tau0 is universal.")
        break
    m = s.model()
    h = np.array([TT if z3.is_true(m.eval(t[x], True)) else FF if z3.is_true(m.eval(f[x], True)) else BOT
                  for x in range(N)], dtype=np.uint8)
    S = np.array([z3.is_true(m.eval(inS[x], True)) for x in range(N)])
    ws = L2.falsify(h)
    viol = [(k, w) for k, w in enumerate(ws) if w is not None]
    if not viol:
        print(f"SAT after {rounds} rounds: bad state found (h preserves all arity-3 tests)")
        print("  |S| =", int(S.sum()), " supp(h) in S =", int((S & (h != BOT)).sum()),
              " values in S:", {int(v): int(((h == v) & S).sum()) for v in (BOT, TT, FF)})
        np.save(os.path.join(m4.HERE, "data", "bad_state_h.npy"), h)
        np.save(os.path.join(m4.HERE, "data", "bad_state_S.npy"), S)
        break
    for k, (i, j, kk) in viol:
        s.add(z3.Or(neq(i, int(h[i])), neq(j, int(h[j])), neq(kk, int(h[kk]))))
    if rounds % 10 == 0:
        print(f"  round {rounds}: {len(viol)} violated tests added ({time.perf_counter() - t0:.0f}s)", flush=True)
