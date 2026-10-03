#!/usr/bin/env python3
"""Root-state search with arity-4 cuts and head-call column generation.

As root4.py, and in addition: when h survives arity 3, look for an invariant
head call psi (headcall_sat.py).  If one exists, its column F |-> F(psi_F) is
added as a cut; if none exists, h is not definable (HEADCALL.md Lemma 4,
OR/Sieber/HeadCall.lean), and h goes to the arity-4 check.

Original description: Root-state search with arity-4 cuts.

Find h : D2 -> B monotone, not constant, preserving every test of arity <= 4,
such that no column q (m4.py: the 11 closed calls and one round of nested
calls) is total on supp(h).  Such an h has no first call among these columns;
non-definability then needs the head-call argument (HEADCALL.md) as for h3.
Arity-3 and arity-4 constraints are added lazily (CEGAR); UNSAT means every h
preserving the arity-<=4 tests has a first call among the columns.
Usage: root5.py SECONDS"""
import os, sys, time
import numpy as np
import z3
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
t00 = time.time()
import m4, arity3_oracle, arity4_oracle as O, headcall_sat
A, N, LE, BOT, TT, FF = m4.A, m4.N, m4.LE, m4.BOT, m4.TT, m4.FF
cols, prov = m4.columns_closed()
new, nprov = m4.columns_nested(cols, prov, None)
Q = np.array(cols + new, dtype=np.uint8)
Q = Q[[i for i in range(len(Q)) if len(set(Q[i].tolist())) > 1]]
L3 = arity3_oracle.Oracle()
HC = headcall_sat.HeadCall(A, np.array(m4.D1, dtype=np.uint8), L3)
print(f"{len(Q)} columns; setup {time.time()-t00:.0f}s", flush=True)

s = z3.SolverFor("QF_FD")
t = [z3.Bool(f"t{x}") for x in range(N)]
f = [z3.Bool(f"f{x}") for x in range(N)]
d = [z3.Or(t[x], f[x]) for x in range(N)]
for x in range(N): s.add(z3.Not(z3.And(t[x], f[x])))
hasse = [(i, j) for i in range(N) for j in range(N) if i != j and LE[i, j] and (LE[i] & LE[:, j]).sum() == 2]
for i, j in hasse: s.add(z3.Implies(t[i], t[j]), z3.Implies(f[i], f[j]))
bot = [x for x in range(N) if LE[x].all()][0]
s.add(z3.Not(d[bot]), z3.Or(d))                      # not constant
for q in Q:                                          # no column total on supp(h)
    s.add(z3.Or([d[x] for x in np.nonzero(q == BOT)[0]]))
print(f"encoding: {len(s.assertions())} assertions ({time.time()-t00:.0f}s)", flush=True)

def neq(x, u):
    return z3.Not(t[x]) if u == TT else z3.Not(f[x]) if u == FF else d[x]

budget = float(sys.argv[1]); order = []; rounds = n3 = n4 = nc = 0
while True:
    left = budget - (time.time() - t00)
    if left <= 0: print(f"DEADLINE: {rounds} rounds, {n3} arity-3 and {n4} arity-4 cuts"); break
    s.set("timeout", int(left * 1000))
    r = s.check(); rounds += 1
    if r == z3.unknown: print(f"DEADLINE in solver: {rounds} rounds, {n3}/{n4} cuts"); break
    if r == z3.unsat:
        print(f"UNSAT after {rounds} rounds ({n3} arity-3, {n4} arity-4 cuts, {time.time()-t00:.0f}s): "
              "every h preserving the arity-<=4 tests has a total column on its support."); break
    m = s.model()
    h = np.array([TT if z3.is_true(m.eval(t[x], True)) else FF if z3.is_true(m.eval(f[x], True)) else BOT
                  for x in range(N)], dtype=np.uint8)
    viol = [w for w in L3.falsify(h) if w is not None]
    if viol:
        for (i, j, k) in viol: s.add(z3.Or(neq(i, int(h[i])), neq(j, int(h[j])), neq(k, int(h[k]))))
        n3 += len(viol)
        if rounds % 20 == 0: print(f"  round {rounds}: {n3} arity-3 cuts, |supp h| {int((h != BOT).sum())} ({time.time()-t00:.0f}s)", flush=True)
        continue
    st, psi = HC.find(h, max(1.0, budget - (time.time() - t00)))
    if st == "unknown": print(f"DEADLINE in the head-call search of round {rounds}"); break
    if st == "sat":
        q = A[np.arange(N), psi]
        s.add(z3.Or([d[x] for x in np.nonzero(q == BOT)[0]])); nc += 1
        print(f"  round {rounds}: head-call column {nc} (|supp h| {int((h != BOT).sum())}, {time.time()-t00:.0f}s)", flush=True)
        continue
    print(f"  round {rounds}: no invariant head call: h is not definable", flush=True)
    np.save(os.environ.get("ROOT4_LAST", os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "root5_last_h.npy")), h)
    print(f"  round {rounds}: arity-4 check of h with |supp h| {int((h != BOT).sum())} ({time.time()-t00:.0f}s)", flush=True)
    found, complete = O.falsify_subprocess(h, order, max(1.0, budget - (time.time() - t00)))
    if found:
        for mask, tup in found:
            s.add(z3.Or([neq(F, int(h[F])) for F in tup]))
            order = [mask] + [o for o in order if o != mask]
        n4 += len(found)
        print(f"  round {rounds}: arity-4 cut {found[0][1]} (|supp h| {int((h != BOT).sum())}, {time.time()-t00:.0f}s)", flush=True)
        continue
    if complete:
        print(f"SAT after {rounds} rounds: h preserves every test of arity <= 4 and no column is total on its support")
        np.save(os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "root5_h.npy"), h)
    else:
        print(f"DEADLINE during the arity-4 check of round {rounds}")
    break
