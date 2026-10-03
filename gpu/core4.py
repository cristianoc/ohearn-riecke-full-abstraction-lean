#!/usr/bin/env python3
"""Tables through a non-definability core.

Given a core K (cores.py: no invariant head call converges on all of K), search
h : D2 -> B monotone with h(x) defined for x in K, preserving every test of
arity <= 3 and <= 4 (CEGAR with arity3_oracle and arity4_oracle).  Every such h
is not definable.  UNSAT: no table through K survives arity 4.
Usage: core4.py SECONDS K0 K1 ..."""
import os, sys, time
import numpy as np
import z3
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arity3_oracle, arity4_oracle as O
t00 = time.time()
tabs = np.load(os.environ["M4_TABLES"]); A = tabs["A"]; N = len(A)
BOT, TT, FF = 0, 1, 2
LE = ((A[:, None, :] == 0) | (A[:, None, :] == A[None, :, :])).all(axis=2)
L3 = arity3_oracle.Oracle()
budget = float(sys.argv[1]); K = [int(a) for a in sys.argv[2:]]
s = z3.SolverFor("QF_FD")
t = [z3.Bool(f"t{x}") for x in range(N)]; f = [z3.Bool(f"f{x}") for x in range(N)]
d = [z3.Or(t[x], f[x]) for x in range(N)]
for x in range(N): s.add(z3.Not(z3.And(t[x], f[x])))
for i in range(N):
    for j in range(N):
        if i != j and LE[i, j] and (LE[i] & LE[:, j]).sum() == 2:
            s.add(z3.Implies(t[i], t[j]), z3.Implies(f[i], f[j]))
for x in K: s.add(d[x])
bot = int(np.nonzero(LE.all(axis=1))[0][0])
s.add(z3.Not(d[bot]))      # not constant: Lemma 4 applies only to non-constant tables
print(f"core {K}; setup {time.time()-t00:.0f}s", flush=True)
def neq(x, u): return z3.Not(t[x]) if u == TT else z3.Not(f[x]) if u == FF else d[x]
from itertools import product
def related_cut(tup, Rarr):
    """tup is R-related, so (h(tup_i))_i must lie in R: forbid every pattern outside R."""
    return [z3.Or([neq(x, g[i]) for i, x in enumerate(tup)]) for g in product(range(3), repeat=len(tup)) if not Rarr[g]]
order = []; rounds = n3 = n4 = 0
while True:
    left = budget - (time.time() - t00)
    if left <= 0: print(f"DEADLINE: {rounds} rounds, {n3} arity-3 and {n4} arity-4 cuts"); break
    s.set("timeout", int(left * 1000)); r = s.check(); rounds += 1
    if r == z3.unknown: print(f"DEADLINE in solver: {rounds} rounds, {n3}/{n4} cuts"); break
    if r == z3.unsat:
        print(f"UNSAT after {rounds} rounds ({n3} arity-3, {n4} arity-4 cuts, {time.time()-t00:.0f}s): "
              f"no monotone table defined on the core preserves the arity-<=4 tests"); break
    m = s.model()
    h = np.array([TT if z3.is_true(m.eval(t[x], True)) else FF if z3.is_true(m.eval(f[x], True)) else BOT
                  for x in range(N)], dtype=np.uint8)
    viol = [(R, w) for R, w in zip(L3.R, L3.falsify(h)) if w is not None]
    if viol:
        for R, w in viol: s.add(*related_cut(w, R))
        n3 += len(viol); continue
    np.save(os.path.join(os.environ.get("SP", "."), "core4_last_h.npy"), h)
    found, complete = O.falsify_subprocess(h, order, max(1.0, budget - (time.time() - t00)))
    if found:
        for mask, tup in found:
            Rarr = np.array([(mask >> k) & 1 for k in range(81)], dtype=bool).reshape(3, 3, 3, 3)
            s.add(*related_cut(tup, Rarr)); order = [mask] + [o for o in order if o != mask]
        n4 += len(found)
        print(f"  round {rounds}: arity-4 cut {found[0][1]} values {[int(h[F]) for F in found[0][1]]} (|supp h| {int((h != BOT).sum())}, {time.time()-t00:.0f}s)", flush=True)
        continue
    print("SAT: h preserves every test of arity <= 4" if complete else f"DEADLINE during the arity-4 check of round {rounds}")
    break
