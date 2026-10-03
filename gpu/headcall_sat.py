#!/usr/bin/env python3
"""Invariant head-call test for a table h : D2 -> B.

If h is definable and not constant, its normal form starts with a call
F(psi_F) where F |-> psi_F is definable (HEADCALL.md, Lemma 4), hence an element
of Sieber's model at tau1 -> (B -> B): monotone and preserving every test.
This script asks z3 for psi : D2 -> D1, monotone, with F(psi_F) defined on
supp(h), preserving every test of arity <= 3 (added lazily from the related
triples of D2).  UNSAT proves h is not definable.
Usage: headcall_sat.py H.npy SECONDS"""
import os, sys, time
import numpy as np
import z3
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arity3_oracle, sieber_cpu as C
class HeadCall:
    """Search for an invariant head call psi : D2 -> D1 for a table h."""
    def __init__(self, A, D1, L3):
        self.A, self.D1, self.L3 = A, D1, L3
        N, M = A.shape
        self.LE2 = np.array([[np.all((A[i] == 0) | (A[i] == A[j])) for j in range(N)] for i in range(N)])
        self.LE1 = np.array([[np.all((D1[a] == 0) | (D1[a] == D1[b])) for b in range(M)] for a in range(M)])
        self.hasse = [(i, j) for i in range(N) for j in range(N)
                      if i != j and self.LE2[i, j] and (self.LE2[i] & self.LE2[:, j]).sum() == 2]
        self.mem1 = []
        for R in L3.tests:
            r1 = C.lift_ground_to_D1(R, [tuple(int(v) for v in row) for row in D1])
            mm = np.zeros((M, M, M), bool)
            for a, b, c in r1: mm[a, b, c] = True
            self.mem1.append(mm)
        self.cuts = []          # violated triples, kept across calls (they hold for every h)

    def find(self, h, budget):
        """Return (status, psi): status 'sat' (psi preserves the arity-<=3 tests),
        'unsat' (no such psi: h is not definable) or 'unknown'."""
        t0 = time.time(); A, M, N = self.A, self.D1.shape[0], self.A.shape[0]
        s = z3.SolverFor("QF_FD")
        p = [[z3.Bool(f"p{F}_{a}") for a in range(M)] for F in range(N)]
        for F in range(N): s.add(z3.PbEq([(v, 1) for v in p[F]], 1))
        for i, j in self.hasse:
            for a in range(M):
                s.add(z3.Implies(p[i][a], z3.Or([p[j][b] for b in range(M) if self.LE1[a, b]])))
        for F in np.nonzero(h)[0]:
            s.add(z3.Or([p[F][a] for a in range(M) if A[F, a] != 0]))
        for (i, a), (j, b), (k, c) in self.cuts:
            s.add(z3.Not(z3.And(p[i][a], p[j][b], p[k][c])))
        while True:
            left = budget - (time.time() - t0)
            if left <= 0: return "unknown", None
            s.set("timeout", int(left * 1000)); r = s.check()
            if r == z3.unknown: return "unknown", None
            if r == z3.unsat: return "unsat", None
            mdl = s.model()
            psi = np.array([next(a for a in range(M) if z3.is_true(mdl.eval(p[F][a], True))) for F in range(N)])
            new = 0
            for mm, tri in zip(self.mem1, self.L3.tri):
                q = psi[tri]
                for b in np.flatnonzero(~mm[q[:, 0], q[:, 1], q[:, 2]])[:20]:
                    i, j, k = (int(v) for v in tri[b])
                    cut = ((i, int(psi[i])), (j, int(psi[j])), (k, int(psi[k])))
                    self.cuts.append(cut); s.add(z3.Not(z3.And(*(p[x][a] for x, a in cut)))); new += 1
            if new == 0: return "sat", psi


if __name__ == "__main__":
    t00 = time.time()
    tabs = np.load(os.environ.get("M4_TABLES", os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "m4_tables.npz")))
    hc = HeadCall(tabs["A"], tabs["D1"], arity3_oracle.Oracle())
    h = np.load(sys.argv[1])
    st, psi = hc.find(h, float(sys.argv[2]))
    print(f"{st} ({time.time()-t00:.0f}s)" + (": h is not definable" if st == "unsat" else ""))
    if st == "sat": np.save(os.path.join(os.path.dirname(os.path.abspath(sys.argv[1])), "headcall_psi.npy"), psi)
