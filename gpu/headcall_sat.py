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

    def _solver(self):
        if getattr(self, "s", None) is None:
            A, M, N = self.A, self.D1.shape[0], self.A.shape[0]
            s = z3.SolverFor("QF_FD")
            self.p = p = [[z3.Bool(f"p{F}_{a}") for a in range(M)] for F in range(N)]
            for F in range(N): s.add(z3.PbEq([(v, 1) for v in p[F]], 1))
            for i, j in self.hasse:
                for a in range(M):
                    s.add(z3.Implies(p[i][a], z3.Or([p[j][b] for b in range(M) if self.LE1[a, b]])))
            # c[F]: "F is in supp(h)", passed as an assumption; then the head call converges at F
            self.c = [z3.Bool(f"c{F}") for F in range(N)]
            for F in range(N):
                s.add(z3.Implies(self.c[F], z3.Or([p[F][a] for a in range(M) if A[F, a] != 0])))
            self.s = s
        return self.s

    def find(self, h, budget):
        """Return (status, psi): status 'sat' (psi preserves the arity-<=3 tests),
        'unsat' (no such psi: h is not definable) or 'unknown'.  One persistent
        solver: the support of h enters as assumptions, cuts are kept."""
        t0 = time.time(); M, N = self.D1.shape[0], self.A.shape[0]
        # an invariant psi does not depend on h: reuse any earlier one that converges on supp(h)
        supp = np.nonzero(h)[0]
        for psi in getattr(self, "pool", []):
            if (self.A[supp, psi[supp]] != 0).all(): return "sat", psi
        s = self._solver(); p = self.p
        assume = [self.c[F] for F in np.nonzero(h)[0]]
        while True:
            left = budget - (time.time() - t0)
            if left <= 0: return "unknown", None
            s.set("timeout", int(left * 1000)); r = s.check(*assume)
            if r == z3.unknown: return "unknown", None
            if r == z3.unsat: return "unsat", None
            mdl = s.model()
            psi = np.array([next(a for a in range(M) if z3.is_true(mdl.eval(p[F][a], True))) for F in range(N)])
            new = 0
            for mm, tri in zip(self.mem1, self.L3.tri):
                q = psi[tri]
                for b in np.flatnonzero(~mm[q[:, 0], q[:, 1], q[:, 2]])[:20]:
                    i, j, k = (int(v) for v in tri[b])
                    s.add(z3.Not(z3.And(p[i][int(psi[i])], p[j][int(psi[j])], p[k][int(psi[k])]))); new += 1
            if new == 0:
                self.pool = getattr(self, "pool", []) + [psi]
                return "sat", psi

if __name__ == "__main__":
    t00 = time.time()
    tabs = np.load(os.environ.get("M4_TABLES", os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "m4_tables.npz")))
    hc = HeadCall(tabs["A"], tabs["D1"], arity3_oracle.Oracle())
    h = np.load(sys.argv[1])
    bot = int(np.nonzero((tabs["A"] == 0).all(axis=1))[0][0])
    if h[bot] != 0: print("h is defined at the least element: constant, Lemma 4 does not apply"); sys.exit()
    st, psi = hc.find(h, float(sys.argv[2]))
    print(f"{st} ({time.time()-t00:.0f}s)" + (": h is not definable" if st == "unsat" else ""))
    if st == "sat": np.save(os.path.join(os.path.dirname(os.path.abspath(sys.argv[1])), "headcall_psi.npy"), psi)
