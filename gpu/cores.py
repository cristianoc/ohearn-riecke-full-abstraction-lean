"""Minimal non-definability cores: a set K of elements of D2 such that no
monotone psi : D2 -> D1 preserving the arity-<=3 tests has F(psi_F) defined
for every F in K.  Any table whose support contains K is then not definable
(HEADCALL.md Lemma 4).  Shrinks the minimal points of a table's support.
Usage: cores.py H.npy SECONDS"""
import os, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arity3_oracle, headcall_sat
t0 = time.time()
tabs = np.load(os.environ["M4_TABLES"]); A, D1 = tabs["A"], tabs["D1"]; N = len(A)
hc = headcall_sat.HeadCall(A, D1, arity3_oracle.Oracle())
h = np.load(sys.argv[1]); budget = float(sys.argv[2])
supp = np.nonzero(h)[0]
mins = [int(x) for x in supp if not any(hc.LE2[y, x] and y != x for y in supp)]
def unsat(K):
    g = np.zeros(N, np.uint8); g[list(K)] = 1
    st, _ = hc.find(g, 30); return st == "unsat"
print(f"{len(mins)} minimal points; UNSAT on them: {unsat(mins)} ({time.time()-t0:.0f}s)", flush=True)
K = list(mins)
for x in list(K):                          # deletion-based shrinking to a minimal core
    if time.time() - t0 > budget: print("deadline"); break
    if unsat([y for y in K if y != x]): K.remove(x)
print(f"core {K} (size {len(K)}), {time.time()-t0:.0f}s")
