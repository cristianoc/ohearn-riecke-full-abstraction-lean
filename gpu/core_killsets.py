#!/usr/bin/env python3
"""Kill sets of the pair cores of D2.  For each ordered Theorem-6 pair core
(a, b), the set of (arity-3 test, position of bot) such that the tuple with bot
at that position and a, b at the others is related and the test excludes every
pattern that is bot there and defined elsewhere.  Prints how many distinct
kill sets occur.
Usage: core_killsets.py"""
import os, sys, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arity3_oracle
z = np.load(os.environ["M4_TABLES"]); A, D1 = z["A"], z["D1"]; N = len(A)
LE = ((A[:, None, :] == 0) | (A[:, None, :] == A[None, :, :])).all(axis=2); Li = LE.astype(np.uint8)
Bd = ((Li @ Li.T) > 0) & ~LE & ~LE.T; conv = A != 0
comp = ~((D1[:, None, :] != 0) & (D1[None, :, :] != 0) & (D1[:, None, :] != D1[None, :, :])).any(axis=2)
bot = int(np.nonzero(~conv.any(1))[0][0])
cores = [(int(a), int(b)) for a, b in zip(*np.nonzero(Bd)) if not (conv[a][:, None] & conv[b][None, :] & comp).any()]
kill = {p: set() for p in cores}
O = arity3_oracle.Oracle()
for ti, (R, tri) in enumerate(zip(O.R, O.tri)):
    for pos in range(3):
        oth = [i for i in range(3) if i != pos]
        def pat(u, v):
            g = [0, 0, 0]; g[oth[0]] = u; g[oth[1]] = v; return tuple(g)
        if not all(not R[pat(u, v)] for u in (1, 2) for v in (1, 2)): continue
        for a, b in tri[tri[:, pos] == bot][:, oth].tolist():
            if (a, b) in kill: kill[(a, b)].add((ti, pos))
ks = {frozenset(k) for k in kill.values()}
print(f"ordered pair cores {len(cores)}; distinct kill sets {len(ks)}; sizes {sorted({len(k) for k in ks})}")
