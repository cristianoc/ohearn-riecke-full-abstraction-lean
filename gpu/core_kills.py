#!/usr/bin/env python3
"""Do small non-definability cores die at arity |K|+1 through a bottom tuple?

A Theorem-6 core K (HEADCALL.md) is a set of elements of D2 that pairwise have
common upper bounds where required and admit no pairwise-compatible choice of
convergent arguments.  Any non-constant table defined on K is not definable,
and is 0 at the least element bot.  This script enumerates the minimal
Theorem-6 cores of size 2 and 3 and checks whether some test of arity |K|+1
relates (bot, K) (in some order) while excluding every pattern that is bot at
bot's position and defined elsewhere; such a test kills every table through K.
Usage: core_kills.py SECONDS"""
import os, sys, time, itertools
from itertools import product, permutations
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arity_lib as L, arity3_oracle, arity4_h3
t0 = time.time(); budget = float(sys.argv[1])
z = np.load(os.environ["M4_TABLES"]); A, D1 = z["A"], z["D1"]; N, M = A.shape
LE = ((A[:, None, :] == 0) | (A[:, None, :] == A[None, :, :])).all(axis=2); Li = LE.astype(np.uint8)
Bd = ((Li @ Li.T) > 0) & ~LE & ~LE.T           # incomparable pairs with a common upper bound
conv = A != 0
comp = ~((D1[:, None, :] != 0) & (D1[None, :, :] != 0) & (D1[:, None, :] != D1[None, :, :])).any(axis=2)
bot = int(np.nonzero(~conv.any(1))[0][0])
paircore = np.zeros((N, N), bool)
for a, b in zip(*np.nonzero(Bd)):
    paircore[a, b] = not (conv[a][:, None] & conv[b][None, :] & comp).any()
pairs = [(int(a), int(b)) for a, b in zip(*np.nonzero(np.triu(paircore)))]
# arity 3: kill (bot, a, b)
O = arity3_oracle.Oracle(); killed = np.zeros(N * N, bool)
for R, tri in zip(O.R, O.tri):
    for pos in range(3):
        oth = [i for i in range(3) if i != pos]
        def pat(u, v):
            g = [0, 0, 0]; g[oth[0]] = u; g[oth[1]] = v; return tuple(g)
        if all(not R[pat(u, v)] for u in (1, 2) for v in (1, 2)):
            sel = tri[tri[:, pos] == bot]; killed[sel[:, oth[0]] * N + sel[:, oth[1]]] = True
pk = sum(bool(killed[a * N + b] or killed[b * N + a]) for a, b in pairs)
print(f"pair cores: {len(pairs)}, killed at arity 3: {pk} ({time.time()-t0:.1f}s)", flush=True)
# arity 4: minimal triple cores
cores = set()
for a in range(N):
    for b, c in itertools.combinations(np.nonzero(Bd[a])[0], 2):
        if paircore[a, b] or paircore[a, c] or paircore[b, c]: continue
        Cab = conv[a][:, None] & conv[b][None, :] & comp
        Cac = conv[a][:, None] & conv[c][None, :] & comp
        Cbc = (conv[b][:, None] & conv[c][None, :]) & (comp if Bd[b, c] else True)
        if not (Cab[:, :, None] & Cac[:, None, :] & Cbc[None, :, :]).any(): cores.add(tuple(sorted((a, int(b), int(c)))))
cores = sorted(cores); X = np.array(cores)
print(f"minimal triple cores: {len(cores)} ({time.time()-t0:.1f}s)", flush=True)
kill4 = np.zeros(len(cores), bool); Phis = np.array(list(product(range(M), repeat=4)))
for m in sorted(arity4_h3.canonical_tests()):
    if kill4.all() or time.time() - t0 > budget: break
    Rarr = np.array([(m >> k) & 1 for k in range(81)], bool).reshape(3, 3, 3, 3)
    gt = np.argwhere(Rarr)
    rel1 = None
    for pos in range(4):
        oth = [i for i in range(4) if i != pos]
        def pat(vals):
            g = [0] * 4
            for i, v in zip(oth, vals): g[i] = v
            return tuple(g)
        if any(Rarr[pat(v)] for v in product((1, 2), repeat=3)): continue
        if rel1 is None: rel1 = Phis[Rarr[tuple(D1[Phis[:, None, i], gt[None, :, i]] for i in range(4))].all(axis=1)]
        for perm in permutations(range(3)):
            idx = np.nonzero(~kill4)[0]
            if not len(idx): break
            Y = np.zeros((len(idx), 4), np.int64); Y[:, pos] = bot
            for i, p in zip(oth, perm): Y[:, i] = X[idx, p]
            kill4[idx[L.related(A, rel1, Rarr, Y)]] = True
print(f"triple cores killed at arity 4: {int(kill4.sum())}/{len(cores)} ({time.time()-t0:.1f}s)")
