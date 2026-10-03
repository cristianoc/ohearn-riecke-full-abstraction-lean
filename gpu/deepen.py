#!/usr/bin/env python3
"""Targeted next nesting level for a stuck state.

Given h (a bad state from universality.py) and a column set Q, build the next
round of nested columns
    F(λz. a)            and   F(λz. case z of tt -> a, ff -> b)
where a, b are atoms 'case q of tt -> u, ff -> v' (q in Q, u, v constants) or
constants, keeping only columns total on supp(h) (the only ones usable at the
root).  Pair compatibility is a matrix product on the GPU (MLX).  Then tries a
decision tree for h over Q plus the new columns.
"""
import os, sys, time
from itertools import product

import mlx.core as mx
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import m4

A, N, BOT, TT, FF = m4.A, m4.N, m4.BOT, m4.TT, m4.FF


def atoms_of(Q):
    out = [np.full(N, v, np.uint8) for v in (BOT, TT, FF)]
    for q in Q:
        for u, v in product((BOT, TT, FF), repeat=2):
            out.append(m4.case(q, np.full(N, u, np.uint8), np.full(N, v, np.uint8)))
    uniq = {x.tobytes(): x for x in out}
    return np.array(list(uniq.values()), dtype=np.uint8)


def deepen(h, Q, chunk=4096):
    supp = np.nonzero(h != BOT)[0]
    at = atoms_of(Q)
    print(f"  {len(at)} distinct atoms", flush=True)
    new = {}
    # shape λz.a: phi = (a, a, a)
    for x in at:
        col = m4.query(np.stack([x, x, x], axis=1))
        if (col[supp] != BOT).all():
            new.setdefault(col.tobytes(), col)
    # shape λz.case z of tt->a, ff->b: phi = (⊥, a, b); allowed (a_F, b_F) per F in supp
    allowed = np.zeros((len(supp), 3, 3), dtype=bool)
    for j, F in enumerate(supp):
        for u, v in product((BOT, TT, FF), repeat=2):
            allowed[j, u, v] = A[F, m4.IDX[BOT, u, v]] != BOT
    R = at[:, supp]                                           # (n, s)
    onehot = [mx.array((R == u).astype(np.float32)) for u in range(3)]
    bad_uv = [[mx.array((~allowed[:, u, v]).astype(np.float32)) for v in range(3)] for u in range(3)]
    n = len(at)
    found = 0
    for i0 in range(0, n, chunk):
        badcount = mx.zeros((min(chunk, n - i0), n))
        for u, v in product(range(3), repeat=2):
            left = onehot[u][i0:i0 + chunk] * bad_uv[u][v][None, :]
            badcount = badcount + left @ onehot[v].T
        ok = np.argwhere(np.array(badcount) == 0)
        for ia, ib in ok:
            a, b = at[i0 + ia], at[ib]
            col = m4.query(np.stack([np.zeros(N, np.uint8), a, b], axis=1))
            if col.tobytes() not in new:
                new[col.tobytes()] = col
                found += 1
    return np.array(list(new.values()), dtype=np.uint8) if new else np.zeros((0, N), np.uint8)


if __name__ == "__main__":
    h = np.load(os.path.join(m4.HERE, "data", "bad_state_h.npy"))
    c0, p0 = m4.columns_closed()
    n0, _ = m4.columns_nested(c0, p0, None)
    Q = np.array(c0 + n0, dtype=np.uint8)
    t = time.perf_counter()
    new = deepen(h, Q)
    print(f"next nesting level: {len(new)} new columns total on supp(h) ({time.perf_counter() - t:.0f}s)", flush=True)
    if len(new):
        tr = m4.tree_solves(None, np.vstack([Q, new]), h=h, beam=16)
        print("h definable with the deeper columns:", tr is not None, flush=True)
        np.save(os.path.join(m4.HERE, "data", "bad_state_deeper_columns.npy"), new)
