#!/usr/bin/env python3
"""M4: two-sided classification of the two-cone problems at tau0.

Each pair {p, q} of incomparable elements of D2 asks whether the up-set
U = up(p) u up(q) is the convergence domain of a definable term; equivalently
whether union(p, q) (tt on U, bot elsewhere) is definable (see REPORT.md).

Proof objects are enumerated once and applied to every unresolved pair:
  * definable side: level-0 query columns F |-> F(phi_F), where phi_F is built
    from earlier columns (iterated nesting), and best-first decision trees over
    them.  A tree found is a term: the pair is definable.
  * non-definable side: two-world Kripke relations (as in REPORT.md).  A
    violation proves non-definability.
Writes gpu/data/m4_pairs.json: pair -> status and certificate.
"""
import json, os, sys, time
from functools import lru_cache
from itertools import product

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sieber_cpu as C

HERE = os.path.dirname(os.path.abspath(__file__))
BOT, TT, FF = 0, 1, 2
D1 = C.carrier_D1()
D2 = sorted(C.definable_D2(D1))
A = np.array(D2, dtype=np.uint8)
N = len(D2)
LE = ((A[:, None, :] == 0) | (A[:, None, :] == A[None, :, :])).all(axis=2)
IDX = -np.ones((3, 3, 3), dtype=np.int16)
for i, f in enumerate(D1):
    IDX[f] = i

# ---------------------------------------------------------------------------
# Pairs
# ---------------------------------------------------------------------------
classes = json.load(open(os.path.join(HERE, "data", "m2_survivor_classes.json")))
pairs = sorted({tuple(sorted(c["minT"] + c["minF"])) for c in classes
                if len(c["minT"]) + len(c["minF"]) == 2})
targets = np.array([LE[p] | LE[q] for p, q in pairs])            # (P, N) bool
status = {pr: None for pr in pairs}                                # None = open


def record(k, kind, cert):
    if status[pairs[k]] is None:
        status[pairs[k]] = {"status": kind, "certificate": cert}


# ---------------------------------------------------------------------------
# Definable side
# ---------------------------------------------------------------------------
def query(phi):
    """phi: (N, 3) values of the argument at (bot, tt, ff) for each F -> column."""
    ix = IDX[phi[:, 0], phi[:, 1], phi[:, 2]]
    assert (ix >= 0).all()
    return A[np.arange(N), ix].astype(np.uint8)


def case(c, a, b):
    return np.where(c == BOT, BOT, np.where(c == TT, a, b)).astype(np.uint8)


def tree_solves(U, cols, beam=12, h=None):
    """Best-first search for a decision tree over `cols` computing tt on U, bot
    elsewhere (or the table h, if given)."""
    if h is None:
        h = np.where(U, TT, BOT).astype(np.uint8)

    @lru_cache(maxsize=None)
    def solve(S):
        Sa = np.array(S, dtype=np.int64)
        hv = h[Sa]
        if len(set(hv.tolist())) <= 1:
            return ("leaf", int(hv[0]) if len(hv) else BOT)
        sub = cols[:, Sa]
        ok = ~((sub == BOT) & (hv != BOT)).any(axis=1)
        prog = ~(sub == TT).all(axis=1) & ~(sub == FF).all(axis=1)
        qs = np.nonzero(ok & prog)[0]
        def impurity(q):
            cost = 0
            for v in (TT, FF):
                part = hv[sub[q] == v]
                if len(part) and len(set(part.tolist())) > 1:
                    cost += len(part)
            return cost
        for q in sorted(qs, key=impurity)[:beam]:
            a = solve(tuple(Sa[sub[q] == TT].tolist()))
            if a is None:
                continue
            b = solve(tuple(Sa[sub[q] == FF].tolist()))
            if b is None:
                continue
            return ("case", int(q), a, b)
        return None
    return solve(tuple(range(N)))


def intersection_solves(U, cols):
    """U is the intersection of the domains of columns defined on all of U
    (sequential composition 'if c1 then (if c2 then ... tt)')."""
    doms = cols != BOT
    cover = doms[:, U].all(axis=1)
    if not cover.any():
        return None
    inter = doms[cover].all(axis=0)
    return np.nonzero(cover)[0].tolist() if (inter == U).all() else None


def columns_closed():
    cols = [A[:, a].copy() for a in range(len(D1))]
    prov = [f"F({a})" for a in range(len(D1))]
    return cols, prov


def columns_nested(cols, prov, keep):
    """New columns F(lambda z. g) with g built from existing columns:
      g = x (z unused) -> phi = (x, x, x);
      g = case z of tt -> a, ff -> b -> phi = (bot, a, b);
    where x, a, b range over atoms: constants and 'case c of tt -> u, ff -> v'
    with c an existing column and u, v constants.  Only columns defined on the
    whole of some open target (`keep`) are retained."""
    atoms = [np.full(N, v, dtype=np.uint8) for v in (BOT, TT, FF)]
    aprov = ["⊥", "tt", "ff"]
    names = {BOT: "⊥", TT: "tt", FF: "ff"}
    seen = {x.tobytes() for x in atoms}
    for c, pc in zip(cols, prov):
        for u, v in product((BOT, TT, FF), repeat=2):
            x = case(c, np.full(N, u, np.uint8), np.full(N, v, np.uint8))
            if x.tobytes() not in seen:
                seen.add(x.tobytes())
                atoms.append(x)
                aprov.append(f"case {pc} of tt->{names[u]}, ff->{names[v]}")
    new, nprov = [], []
    have = {c.tobytes() for c in cols}
    def consider(phi, p):
        col = query(phi)
        key = col.tobytes()
        if key in have:
            return
        dom = col != BOT
        if keep is not None and not (dom[None, :] | ~keep).all(axis=1).any():
            return
        have.add(key)
        new.append(col)
        nprov.append(p)
    for x, px in zip(atoms, aprov):
        consider(np.stack([x, x, x], axis=1), f"F(λz. {px})")
    for (a, pa), (b, pb) in product(list(zip(atoms, aprov)), repeat=2):
        consider(np.stack([np.zeros(N, np.uint8), a, b], axis=1),
                 f"F(λz. case z of tt->[{pa}], ff->[{pb}])")
    return new, nprov


def definable_round(cols, prov, label):
    C_ = np.array(cols, dtype=np.uint8)
    t = time.perf_counter()
    solved = 0
    for k, pr in enumerate(pairs):
        if status[pr] is not None:
            continue
        U = targets[k]
        cover = intersection_solves(U, C_)
        if cover is not None:
            record(k, "definable", {"method": "intersection", "columns": [prov[c] for c in cover]})
            solved += 1
            continue
        tree = tree_solves(U, C_)
        if tree is not None:
            def show(tr):
                return ("tt" if tr[1] == TT else "⊥") if tr[0] == "leaf" else \
                    [prov[tr[1]], show(tr[2]), show(tr[3])]
            record(k, "definable", {"method": "tree", "tree": show(tree)})
            solved += 1
    print(f"[{label}] {len(cols)} columns: {solved} pairs newly definable; "
          f"{sum(v is None for v in status.values())} open ({time.perf_counter() - t:.0f}s)", flush=True)


# ---------------------------------------------------------------------------
# Non-definable side: two-world Kripke relations, vectorised over pairs
# ---------------------------------------------------------------------------
sys.path.insert(0, HERE)


def kripke_round():
    import search_kripke_two_world as K
    open_idx = [k for k, pr in enumerate(pairs) if status[pr] is None]
    if not open_idx:
        return
    Uo = targets[open_idx].astype(np.float32)                     # (P, N)
    t = time.perf_counter()
    n = 0
    for desc, Rw, relD2 in K.relations():
        n += 1
        # union(p, q) takes values tt on U, bot elsewhere; violation iff some
        # related (a, b) has (h a, h b) outside R(w)
        viol = np.zeros(len(open_idx), dtype=bool)
        R = relD2.astype(np.float32)
        for u, v in product((BOT, TT), repeat=2):
            if Rw[u, v]:
                continue
            L = Uo if u == TT else 1 - Uo
            Rr = Uo if v == TT else 1 - Uo
            viol |= ((L @ R) * Rr).sum(axis=1) > 0
        for i in np.nonzero(viol)[0]:
            record(open_idx[i], "non-definable", {"kripke": desc})
    print(f"[kripke] {n} two-world relations; {sum(v is None for v in status.values())} open "
          f"({time.perf_counter() - t:.0f}s)", flush=True)


if __name__ == "__main__":
    print(f"{len(pairs)} two-cone pair problems")
    cols, prov = columns_closed()
    definable_round(cols, prov, "closed calls")
    for r in range(2):
        if all(v is not None for v in status.values()):
            break
        keep = targets[[k for k, pr in enumerate(pairs) if status[pr] is None]]
        new, nprov = columns_nested(cols, prov, keep)
        cols, prov = cols + new, prov + nprov
        definable_round(cols, prov, f"nested round {r + 1}")
    if "--kripke" in sys.argv:
        kripke_round()

    # the remaining survivor classes (three or four cones): search trees for the
    # full table, over the same columns plus one more nested round built for them
    rest = [c for c in classes if len(c["minT"]) + len(c["minF"]) > 2]
    def table(c):
        h = np.zeros(N, dtype=np.uint8)
        for x in c["minT"]:
            h[LE[x]] = TT
        for x in c["minF"]:
            h[LE[x]] = FF
        return h
    tables = [table(c) for c in rest]
    C_ = np.array(cols, dtype=np.uint8)
    multi = {}
    for c, h in zip(rest, tables):
        tr = tree_solves(None, C_, h=h)
        multi[json.dumps([c["minT"], c["minF"]])] = "definable" if tr is not None else None
    left = [k for k, v in multi.items() if v is None]
    print(f"[multi-cone] {len(rest)} classes with 3-4 cones: {len(rest) - len(left)} definable, "
          f"{len(left)} open", flush=True)
    if left:
        keep = np.array([table(rest[i]) != BOT for i, (k, v) in enumerate(multi.items()) if v is None])
        new, nprov = columns_nested(cols, prov, keep)
        C_ = np.array(cols + new, dtype=np.uint8)
        for i, (k, v) in enumerate(multi.items()):
            if v is None and tree_solves(None, C_, h=tables[i]) is not None:
                multi[k] = "definable"
        print(f"[multi-cone] after a nested round: {sum(v is None for v in multi.values())} open", flush=True)
    json.dump(multi, open(os.path.join(HERE, "data", "m4_multicone.json"), "w"))
    out = {f"{p},{q}": status[(p, q)] for p, q in pairs}
    json.dump(out, open(os.path.join(HERE, "data", "m4_pairs.json"), "w"))
    counts = {}
    for v in status.values():
        k = "open" if v is None else v["status"]
        counts[k] = counts.get(k, 0) + 1
    print("final:", counts)


def verify_all_classes():
    """Direct check, without the union/race reduction: every survivor class's own
    table has a decision tree over the closed and first-round nested columns."""
    cols, prov = columns_closed()
    new, nprov = columns_nested(cols, prov, None)
    C_ = np.array(cols + new, dtype=np.uint8)
    bad = []
    for c in classes:
        h = np.zeros(N, dtype=np.uint8)
        for x in c["minT"]:
            h[LE[x]] = TT
        for x in c["minF"]:
            h[LE[x]] = FF
        if tree_solves(None, C_, h=h) is None:
            bad.append(c)
    print(f"[verify] {len(classes) - len(bad)}/{len(classes)} survivor classes have a tree "
          f"over {len(C_)} columns", flush=True)
    return bad
