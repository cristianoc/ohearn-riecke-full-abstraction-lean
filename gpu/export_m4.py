#!/usr/bin/env python3
"""Export the M4 data requested for the universality analysis (gpu/data/m4_export/).

  columns.json      every column of Q (closed calls + one nested round): table
                    (355 chars over ⊥/t/f), smallest generating term, term size,
                    F-nesting depth, structured provenance (DAG by column id)
  trees.json        a decision-tree certificate for each of the 13,460 survivor
                    classes (nodes name column ids), with depth and usage stats
  nested_pairs.json the 278 pair problems that needed nested calls, with the
                    nested columns (their a, b) used by their trees
"""
import json, os, sys
from collections import Counter
from itertools import product

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import m4

A, N, LE, BOT, TT, FF = m4.A, m4.N, m4.LE, m4.BOT, m4.TT, m4.FF
D1 = m4.D1
OUT = os.path.join(m4.HERE, "data", "m4_export")
os.makedirs(OUT, exist_ok=True)
V = {BOT: "⊥", TT: "tt", FF: "ff"}
CH = {BOT: "⊥", TT: "t", FF: "f"}


def tabstr(x):
    return "".join(CH[int(v)] for v in x)


def closed_arg(phi):
    """A term for the closed element phi = (phi(⊥), phi(tt), phi(ff)) of B -> B."""
    b, t, f = D1[phi]
    if b != BOT:
        return f"λz.{V[b]}", 2
    if (t, f) == (TT, FF):
        return "λz.z", 2
    if t == f:
        return f"λz.case z of tt->{V[t]}, ff->{V[f]}", 4
    return f"λz.case z of tt->{V[t]}, ff->{V[f]}", 4


# ---------------------------------------------------------------------------
# Columns with smallest terms and structured provenance
# ---------------------------------------------------------------------------
table_of = {}          # bytes -> column id
cols = []              # dicts


def add(col, term, size, depth, struct):
    key = col.tobytes()
    if key in table_of:
        c = cols[table_of[key]]
        if size < c["size"]:
            c.update(term=term, size=size, depth=depth, provenance=struct)
        return table_of[key]
    table_of[key] = len(cols)
    cols.append({"id": len(cols), "table": tabstr(col), "term": term, "size": size,
                 "depth": depth, "provenance": struct, "_col": col})
    return table_of[key]


closed_ids = []
for a in range(len(D1)):
    term, sz = closed_arg(a)
    closed_ids.append(add(A[:, a].astype(np.uint8), f"F({term})", sz + 1, 1,
                          {"kind": "closed", "arg": list(D1[a])}))

# atoms: constants and case c of tt->u, ff->v over closed columns
atoms = [(np.full(N, v, np.uint8), V[v], 1, 0, {"kind": "const", "value": V[v]}) for v in (BOT, TT, FF)]
for cid in closed_ids:
    c = cols[cid]
    for u, v in product((BOT, TT, FF), repeat=2):
        x = m4.case(c["_col"], np.full(N, u, np.uint8), np.full(N, v, np.uint8))
        atoms.append((x, f"case {c['term']} of tt->{V[u]}, ff->{V[v]}", c["size"] + 3, 1,
                      {"kind": "case", "column": cid, "tt": V[u], "ff": V[v]}))
for x, px, sx, dx, st in atoms:
    add(m4.query(np.stack([x, x, x], axis=1)), f"F(λz.{px})", sx + 2, dx + 1,
        {"kind": "nested", "shape": "λz.a", "a": st})
for (a, pa, sa, da, sta), (b, pb, sb, db, stb) in product(atoms, repeat=2):
    add(m4.query(np.stack([np.zeros(N, np.uint8), a, b], axis=1)),
        f"F(λz.case z of tt->[{pa}], ff->[{pb}])", sa + sb + 4, max(da, db) + 1,
        {"kind": "nested", "shape": "λz.case z of tt->a, ff->b", "a": sta, "b": stb})

# cross-check against m4's column set
c0, p0 = m4.columns_closed()
n0, _ = m4.columns_nested(c0, p0, None)
assert {c.tobytes() for c in c0 + n0} == set(table_of), "column sets differ from m4"
Q = np.array([c["_col"] for c in cols], dtype=np.uint8)
json.dump([{k: v for k, v in c.items() if k != "_col"} for c in cols],
          open(os.path.join(OUT, "columns.json"), "w"), ensure_ascii=False)
print(f"columns: {len(cols)} (depth 1: {sum(c['depth'] == 1 for c in cols)}, "
      f"depth 2: {sum(c['depth'] == 2 for c in cols)})")

# ---------------------------------------------------------------------------
# Tree certificates for all survivor classes
# ---------------------------------------------------------------------------
def to_json(tr):
    if tr[0] == "leaf":
        return V[tr[1]]
    return {"column": tr[1], "tt": to_json(tr[2]), "ff": to_json(tr[3])}


def depth(tr):
    return 0 if tr[0] == "leaf" else 1 + max(depth(tr[2]), depth(tr[3]))


def used(tr, acc):
    if tr[0] != "leaf":
        acc[tr[1]] += 1
        used(tr[2], acc)
        used(tr[3], acc)


trees, depths, usage = [], [], Counter()
for c in m4.classes:
    h = np.zeros(N, dtype=np.uint8)
    for x in c["minT"]:
        h[LE[x]] = TT
    for x in c["minF"]:
        h[LE[x]] = FF
    tr = m4.tree_solves(None, Q, h=h)
    assert tr is not None
    d = depth(tr)
    depths.append(d)
    used(tr, usage)
    trees.append({"minT": c["minT"], "minF": c["minF"], "depth": d, "tree": to_json(tr)})
stats = {"classes": len(trees), "depth_min": int(min(depths)), "depth_max": int(max(depths)),
         "depth_median": float(np.median(depths)),
         "depth_histogram": dict(sorted(Counter(depths).items())),
         "columns_used": len(usage),
         "column_usage_top50": [{"column": k, "term": cols[k]["term"], "uses": n}
                                for k, n in usage.most_common(50)]}
json.dump({"stats": stats, "trees": trees}, open(os.path.join(OUT, "trees.json"), "w"), ensure_ascii=False)
print(f"trees: depth {stats['depth_min']}..{stats['depth_max']} (median {stats['depth_median']}); "
      f"{len(usage)} distinct columns used")

# ---------------------------------------------------------------------------
# The 278 pairs that need nested calls
# ---------------------------------------------------------------------------
closed_Q = Q[[c["depth"] == 1 for c in cols]]
nested_rows = []
for (p, q), U in zip(m4.pairs, m4.targets):
    if m4.tree_solves(U, closed_Q) is not None or m4.intersection_solves(U, closed_Q) is not None:
        continue
    tr = m4.tree_solves(U, Q)
    acc = Counter()
    used(tr, acc)
    nested_rows.append({"p": p, "q": q, "p_table": tabstr(A[p]), "q_table": tabstr(A[q]),
                        "tree": to_json(tr),
                        "nested_columns": [{"column": k, "term": cols[k]["term"],
                                            "provenance": cols[k]["provenance"]}
                                           for k in acc if cols[k]["depth"] == 2]})
json.dump(nested_rows, open(os.path.join(OUT, "nested_pairs.json"), "w"), ensure_ascii=False)
print(f"nested pairs: {len(nested_rows)}")
