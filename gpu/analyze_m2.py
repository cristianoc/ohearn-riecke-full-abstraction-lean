#!/usr/bin/env python3
"""Post-M2 analysis: certificates and canonical forms (no GPU needed).

  * width certificate: an explicit 80-element antichain of D2, checked pairwise;
  * survivors: canonical forms under the symmetry group, represented by the
    minimal antichains of T_h = h^-1(tt) and F_h = h^-1(ff), ranked by size;
  * witness bank: orbit classes of the certificates (i, j, k, test) under the
    symmetry group and permutations of the three coordinates.

Symmetry group: tau = ((B1 -> B2) -> B3) -> B4 has 16 automorphisms swapping
tt/ff independently at each Bi.  Negation is definable and every test is
invariant under a simultaneous swap of all coordinates, so definability and
test preservation are both invariant.

Reads .validation/m2_survivors.json (written by m2.py), writes gpu/data/.
"""
import json, os, sys
from itertools import permutations, product

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sieber_cpu as C

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
os.makedirs(DATA, exist_ok=True)

tests = C.arity3_tests()
D1 = C.carrier_D1()
D2 = sorted(C.definable_D2(D1))
A = np.array(D2, dtype=np.uint8)
N = len(D2)
LE = ((A[:, None, :] == 0) | (A[:, None, :] == A[None, :, :])).all(axis=2)
SW = np.array([0, 2, 1], dtype=np.uint8)          # swap tt/ff
ID = np.array([0, 1, 2], dtype=np.uint8)

# ---------------------------------------------------------------------------
# Width certificate (Dilworth / Koenig)
# ---------------------------------------------------------------------------
LT = LE & ~np.eye(N, dtype=bool)
adj = [list(np.nonzero(LT[i])[0]) for i in range(N)]
match_r = [-1] * N                                  # right vertex -> left vertex
sys.setrecursionlimit(10000)


def augment(u, seen):
    for v in adj[u]:
        if v not in seen:
            seen.add(v)
            if match_r[v] == -1 or augment(match_r[v], seen):
                match_r[v] = u
                return True
    return False


msize = sum(augment(u, set()) for u in range(N))
match_l = [-1] * N
for v, u in enumerate(match_r):
    if u != -1:
        match_l[u] = v
# Koenig: Z = vertices reachable from unmatched left vertices by alternating paths
ZL, ZR = set(), set()
stack = [u for u in range(N) if match_l[u] == -1]
ZL.update(stack)
while stack:
    u = stack.pop()
    for v in adj[u]:
        if v not in ZR:
            ZR.add(v)
            w = match_r[v]
            if w != -1 and w not in ZL:
                ZL.add(w)
                stack.append(w)
cover_l = set(range(N)) - ZL
cover_r = ZR
antichain = [x for x in range(N) if x not in cover_l and x not in cover_r]
assert len(antichain) == N - msize
assert all(not LE[a, b] for a in antichain for b in antichain if a != b)
json.dump({"D2_size": N, "width": len(antichain), "antichain": antichain,
           "antichain_tables": [list(D2[a]) for a in antichain]},
          open(os.path.join(DATA, "width_certificate.json"), "w"))
print(f"width certificate: explicit antichain of size {len(antichain)} (pairwise incomparable, checked)")

# ---------------------------------------------------------------------------
# Symmetry group action on D1, D2 and on candidates h : D2 -> B
# ---------------------------------------------------------------------------
D1_index = {f: i for i, f in enumerate(D1)}
D2_index = {tuple(F): i for i, F in enumerate(D2)}


def act_D1(s1, s2):
    """Permutation of D1 indices for f |-> s2 . f . s1."""
    return [D1_index[tuple(int(s2[f[int(s1[x])]]) for x in range(3))] for f in D1]


def act_D2(s1, s2, s3):
    """Permutation of D2 indices for F |-> s3 . F . (action on D1)."""
    p1 = act_D1(s1, s2)            # an involution, so it is its own inverse
    return [D2_index[tuple(int(s3[F[p1[a]]]) for a in range(len(D1)))] for F in D2]


GROUP = []
for s in product((ID, SW), repeat=4):
    GROUP.append((np.array(act_D2(*s[:3])), s[3]))


def canon(h):
    """Lexicographically least table in the orbit of h."""
    best = None
    for perm, s4 in GROUP:
        g = s4[h[perm]]
        b = g.tobytes()
        if best is None or b < best:
            best = b
    return best


def minimal(mask):
    idx = np.nonzero(mask)[0]
    return [int(x) for x in idx if not (LE[idx, x] & (idx != x)).any()]


# ---------------------------------------------------------------------------
# Survivors
# ---------------------------------------------------------------------------
m2 = json.load(open(os.path.join(HERE, "..", ".validation", "m2_survivors.json")))
surv = m2["survivors"]
classes = {}
for prov, h in surv:
    h = np.array(h, dtype=np.uint8)
    key = canon(h)
    if key not in classes:
        g = np.frombuffer(key, dtype=np.uint8)
        classes[key] = {"example": prov, "count": 0,
                        "minT": minimal(g == 1), "minF": minimal(g == 2)}
    classes[key]["count"] += 1
rows = sorted(classes.values(), key=lambda r: (len(r["minT"]) + len(r["minF"]), -r["count"]))
json.dump(rows, open(os.path.join(DATA, "m2_survivor_classes.json"), "w"))
sizes = {}
for r in rows:
    k = len(r["minT"]) + len(r["minF"])
    sizes[k] = sizes.get(k, 0) + 1
print(f"survivors: {len(surv)} tables -> {len(classes)} symmetry classes")
print("classes by |min T_h| + |min F_h|:", dict(sorted(sizes.items())))

# ---------------------------------------------------------------------------
# Witness bank: obstruction orbits
# ---------------------------------------------------------------------------
def permute_mask(R, pi):
    out = 0
    for x, y, z in product(range(3), repeat=3):
        v = (x, y, z)
        if R >> (9 * v[pi[0]] + 3 * v[pi[1]] + v[pi[2]]) & 1:
            out |= 1 << (9 * x + 3 * y + z)
    return out


bank = m2["bank"]
schemas = {}
for i, j, k, t in bank:
    best = None
    for perm, _ in GROUP:
        trip = (int(perm[i]), int(perm[j]), int(perm[k]))
        for pi in permutations(range(3)):
            key = (tuple(trip[p] for p in pi), permute_mask(tests[t], pi))
            if best is None or key < best:
                best = key
    schemas.setdefault(best, 0)
    schemas[best] += 1
by_test = {}
for (trip, R), n in schemas.items():
    by_test.setdefault(R, [0, 0])
    by_test[R][0] += 1
    by_test[R][1] += n
json.dump([{"triple": list(k[0]), "test_mask": k[1], "count": n} for k, n in
           sorted(schemas.items(), key=lambda kv: -kv[1])],
          open(os.path.join(DATA, "m2_bank_orbits.json"), "w"))
json.dump(bank, open(os.path.join(DATA, "m2_bank.json"), "w"))
print(f"bank: {len(bank)} certificates -> {len(schemas)} orbits of (triple, test); "
      f"{len(by_test)} distinct tests (up to coordinate permutation) involved")
for R, (orbits, n) in sorted(by_test.items(), key=lambda kv: -kv[1][1])[:10]:
    print(f"  test {R:#09x}: {orbits} orbits, {n} certificates")
