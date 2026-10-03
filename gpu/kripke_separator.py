#!/usr/bin/env python3
"""Kripke-vs-ordinary separator search at tau0.

For each small Kripke relation K (search_kripke_two_world: worlds w of arity 2
and w+ of arity 3, maps p : w+ -> w, sequentiality relations R(w), R(w+)),
compute the pairs E that K relates at D2 (world w) but the ordinary lift of R(w)
does not.  Only those pairs can separate: an h preserving the ordinary test R(w)
maps every ordinarily related pair into R(w).  If E contributes a forbidden
output pattern, ask z3 for a monotone h : D2 -> B that
  * preserves all arity-3 ordinary tests (lazily, GPU oracle from M1), and
  * violates K on some pair of E.
Such an h is not definable (definable elements preserve every Kripke relation).
Each hit is then checked against arity-4 ordinary tests (arity4_h3.py).

Every case is recorded in gpu/data/kripke_separator_all.json: the indices of
R(w) (among search_kripke_two_world.tests2()) and R(w+) (among the non-full
arity-3 tests), the map set P, the sizes of K_D1(w) and of the ordinary lift
R^ord_D1(w), the sizes of K_D2(w) and R^ord_D2(w), |E| = |K_D2(w) - R^ord_D2(w)|,
|R^ord_D2(w) - K_D2(w)| (the reverse inclusion holds iff it is 0), and whether
a candidate was searched (only when E is non-empty).  The cases with E
non-empty are also written to gpu/data/kripke_separator.json; that file is left
as it is when there are none.
"""
import json, os, sys, time
from itertools import product

import numpy as np
import z3

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sieber_cpu as C
import search_kripke_two_world as K

HERE = os.path.dirname(os.path.abspath(__file__))
BOT, TT, FF = C.BOT, C.TT, C.FF
A, N, D1 = K.A, K.N, K.D1                       # D2 as sorted definable tables (= m4.A)
B1A = np.array(D1, dtype=np.uint8)
LE = ((A[:, None, :] == BOT) | (A[:, None, :] == A[None, :, :])).all(axis=2)
hasse = [(i, j) for i in range(N) for j in range(N)
         if i != j and LE[i, j] and (LE[i] & LE[:, j]).sum() == 2]
_L2 = None


def arity3_level():
    """GPU arity-3 falsifier (M1), built on first use: only separate() needs it."""
    global _L2
    if _L2 is None:
        import sieber_metal as G
        tests = C.arity3_tests()
        _L2 = G.Level([tuple(r) for r in A.tolist()], tests,
                      [C.lift_ground_to_D1(R, D1) for R in tests])
    return _L2


def cases():
    """The relations of search_kripke_two_world.relations(), in the same order and
    with the same compatibility filter and soundness assertion, with parameters
    and the D1-level relations exposed."""
    T2 = K.tests2()
    T3 = [K.ground3(R) for R in C.arity3_tests() if R != (1 << 27) - 1]
    maps = list(product(range(2), repeat=3))
    map_sets = [[(0, 0, 0)], [(0, 0, 1)], [p for p in maps if len(set(p)) == 2]]
    lift_cache = {}
    for i, Rw in enumerate(T2):
        gw = np.argwhere(Rw)
        for j, Rwp in enumerate(T3):
            for P in map_sets:
                if not all(Rwp[tuple(g[p[k]] for k in range(3))] for p in P for g in gw):
                    continue
                if j not in lift_cache:
                    lift_cache[j] = K.lift_D1_ordinary(Rwp)
                D1w = K.lift_D1_at_w(Rw, Rwp, P)
                rel = K.lift_D2_at_w(Rw, Rwp, P, D1w, lift_cache[j])
                assert rel.diagonal().all(), "a definable element of D2 fell outside R_D2(w)"
                yield {"i": i, "j": j, "P": P, "Rw": Rw, "D1w": D1w, "relD2": rel,
                       "desc": f"R(w)=arity-2 test {i}, R(w+)=arity-3 test {j}, P={P}"}


def ordinary_lift1(Rw):
    """Ordinary lift of an arity-2 relation to D1 pairs."""
    gt = np.argwhere(Rw)
    return [(a, b) for a in range(len(D1)) for b in range(len(D1))
            if all(Rw[B1A[a, x], B1A[b, y]] for x, y in gt)]


def ordinary_lift2(Rw):
    """Ordinary lift of an arity-2 relation to D2 pairs."""
    rel_d1 = ordinary_lift1(Rw)
    rel = np.ones((N, N), dtype=bool)
    for a, b in rel_d1:
        rel &= Rw[A[:, a][:, None], A[:, b][None, :]]
    return rel


def separate(Rw, E):
    """z3: monotone h preserving arity-3 tests and violating (Rw) on a pair of E."""
    s = z3.SolverFor("QF_FD")
    t = [z3.Bool(f"t{x}") for x in range(N)]
    f = [z3.Bool(f"f{x}") for x in range(N)]
    for x in range(N):
        s.add(z3.Not(z3.And(t[x], f[x])))
    for i, j in hasse:
        s.add(z3.Implies(t[i], t[j]), z3.Implies(f[i], f[j]))

    def is_(x, u):
        return z3.And(z3.Not(t[x]), z3.Not(f[x])) if u == BOT else (t[x] if u == TT else f[x])

    def neq(x, u):
        return z3.Not(t[x]) if u == TT else z3.Not(f[x]) if u == FF else z3.Or(t[x], f[x])

    bad = [(u, v) for u, v in product(range(3), repeat=2) if not Rw[u, v]]
    s.add(z3.Or([z3.And(is_(int(a), u), is_(int(b), v)) for a, b in E for u, v in bad]))
    rounds = 0
    while True:
        rounds += 1
        if s.check() != z3.sat:
            return None, rounds
        m = s.model()
        h = np.array([TT if z3.is_true(m.eval(t[x], True)) else FF if z3.is_true(m.eval(f[x], True))
                      else BOT for x in range(N)], dtype=np.uint8)
        viol = [w for w in arity3_level().falsify(h) if w is not None]
        if not viol:
            return h, rounds
        for i, j, k in viol:
            s.add(z3.Or(neq(i, int(h[i])), neq(j, int(h[j])), neq(k, int(h[k]))))


if __name__ == "__main__":
    t0 = time.perf_counter()
    ord_cache, rows, results = {}, [], []
    for case in cases():
        Rw, relD2 = case["Rw"], case["relD2"]
        key = Rw.tobytes()
        if key not in ord_cache:
            ord_cache[key] = (ordinary_lift1(Rw), ordinary_lift2(Rw))
        ord1, ord2 = ord_cache[key]
        E = np.argwhere(relD2 & ~ord2)
        reverse_missing = int((ord2 & ~relD2).sum())
        row = {"id": len(rows), "kripke": case["desc"], "Rw_index": case["i"], "Rwp_index": case["j"],
               "P": [list(p) for p in case["P"]],
               "K_D1": len(case["D1w"]), "Rord_D1": len(ord1),
               "K_D1_subset_Rord_D1": set(case["D1w"]) <= set(ord1),
               "K_D2": int(relD2.sum()), "Rord_D2": int(ord2.sum()),
               "E": int(len(E)), "Rord_minus_K_D2": reverse_missing,
               "searched": bool(len(E))}
        # only pairs whose values can leave R(w) matter; monotone h can take any values
        if len(E):
            h, rounds = separate(Rw, E)
            row.update({"separated": h is not None, "rounds": rounds})
            if h is not None:
                path = os.path.join(HERE, "data", f"kripke_sep_{len(results)}.npy")
                np.save(path, h)
                row["candidate"] = os.path.basename(path)
                row["support"] = int((h != BOT).sum())
            results.append({k: row[k] for k in ("kripke", "E", "separated", "rounds")
                            if k in row} | {k: row[k] for k in ("candidate", "support") if k in row})
            print(f"{case['desc']}: |E|={len(E)} separated={h is not None} (rounds {rounds}, "
                  f"{time.perf_counter() - t0:.0f}s)", flush=True)
        rows.append(row)
    n = len(rows)
    print(f"{n} Kripke relations, {len(results)} with E non-empty, "
          f"{sum(r['separated'] for r in results)} separations; "
          f"K_D2 subset of Rord_D2 in {sum(r['E'] == 0 for r in rows)}, "
          f"Rord_D2 subset of K_D2 in {sum(r['Rord_minus_K_D2'] == 0 for r in rows)}, "
          f"K_D1 subset of Rord_D1 in {sum(r['K_D1_subset_Rord_D1'] for r in rows)} "
          f"({time.perf_counter() - t0:.0f}s)")
    json.dump(rows, open(os.path.join(HERE, "data", "kripke_separator_all.json"), "w"), indent=1)
    if results:
        json.dump(results, open(os.path.join(HERE, "data", "kripke_separator.json"), "w"), indent=1)
