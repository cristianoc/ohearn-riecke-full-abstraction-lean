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
Results: gpu/data/kripke_separator.json.
"""
import json, os, sys, time
from itertools import product

import numpy as np
import z3

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sieber_cpu as C
import sieber_metal as G
import m4
import search_kripke_two_world as K

A, N, LE, BOT, TT, FF = m4.A, m4.N, m4.LE, m4.BOT, m4.TT, m4.FF
D1 = m4.D1
B1A = np.array(D1, dtype=np.uint8)

tests = C.arity3_tests()
rel1 = [C.lift_ground_to_D1(R, D1) for R in tests]
L2 = G.Level([tuple(r) for r in A.tolist()], tests, rel1)
hasse = [(i, j) for i in range(N) for j in range(N)
         if i != j and LE[i, j] and (LE[i] & LE[:, j]).sum() == 2]


def ordinary_lift2(Rw):
    """Ordinary lift of an arity-2 relation to D2 pairs."""
    gt = np.argwhere(Rw)
    rel_d1 = [(a, b) for a in range(len(D1)) for b in range(len(D1))
              if all(Rw[B1A[a, x], B1A[b, y]] for x, y in gt)]
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
        viol = [w for w in L2.falsify(h) if w is not None]
        if not viol:
            return h, rounds
        for i, j, k in viol:
            s.add(z3.Or(neq(i, int(h[i])), neq(j, int(h[j])), neq(k, int(h[k]))))


if __name__ == "__main__":
    t0 = time.perf_counter()
    ord_cache, results, n, useful = {}, [], 0, 0
    for desc, Rw, relD2 in K.relations():
        n += 1
        key = Rw.tobytes()
        if key not in ord_cache:
            ord_cache[key] = ordinary_lift2(Rw)
        E = np.argwhere(relD2 & ~ord_cache[key])
        # only pairs whose values can leave R(w) matter; monotone h can take any values
        if len(E) == 0:
            continue
        useful += 1
        h, rounds = separate(Rw, E)
        row = {"kripke": desc, "extra_pairs": int(len(E)), "separated": h is not None, "rounds": rounds}
        if h is not None:
            path = os.path.join(m4.HERE, "data", f"kripke_sep_{len(results)}.npy")
            np.save(path, h)
            row["candidate"] = os.path.basename(path)
            row["support"] = int((h != BOT).sum())
        results.append(row)
        print(f"{desc}: |E|={len(E)} separated={h is not None} (rounds {rounds}, "
              f"{time.perf_counter() - t0:.0f}s)", flush=True)
    print(f"{n} Kripke relations, {useful} with extra pairs, "
          f"{sum(r['separated'] for r in results)} separations ({time.perf_counter() - t0:.0f}s)")
    json.dump(results, open(os.path.join(m4.HERE, "data", "kripke_separator.json"), "w"), indent=1)
