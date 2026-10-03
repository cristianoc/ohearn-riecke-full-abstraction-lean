#!/usr/bin/env python3
"""Compare pi^*(R_tau) with (pi^*R)_tau (ARITY.md, section 2).

For tests R of arity w in {3, 4} and surjections pi : w -> k (2 <= k < w):
  P = {x in D_tau^k : x o pi in R_tau},  Q = (pi^*R)_tau,
  Q2 = {x : x o pi in (R n E_pi)_tau}   (Lemma R2 predicts Q = Q2).
Levels: B->B (11), B->B->B (163), (B->B)->B = D2 (355).
At B->B and B->B->B every k-tuple is checked.  At D2, k = 2 checks all
126,025 pairs; k = 3 checks a seeded random sample of triples.
Arity-4 tests are a seeded random sample of the 17,241 distinct intersections.

Usage: arity_reindex.py [--deadline SECONDS] [--n4 N] [--seed S] [--out PATH]
Stops at the deadline and writes partial results.
"""
import argparse
import json
import os
import random
import time
from itertools import product

import numpy as np

import arity_lib as L

S = "⊥tf"


def tab(t):
    return "".join(S[v] for v in t)


def gstr(g):
    return "".join(S[int(v)] for v in g)


def test_gens(R):
    """A generator list (A,B) whose intersection is R: all S^w_{A,B} containing R."""
    w = R.ndim
    out = []
    for a in range(1 << w):
        for b in range(1 << w):
            A = [i for i in range(w) if a >> i & 1]
            B = [i for i in range(w) if b >> i & 1]
            if set(A) <= set(B) and len(B) >= 2:
                Sg = L.elementary(w, A, B)
                if (R <= Sg).all() and not Sg.all():
                    out.append((A, B))
    # keep the inclusion-minimal generators only
    mins = [(A, B) for (A, B) in out
            if not any((A2, B2) != (A, B) and (L.elementary(w, A2, B2) <= L.elementary(w, A, B)).all()
                       for (A2, B2) in out)]
    return mins


def witness_Q_not_P(level, R, pi, x):
    """G in R_sigma with (x_{pi i} G_i)_i not in R."""
    G = level.argrel(R)
    for row in G:
        o = tuple(int(level.elems[x[pi[i]], row[i]]) for i in range(len(pi)))
        if not R[o]:
            return [int(v) for v in row], list(o)
    return None


def witness_P_not_Q(level, R, pi, k, x):
    Sk = L.pullback(R, np.array(pi), k)
    for row in level.argrel(Sk):
        o = tuple(int(level.elems[x[j], row[j]]) for j in range(k))
        if not Sk[o]:
            return [int(v) for v in row], list(o)
    return None


def run_level(level, tests, maps, X_for_k, deadline, label, describe):
    st = {"level": level.name, "tests": label, "pairs_checked": 0, "tuples_checked": 0,
          "P_subset_Q": 0, "Q_subset_P": 0, "equal": 0, "lemma_R2_holds": 0,
          "complete": True, "first_Q_not_P": None, "first_P_not_Q": None,
          "count_Q_not_P_tuples": 0, "count_P_not_Q_tuples": 0}
    for R in tests:
        for pi in maps:
            if time.time() > deadline:
                st["complete"] = False
                return st
            k = max(pi) + 1
            X = X_for_k(k)
            P, Q, Q2 = L.compare(level, R, pi, k, X=X)
            st["pairs_checked"] += 1
            st["tuples_checked"] += len(X)
            st["P_subset_Q"] += int(not (P & ~Q).any())
            st["Q_subset_P"] += int(not (Q & ~P).any())
            st["equal"] += int((P == Q).all())
            st["lemma_R2_holds"] += int((Q == Q2).all())
            st["count_Q_not_P_tuples"] += int((Q & ~P).sum())
            st["count_P_not_Q_tuples"] += int((P & ~Q).sum())
            for key, mask, wit in (("first_Q_not_P", Q & ~P, witness_Q_not_P),
                                   ("first_P_not_Q", P & ~Q, None)):
                if st[key] is None and mask.any():
                    x = [int(v) for v in X[np.argmax(mask)]]
                    if wit is not None:
                        G, o = wit(level, R, pi, x)
                    else:
                        G, o = witness_P_not_Q(level, R, pi, k, x)
                    st[key] = {"R_generators": test_gens(R), "R_size": int(R.sum()),
                               "pi": list(pi), "x": describe(x), "x_index": x,
                               "violating_argument": G, "output": gstr(o)}
    return st


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--deadline", type=float, default=540)
    ap.add_argument("--n4", type=int, default=40)
    ap.add_argument("--n4_d2", type=int, default=12)
    ap.add_argument("--k3_samples", type=int, default=20000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--parts", default="0,1,2,3,4,5,6", help="indices into the plan")
    ap.add_argument("--out", default=os.path.join(L.HERE, "data", "arity_reindex.json"))
    a = ap.parse_args()
    t0 = time.time()
    deadline = t0 + a.deadline
    rng = random.Random(a.seed)

    D1, D1tabs = L.level_D1()
    BBB = L.level_BBB()
    D2 = L.level_D2(D1)
    t3 = [L.from_mask(m, 3) for m in L.all_tests(3)]
    m4 = L.all_tests(4)
    t4 = [L.from_mask(m, 4) for m in rng.sample(m4, a.n4)]
    t4_d2 = t4[:a.n4_d2]
    s32 = L.surjections(3, 2)
    s42 = L.surjections(4, 2)
    s43 = L.surjections(4, 3)

    def desc_D1(x):
        return [tab(D1tabs[i]) for i in x]

    def desc_BBB(x):
        return [tab(BBB.elems[i]) for i in x]

    def desc_D2(x):
        return [tab(D2.elems[i]) for i in x]

    nprng = np.random.default_rng(a.seed)

    def full(level):
        return lambda k: L.all_tuples(len(level.elems), k)

    def d2_tuples(k):
        if k == 2:
            return L.all_tuples(len(D2.elems), 2)
        return nprng.integers(0, len(D2.elems), size=(a.k3_samples, k))

    results = {"seed": a.seed, "n_arity3_tests": len(t3), "n_arity4_tests_total": len(m4),
               "n_arity4_sampled": a.n4, "n_arity4_sampled_D2": a.n4_d2,
               "D1_order": [tab(t) for t in D1tabs], "runs": []}
    plan = [
        (D1, t3, s32, full(D1), "all arity-3, pi:3->2", desc_D1),
        (BBB, t3, s32, full(BBB), "all arity-3, pi:3->2", desc_BBB),
        (D1, t4, s42 + s43, full(D1), "sampled arity-4, pi:4->2,3", desc_D1),
        (D2, t3, s32, d2_tuples, "all arity-3, pi:3->2, all pairs", desc_D2),
        (D2, t4_d2, s42, d2_tuples, "sampled arity-4, pi:4->2, all pairs", desc_D2),
        (D2, t4_d2, s43, d2_tuples, "sampled arity-4, pi:4->3, sampled triples", desc_D2),
        (BBB, t4[:10], s42, full(BBB), "sampled arity-4, pi:4->2", desc_BBB),
    ]
    parts = [int(i) for i in a.parts.split(",")]
    results["parts"] = parts
    for level, tests, maps, Xk, label, desc in [plan[i] for i in parts]:
        st = run_level(level, tests, maps, Xk, deadline, label, desc)
        st["elapsed_s"] = round(time.time() - t0, 1)
        results["runs"].append(st)
        print(json.dumps({k: v for k, v in st.items() if not k.startswith("first")}), flush=True)
        with open(a.out, "w") as f:
            json.dump(results, f, indent=1, ensure_ascii=False)
        if time.time() > deadline:
            break
    print("wrote", a.out)


if __name__ == "__main__":
    main()
