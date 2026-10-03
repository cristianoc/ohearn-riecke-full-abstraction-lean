#!/usr/bin/env python3
"""Search for P not subset of Q at D2 = D_{(B->B)->B} (ARITY.md, section 2.4).

By Lemma R3(b), P_{D2} subset Q_{D2} holds for a pair (R, pi) whenever
Q_{B->B} subset P_{B->B} for that pair.  So only pairs with a nonempty
Q_{B->B} minus P_{B->B} can give P_{D2} not subset Q_{D2}; this script draws
arity-4 tests at random (seeded), keeps such pairs, and checks every D2 pair
(k = 2) or a random D2 triple sample (k = 3) for x in P minus Q.

Usage: arity_focus.py [--deadline S] [--seed N] [--k3_samples M] [--out PATH]
Stops at the deadline and writes partial results.
"""
import argparse
import json
import os
import random
import time

import numpy as np

import arity_lib as L


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--deadline", type=float, default=50)
    ap.add_argument("--seed", type=int, default=2)
    ap.add_argument("--k3_samples", type=int, default=20000)
    ap.add_argument("--out", default=os.path.join(L.HERE, "data", "arity_focus.json"))
    a = ap.parse_args()
    t0 = time.time()
    rng = random.Random(a.seed)
    nprng = np.random.default_rng(a.seed)
    D1, _ = L.level_D1()
    D2 = L.level_D2(D1)
    masks = L.all_tests(4)
    maps = L.surjections(4, 2) + L.surjections(4, 3)
    out = {"seed": a.seed, "tests_drawn": 0, "pairs_examined": 0, "pairs_with_QnotP_at_B->B": 0,
           "D2_checked_k2_all_pairs": 0, "D2_checked_k3_sampled": 0, "k3_samples": a.k3_samples,
           "P_not_subset_Q_at_D2": [], "complete": False}
    X2 = L.all_tuples(len(D2.elems), 2)
    while time.time() - t0 < a.deadline:
        R = L.from_mask(rng.choice(masks), 4)
        out["tests_drawn"] += 1
        for pi in maps:
            if time.time() - t0 > a.deadline:
                break
            k = max(pi) + 1
            out["pairs_examined"] += 1
            P1, Q1, _ = L.compare(D1, R, pi, k, check_R2=False)
            if not (Q1 & ~P1).any():
                continue
            out["pairs_with_QnotP_at_B->B"] += 1
            X = X2 if k == 2 else nprng.integers(0, len(D2.elems), size=(a.k3_samples, 3))
            pia = np.array(pi)
            P = L.related(D2.elems, D2.argrel(R), R, X[:, pia])
            S = L.pullback(R, pia, k)
            Q = np.zeros(len(X), dtype=bool)
            Q[P] = L.related(D2.elems, D2.argrel(S), S, X[P])
            out["D2_checked_k2_all_pairs" if k == 2 else "D2_checked_k3_sampled"] += 1
            if (P & ~Q).any():
                x = X[np.argmax(P & ~Q)]
                out["P_not_subset_Q_at_D2"].append({"R_mask": hex(int(sum(int(b) << i for i, b in enumerate(R.ravel())))),
                                                     "pi": list(pi), "x_index": [int(v) for v in x]})
    out["elapsed_s"] = round(time.time() - t0, 1)
    with open(a.out, "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out))


if __name__ == "__main__":
    main()
