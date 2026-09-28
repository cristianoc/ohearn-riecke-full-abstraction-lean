#!/usr/bin/env python3
"""Milestone M2 of GPU_SEARCH.md: batched falsification of symbolic candidates.

Pipeline for h : D2 -> B at tau0 = ((B -> B) -> B) -> B:
  1. generate candidates in the symbolic language of section 7, evaluate each to
     its 355-byte table, keep one provenance string per distinct table;
  2. drop non-monotone tables (CPU);
  3. learned bank: CPU-check every verified witness triple found so far;
  4. GPU: batched, output-bucketed arity-3 falsification of the rest, tests in
     learned order (most frequent killers first);
  5. add new witnesses to the bank, update the order, repeat.
Every GPU witness is re-verified on the CPU; verdicts on a sample are checked
against the M1 kernel.
"""
import json, os, random, sys, time
from itertools import combinations, product

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sieber_cpu as C
import sieber_metal as G

rng = random.Random(20260928)
TARGET = int(sys.argv[1]) if len(sys.argv) > 1 else 100_000

# ---------------------------------------------------------------------------
# Setup (as in M1)
# ---------------------------------------------------------------------------
tests = C.arity3_tests()
D1 = C.carrier_D1()
D2 = sorted(C.definable_D2(D1))
A = np.array(D2, dtype=np.uint8)
N = len(D2)
rel1 = [C.lift_ground_to_D1(R, D1) for R in tests]
Rarr = np.array([[(R >> x) & 1 for x in range(27)] for R in tests], dtype=bool)   # (ntests, 27)

# order each test's rel1 entries by how often they reject random related-looking triples
sample = np.array([[rng.randrange(N) for _ in range(3)] for _ in range(20000)])
for t, r1 in enumerate(rel1):
    if not r1:
        continue
    e = np.array(r1)
    vals = 9 * A[sample[:, 0]][:, e[:, 0]] + 3 * A[sample[:, 1]][:, e[:, 1]] + A[sample[:, 2]][:, e[:, 2]]
    fails = (~Rarr[t][vals]).sum(axis=0)
    rel1[t] = [r1[x] for x in np.argsort(-fails, kind="stable")]
L2 = G.Level(D2, tests, rel1)

LE = (A[:, None, :] == 0) | (A[:, None, :] == A[None, :, :])
LE = LE.all(axis=2)                                        # LE[i, j]: D2[i] <= D2[j]
hasse = [(i, j) for i in range(N) for j in range(N)
         if i != j and LE[i, j] and not (LE[i] & LE[:, j]).sum() > 2]
E0 = np.array([e[0] for e in hasse]); E1 = np.array([e[1] for e in hasse])


def monotone(H):
    """H: (b, N).  Boolean per row."""
    lo, hi = H[:, E0], H[:, E1]
    return ((lo == 0) | (lo == hi)).all(axis=1)


# ---------------------------------------------------------------------------
# Candidate language (section 7), hash-consed by semantic table
# ---------------------------------------------------------------------------
table = {}          # bytes -> provenance


def add(h, prov):
    h = np.asarray(h, dtype=np.uint8)
    key = h.tobytes()
    if key not in table:
        table[key] = prov
    return h


def ite(c, t, e):
    return np.where(c == 0, 0, np.where(c == 1, t, e)).astype(np.uint8)


def generate(target):
    base = []
    for v, name in ((0, "BOT"), (1, "TT"), (2, "FF")):
        base.append((add(np.full(N, v), name), name))
    for a in range(len(D1)):
        base.append((add(A[:, a], f"eval({a})"), f"eval({a})"))
    unary = []
    for h, p in base[3:]:
        unary.append((add(np.where(h == 1, 1, 0), f"is_tt({p})"), f"is_tt({p})"))
        unary.append((add(np.where(h == 2, 1, 0), f"is_ff({p})"), f"is_ff({p})"))
        unary.append((add(np.where(h != 0, 1, 0), f"defined({p})"), f"defined({p})"))
        unary.append((add(np.where(h == 0, 0, 3 - h), f"not({p})"), f"not({p})"))
    pool = base + unary
    for (x, px), (y, py) in combinations(pool[3:], 2):
        add(np.where((x == 1) & (y == 1), 1, 0), f"semi_and({px},{py})")
        add(np.where((x == 1) | (y == 1), 1, 0), f"semi_or({px},{py})")
    evals = base[3:]
    for (c, pc), (t, pt), (e, pe) in product(evals, repeat=3):
        add(ite(c, t, e), f"if({pc},{pt},{pe})")
    for p in range(N):
        for v, name in ((1, "tt"), (2, "ff")):
            add(np.where(LE[p], v, 0), f"principal({p},{name})")
    pairs = list(combinations(range(N), 2))
    rng.shuffle(pairs)
    for p, q in pairs:
        if len(table) >= target:
            break
        add(np.where(LE[p] | LE[q], 1, 0), f"union({p},{q})")
        if not (LE[p] & LE[q]).any():
            add(np.where(LE[p], 1, np.where(LE[q], 2, 0)), f"race({p},{q})")
    while len(table) < target:
        ps = rng.sample(range(N), rng.randrange(3, 6))
        up = np.zeros(N, dtype=bool)
        for p in ps:
            up |= LE[p]
        add(np.where(up, 1, 0), f"union{tuple(ps)}")


t0 = time.perf_counter()
generate(TARGET)
keys = list(table)
H_all = np.frombuffer(b"".join(keys), dtype=np.uint8).reshape(-1, N)
mono = monotone(H_all)
H = H_all[mono]
provs = [table[k] for k, m in zip(keys, mono) if m]
t_gen = time.perf_counter() - t0
print(f"generated {len(keys)} distinct tables in {t_gen:.1f}s; {len(H)} monotone")

# ---------------------------------------------------------------------------
# CEGAR loop
# ---------------------------------------------------------------------------
bank = []                                   # verified (i, j, k, t)
order = list(range(len(tests)))
kills = np.zeros(len(tests), dtype=np.int64)
verdict = [None] * len(H)                   # None = unknown, else witness or "alive"
t_bank = t_gpu = 0.0
BATCH = 4096
for start in range(0, len(H), BATCH):
    idx = np.arange(start, min(start + BATCH, len(H)))
    # 3. learned bank on CPU
    s = time.perf_counter()
    if bank:
        B = np.array(bank)
        out = 9 * H[idx][:, B[:, 0]] + 3 * H[idx][:, B[:, 1]] + H[idx][:, B[:, 2]]   # (b, nbank)
        dead = ~Rarr[B[:, 3][None, :], out]
        hit = dead.any(axis=1)
        for r in np.nonzero(hit)[0]:
            w = bank[int(np.argmax(dead[r]))]
            verdict[idx[r]] = w
        idx = idx[~hit]
    t_bank += time.perf_counter() - s
    # 4. GPU on the rest
    s = time.perf_counter()
    res = G.batch_falsify(L2, H[idx], order) if len(idx) else []
    t_gpu += time.perf_counter() - s
    for c, w in zip(idx, res):
        if w is None:
            verdict[c] = "alive"
        else:
            verdict[c] = w
            i, j, k, t = w
            assert C.related_level_tuple(tests[t], D2, rel1[t], (i, j, k)), "unrelated witness"
            assert not C.ground_member(tests[t], (H[c][i], H[c][j], H[c][k])), "witness not violating"
            if w not in bank:
                bank.append(w)
            kills[t] += 1
    order = list(np.argsort(-kills, kind="stable"))

alive = [c for c, v in enumerate(verdict) if v == "alive"]
print(f"bank {len(bank)} witnesses; CPU bank {t_bank:.1f}s, GPU {t_gpu:.1f}s; "
      f"{len(H) / (t_bank + t_gpu):.0f} candidates/s; {len(alive)} survive all arity-3 tests")

# ---------------------------------------------------------------------------
# Validation against M1 on a sample
# ---------------------------------------------------------------------------
sample = rng.sample(range(len(H)), min(300, len(H)))
sample += rng.sample(alive, min(50, len(alive)))
for c in sample:
    m1 = L2.falsify(H[c])
    assert (verdict[c] == "alive") == all(w is None for w in m1), f"M1/M2 disagree on {provs[c]}"
print(f"[PASS] M2 verdicts agree with M1 on {len(sample)} candidates; all witnesses CPU-verified")

kinds = {}
for c in alive:
    k = provs[c].split("(")[0]
    kinds[k] = kinds.get(k, 0) + 1
print("survivors by constructor:", json.dumps(kinds))
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".validation", "m2_survivors.json")
json.dump({"survivors": [[provs[c], H[c].tolist()] for c in alive],
           "bank": [list(map(int, w)) for w in bank]}, open(out, "w"))
