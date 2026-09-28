#!/usr/bin/env python3
"""Milestone M1 of GPU_SEARCH.md: arity-3 falsifier, gates A-C, benchmark."""
import json, os, platform, random, subprocess, sys, time
from itertools import product

import mlx.core as mx
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sieber_cpu as C
import sieber_metal as G

rng = random.Random(20260928)
report = {}


def gate(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name} {detail}", flush=True)
    if not ok:
        sys.exit(1)


# ---------------------------------------------------------------------------
# Setup: tests and carriers
# ---------------------------------------------------------------------------
t0 = time.perf_counter()
tests = C.arity3_tests()
D0 = list(C.V)
D1 = C.carrier_D1()
print(f"{len(tests)} distinct arity-3 tests (full relation included)")

# level 1: elements of D1 are tables over D0; previous "lifted" relation is R itself
rel0 = [[g for g in product(C.V, repeat=3) if C.ground_member(R, g)] for R in tests]
L1 = G.Level(D1, tests, rel0)

# ---------------------------------------------------------------------------
# Gate A: carriers 3 / 11 / 355
# ---------------------------------------------------------------------------
mono = C.monotone_over(D1)
survivors = [h for h in mono if all(w is None for w in L1.falsify(h))]
definable = C.definable_D2(D1)
report["carriers"] = [len(D0), len(D1), len(survivors)]
gate("A carriers", (len(D0), len(D1), len(survivors)) == (3, 11, 355),
     f"3 / 11 / {len(survivors)} (monotone candidates {len(mono)})")
gate("A carrier == definable set", set(survivors) == definable, f"({len(definable)} definable)")
D2 = sorted(survivors)

# level 2: elements of D2 are tables over D1; rel1 = R lifted to D1
t = time.perf_counter()
rel1 = [C.lift_ground_to_D1(R, D1) for R in tests]
print(f"rel1 computed in {time.perf_counter() - t:.1f}s; sizes {min(map(len, rel1))}..{max(map(len, rel1))}")
L2 = G.Level(D2, tests, rel1)
report["compile_seconds"] = G.COMPILE_SECONDS

# spot-check rel1 against the definition-level oracle
for _ in range(200):
    R = rng.choice(tests)
    idx = tuple(rng.randrange(len(D2)) for _ in range(3))
    assert C.related_D2_tuple(R, D1, D2, idx) == C.related_level_tuple(
        R, D2, C.lift_ground_to_D1(R, D1), idx)
gate("A rel1 matches definition-level oracle", True, "(200 random tuples)")

# ---------------------------------------------------------------------------
# Gate B: differential CPU/GPU on restricted grids
# ---------------------------------------------------------------------------
def random_candidate(kind):
    if kind == "uniform":
        return [rng.choice(C.V) for _ in range(len(D2))]
    if kind == "sparse":
        h = [C.BOT] * len(D2)
        for _ in range(rng.randrange(1, 8)):
            h[rng.randrange(len(D2))] = rng.choice((C.TT, C.FF))
        return h
    # definable: F |-> F(phi), or if F(phi1) then F(phi2) else F(phi3)
    p = [rng.randrange(len(D1)) for _ in range(3)]
    if kind == "query":
        return [F[p[0]] for F in D2]
    return [C.BOT if F[p[0]] == C.BOT else F[p[1]] if F[p[0]] == C.TT else F[p[2]] for F in D2]


def differential(level, T, rels, h, I, J, K):
    gpu = level.falsify(h, I, J, K)
    for t, R in enumerate(tests):
        cpu = C.candidate_witnesses(R, T, rels[t], h, I, J, K)
        if gpu[t] is None:
            if cpu:
                return False, f"GPU found none, CPU found {cpu[0]} for test {t}"
        else:
            if gpu[t] not in cpu:
                return False, f"GPU witness {gpu[t]} for test {t} not confirmed by CPU"
            if not (gpu[t][0] in I and gpu[t][1] in J and gpu[t][2] in K):
                return False, "GPU witness outside the grid"
    return True, ""


cases = 0
with_witness = without = 0
t = time.perf_counter()
for n in range(1500):
    kind = ["uniform", "sparse", "query", "cond"][n % 4]
    h = random_candidate(kind)
    size = rng.randrange(1, 7)
    I, J, K = (rng.sample(range(len(D2)), size) for _ in range(3))
    ok, why = differential(L2, D2, rel1, h, I, J, K)
    if not ok:
        gate("B differential (level 2)", False, why)
    found = any(w is not None for w in L2.falsify(h, I, J, K))
    with_witness += found
    without += not found
    cases += 1
for n in range(500):                                   # level 1, full grids
    h = rng.choice(mono) if n % 2 else [rng.choice(C.V) for _ in range(len(D1))]
    ok, why = differential(L1, D1, rel0, h, range(11), range(11), range(11))
    if not ok:
        gate("B differential (level 1)", False, why)
    cases += 1
report["differential_cases"] = cases
report["differential_test_checks"] = cases * len(tests)
gate("B differential", True,
     f"{cases} cases x {len(tests)} tests = {cases * len(tests)} per-test comparisons "
     f"(level-2 grids: {with_witness} with a witness, {without} without) "
     f"in {time.perf_counter() - t:.0f}s")

# full-grid negative controls: definable candidates have no witness anywhere
for n in range(20):
    h = random_candidate("query" if n % 2 else "cond")
    assert all(w is None for w in L2.falsify(h)), "definable candidate falsified"
gate("B full-grid definable controls", True, "(20 candidates, all 44.7M triples, no witness)")

# ---------------------------------------------------------------------------
# Gate C: historical witnesses
# ---------------------------------------------------------------------------
# The ternary relation R = S^3_{01,012}: x0 = BOT or x1 = BOT or x0 = x1 = x2.
R = C.elementary_mask({0, 1}, {0, 1, 2})
tR = tests.index(R)
f0, f1, f2 = D1.index((C.BOT, C.BOT, C.TT)), D1.index((C.BOT, C.TT, C.BOT)), D1.index((C.BOT,) * 3)
assert C.related_D1_tuple(R, D1, (f0, f1, f2))
rejected = [h for h in mono if h not in definable]
hist = [h for h in rejected if (h[f0], h[f1], h[f2]) == (C.TT, C.TT, C.BOT)]
for h in hist:
    w = L1.falsify(h, [f0], [f1], [f2])[tR]
    assert w == (f0, f1, f2)
gate("C historical AND witness", len(hist) > 0,
     f"((BOT,BOT,tt),(BOT,tt,BOT),(BOT,BOT,BOT)) under S^3_(01,012) rediscovered for {len(hist)} rejected candidates")
for h in rejected:
    ws = L1.falsify(h)
    tw = next(t for t, w in enumerate(ws) if w is not None)
    assert ws[tw] in C.candidate_witnesses(tests[tw], D1, rel0[tw], h)
gate("C every rejected D2 candidate has a CPU-verified GPU witness", True, f"({len(rejected)})")

# ---------------------------------------------------------------------------
# Benchmark: one candidate against all arity-3 tests on the full D2^3 grid
# ---------------------------------------------------------------------------
def bench(h, tg, reps=5):
    L2.falsify(h, threadgroup=tg)                       # warm-up
    ts = []
    for _ in range(reps):
        s = time.perf_counter()
        L2.falsify(h, threadgroup=tg)
        ts.append(time.perf_counter() - s)
    return min(ts)


triples = len(D2) ** 3
bench_rows = []
for label, h in [("definable F(id) (no witness: worst case)", [F[D1.index((C.BOT, C.TT, C.FF))] for F in D2]),
                 ("uniform random table", random_candidate("uniform"))]:
    for tg in (128, 256, 512):
        s = bench(h, tg)
        bench_rows.append((label, tg, s, triples / s))
        print(f"  {label:42s} tg={tg:3d}: {s * 1e3:8.1f} ms  {triples / s / 1e9:6.2f} G triples/s", flush=True)
report["benchmark"] = [dict(candidate=a, threadgroup=b, seconds=c, triples_per_second=d)
                       for a, b, c, d in bench_rows]


def sysinfo():
    def sh(cmd):
        return subprocess.run(cmd, shell=True, capture_output=True, text=True).stdout.strip()
    return dict(model=sh("sysctl -n hw.model"), chip=sh("sysctl -n machdep.cpu.brand_string"),
                gpu_cores=sh("system_profiler SPDisplaysDataType | awk -F': ' '/Total Number of Cores/{print $2}'"),
                ram_gb=int(sh("sysctl -n hw.memsize")) // 2**30, mlx=mx.__version__,
                python=platform.python_version())


report["system"] = sysinfo()
report["wall_seconds"] = time.perf_counter() - t0
print(json.dumps(report, indent=1))
