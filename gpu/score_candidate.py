#!/usr/bin/env python3
"""Ordinary-arity score of a candidate table h : D2 -> B at tau0 = ((B->B)->B)->B.

Usage (from the repository root; needs numpy and z3-solver):

  python gpu/score_candidate.py H.npy [--max-arity 3|4] [--first] [--time-limit SEC]
                                [--workers N] [--json OUT.json]
  python gpu/score_candidate.py --definable-control OUT.npy [options]

H.npy is a uint8 array of length 355 indexed like D2 (m4.A), with values
0 = bot, 1 = tt, 2 = ff (the format of gpu/data/candidate_3cone_h.npy).
--definable-control writes the table of an explicit closed term (see
definable_control) to OUT.npy and scores it.

Reported:
  (a) monotonicity (and a violating pair if any);
  (b) every non-trivial arity-3 test (85 masks, sieber_cpu.arity3_tests) that h
      violates, with one witness triple each; the arity-3 masks include all
      tests of arity 1 and 2 (constant in the remaining coordinates);
  (c) every arity-4 intersection class (1,027 up to coordinate permutation,
      arity4_h3.canonical_tests) that h violates, with the first witness z3
      finds per class; a permuted test is violated iff the original is, so the
      classes cover all 17,240 intersections;
  (d) score = largest k such that h preserves every test of arity <= k among
      those checked.  The arity of a test is its number of essential
      coordinates; "killed at" is the least arity of a violated test.
Every witness is re-verified directly from the definitions: arity-3 witnesses
with sieber_cpu.related_D2_tuple, arity-4 witnesses by enumerating all of D1^4.
A score of K with no violation found is a lower bound: preservation of all
tests of every arity is not a finite check.

Run time on an M2 Max (12 cores): D2 about 6 s; arity 3 about 2 s on the GPU
(sieber_metal, needs mlx), otherwise 10-50 s on the CPU depending on the
table's output buckets; arity 4 is one SAT query per class, all 1,027 classes
in 35-90 s on all cores.  --time-limit (default 540 s, counted from start)
stops the arity-4 search and the report then states how many classes were
checked ("score >= 3", partial).  --first stops at the first arity-4 witness,
which settles the score of a table that survives arity 3.
With mlx:  uv run --python 3.12 --with mlx --with numpy --with z3-solver \
             python gpu/score_candidate.py H.npy
"""
import argparse, json, os, sys, time

T_START = time.perf_counter()
from itertools import product
from multiprocessing import Pool

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sieber_cpu as C
import arity4_h3 as A4

BOT, TT, FF = C.BOT, C.TT, C.FF
D1 = C.carrier_D1()
M = len(D1)
D1A = np.array(D1, dtype=np.uint8)


def definable_D2():
    """The set sieber_cpu.definable_D2 computes (closure of the constants under
    application of f and the pointwise strict conditional), sorted as in m4.D2.
    Semi-naive: each round combines only triples containing a new element.
    `--check-d2` compares it with sieber_cpu.definable_D2 (about 20 s)."""
    code = 3 ** np.arange(M)
    seen = np.zeros(3 ** M, dtype=bool)
    old = np.zeros((0, M), dtype=np.uint8)
    new = np.array([[v] * M for v in (BOT, TT, FF)], dtype=np.uint8)
    seen[new.astype(np.int64) @ code] = True

    def cond(c, a, b):                  # c: (M,), a: (p, M), b: (q, M) -> (p*q, M)
        return np.where(c == BOT, BOT, np.where(c == TT, a[:, None, :], b[None, :, :])).reshape(-1, M)

    while len(new):
        allr = np.concatenate([old, new])
        cand = [D1A[np.arange(M)[None, :], new]]
        for c in new:
            cand.append(cond(c, allr, allr))
        for c in old:
            cand.append(cond(c, new, allr))
            cand.append(cond(c, old, new))
        cand = np.concatenate(cand).astype(np.uint8)
        codes = cand.astype(np.int64) @ code
        codes, first = np.unique(codes, return_index=True)
        fresh = ~seen[codes]
        seen[codes[fresh]] = True
        old, new = allr, cand[first[fresh]]
    return np.array(sorted(map(tuple, old.tolist())), dtype=np.uint8)


IDX = -np.ones((3, 3, 3), dtype=np.int16)
for _i, _f in enumerate(D1):
    IDX[_f] = _i
A = N = D2 = LE = None                  # set by setup() (main) or _init (workers)


def setup(table=None):
    global A, N, D2, LE
    A = definable_D2() if table is None else table
    N = len(A)
    D2 = [tuple(r) for r in A.tolist()]
    LE = ((A[:, None, :] == BOT) | (A[:, None, :] == A[None, :, :])).all(axis=2)


def essential_arity(arr):
    """Number of coordinates on which membership in the ground relation depends."""
    return sum(1 for i in range(arr.ndim) if not (arr == arr.take([0], axis=i)).all())


def mask3(R):
    return np.array([(R >> x) & 1 for x in range(27)], dtype=bool).reshape(3, 3, 3)


def mask4(m):
    return np.array([(m >> k) & 1 for k in range(len(A4.T))], dtype=bool).reshape((3,) * 4)


# ---------------------------------------------------------------------------
# (a) monotonicity
# ---------------------------------------------------------------------------
def monotonicity(h):
    """Pairs F <= G with h(F) not <= h(G).  Monotonicity is preservation of the
    arity-2 test S^2_{{0},{0,1}} (the order of B), so a violation kills at 2."""
    bad = np.argwhere(LE & ~((h[:, None] == BOT) | (h[:, None] == h[None, :])))
    return [(int(i), int(j)) for i, j in bad]


# ---------------------------------------------------------------------------
# (b) arity 3
# ---------------------------------------------------------------------------
def arity3(h):
    """Arity-3 witnesses: on the GPU (sieber_metal, M1 kernel) when mlx is
    available, otherwise on the CPU (arity3_cpu)."""
    tests = [R for R in C.arity3_tests() if R != (1 << 27) - 1]
    try:
        import sieber_metal as G
    except ImportError:
        G = None
    if G is None:
        found = arity3_cpu(h, tests)
        print("    (arity 3 on the CPU; install mlx for the GPU path)")
    else:
        level = G.Level(D2, tests, [C.lift_ground_to_D1(R, D1) for R in tests])
        found = [(R, w) for R, w in zip(tests, level.falsify(h)) if w is not None]
    out = []
    for R, w in found:
        # direct re-verification from the definitions
        assert C.related_D2_tuple(R, D1, D2, w), "arity-3 witness not related"
        assert not C.ground_member(R, tuple(int(h[x]) for x in w)), "arity-3 witness not violating"
        out.append({"test": hex(R), "arity": essential_arity(mask3(R)), "witness": list(w),
                    "outputs": [int(h[x]) for x in w]})
    return len(tests), out


def arity3_cpu(h, tests):
    """For each test, scan only the buckets H_u x H_v x H_w (H_u = h^-1(u)) whose
    output pattern (u, v, w) lies outside the test; the lifted relation at D2
    is computed on those buckets only, from the D1 lift (as root_obstruction)."""
    values = sorted(set(h.tolist()))
    H = {v: np.nonzero(h == v)[0] for v in values}
    out = []
    for R in tests:
        Rarr = mask3(R)
        pats = [p for p in product(values, repeat=3) if not Rarr[p]]
        if not pats:
            continue
        by = {}
        for a, b, c in C.lift_ground_to_D1(R, D1):
            by.setdefault((a, b), []).append(c)
        w = None
        for p in pats:
            I, J, K = H[p[0]], H[p[1]], H[p[2]]
            rel = np.ones((len(I), len(J), len(K)), dtype=bool)
            for (a, b), cs in by.items():
                mk = Rarr[:, :, A[K][:, cs]].all(axis=3)            # (3, 3, |K|)
                rel &= mk[A[I, a][:, None], A[J, b][None, :], :]
                if not rel.any():
                    break
            hit = np.argwhere(rel)
            if len(hit):
                i, j, k = hit[0]
                w = (int(I[i]), int(J[j]), int(K[k]))
                break
        if w is not None:
            out.append((R, w))
    return out


# ---------------------------------------------------------------------------
# (c) arity 4
# ---------------------------------------------------------------------------
_h = None


def _init(h, table):
    global _h
    _h = h
    setup(table)


def solve4(mask):
    """SAT: a related 4-tuple of D2 whose image under h lies outside the test.

    CNF (DIMACS, parsed by z3 in C).  Variables: s[i,F] (coordinate i may be F),
    v[i,a,x] (some chosen F at coordinate i has F(a) = x), y[p] (output pattern p).
      s[i,F] -> v[i,a,F(a)]                       for all i, F, a
      OR_i not v[i,phi_i,g_i]                     for phi in the D1 lift, g outside R
      OR_p y[p];  y[p] -> OR_{F in h^-1(p_i)} s[i,F]   for each i
    From a model, any F in h^-1(p_i) with s[i,F] gives a witness: its values are
    among the true v[i,...], so every clause above still holds for it alone."""
    import z3
    h = _h
    W = 4
    Rarr = mask4(mask)
    values = sorted(set(h.tolist()))
    pats = [p for p in product(values, repeat=W) if not Rarr[p]]
    if not pats:
        return mask, None
    gt = np.argwhere(Rarr)
    Phis = np.array(list(product(range(M), repeat=W)))
    ok = Rarr[tuple(D1A[Phis[:, None, i], gt[None, :, i]] for i in range(W))].all(axis=1)
    rel1 = Phis[ok]
    forb = np.argwhere(~Rarr)                                        # (G, W)

    def sv(i, F):
        return 1 + i * N + F

    def vv(i, a, x):
        return 1 + W * N + (i * M + a) * 3 + x

    ybase = 1 + W * N + W * M * 3
    lines = []
    # s -> v
    I, F, a = np.meshgrid(np.arange(W), np.arange(N), np.arange(M), indexing="ij")
    I, F, a = I.ravel(), F.ravel(), a.ravel()
    lines.append(np.stack([-sv(I, F), vv(I, a, A[F, a].astype(np.int64)), np.zeros_like(I)], 1))
    # relatedness
    lits = np.stack([-vv(i, rel1[:, None, i], forb[None, :, i]) for i in range(W)], 2).reshape(-1, W)
    lines.append(np.concatenate([lits, np.zeros((len(lits), 1), dtype=np.int64)], 1))
    text = [" ".join(map(str, r)) for arr in lines for r in arr.tolist()]
    text.append(" ".join(str(ybase + k) for k in range(len(pats))) + " 0")
    for k, p in enumerate(pats):
        for i in range(W):
            text.append(f"-{ybase + k} " + " ".join(str(sv(i, F)) for F in np.nonzero(h == p[i])[0]) + " 0")
    nvars = ybase + len(pats) - 1
    s = z3.SolverFor("QF_FD")
    s.from_string(f"p cnf {nvars} {len(text)}\n" + "\n".join(text) + "\n")
    if s.check() != z3.sat:
        return mask, None
    m = s.model()
    true = {int(d.name()[2:]) for d in m.decls() if z3.is_true(m[d])}
    k = next(k for k in range(len(pats)) if ybase + k in true)
    tup = [next(int(F) for F in np.nonzero(h == pats[k][i])[0] if sv(i, F) in true) for i in range(W)]
    return mask, tup


def verify4(mask, tup, h):
    """Direct check: tup is related at D2 and its image under h is outside the test."""
    Rarr = mask4(mask)
    ground = [g for g in product(range(3), repeat=4) if Rarr[g]]
    for phi in product(range(M), repeat=4):
        if all(Rarr[tuple(D1[phi[i]][g[i]] for i in range(4))] for g in ground):
            assert Rarr[tuple(int(A[tup[i], phi[i]]) for i in range(4))], "arity-4 witness not related"
    assert not Rarr[tuple(int(h[F]) for F in tup)], "arity-4 witness not violating"


def arity4(h, workers, deadline, first):
    """Returns (number of classes, number checked, violations).  Stops at the
    deadline (time.perf_counter() value) or, with `first`, at the first violation."""
    import multiprocessing as mp
    reps = A4.canonical_tests()
    found, checked, t0 = [], 0, time.perf_counter()
    pool = Pool(workers, initializer=_init, initargs=(h, A))
    try:
        it = pool.imap_unordered(solve4, reps, chunksize=1)
        while checked < len(reps):
            try:
                mask, tup = it.next(timeout=max(0.0, deadline - time.perf_counter()))
            except mp.TimeoutError:
                print("  arity 4: deadline reached", flush=True)
                break
            checked += 1
            if tup is not None:
                verify4(mask, tup, h)
                found.append({"test": hex(mask), "arity": essential_arity(mask4(mask)),
                              "witness": tup, "outputs": [int(h[F]) for F in tup]})
                if first:
                    break
            if checked % 100 == 0:
                print(f"  arity 4: {checked}/{len(reps)} classes, {len(found)} violated "
                      f"({time.perf_counter() - t0:.0f}s)", flush=True)
    finally:
        pool.terminate()
        pool.join()
    found.sort(key=lambda r: int(r["test"], 16))
    return len(reps), checked, found


# ---------------------------------------------------------------------------
# definable control
# ---------------------------------------------------------------------------
def definable_control():
    """Table of  λF. if F(λz. if F(λz.z) then z else ff) then tt else F(λz.tt),
    a closed term with a nested call in the first argument."""
    def col(phi):                       # phi: (N, 3) argument table per F -> F(phi_F)
        ix = IDX[phi[:, 0], phi[:, 1], phi[:, 2]]
        assert (ix >= 0).all()
        return A[np.arange(N), ix]

    def case(c, a, b):
        return np.where(c == BOT, BOT, np.where(c == TT, a, b)).astype(np.uint8)

    ident = np.tile(np.array([BOT, TT, FF]), (N, 1))
    const_tt = np.tile(np.array([TT, TT, TT]), (N, 1))
    c = col(ident)
    z = np.array([BOT, TT, FF])
    inner = np.where(c[:, None] == BOT, BOT, np.where(c[:, None] == TT, z[None, :], FF))
    return case(col(inner), np.full(N, TT, dtype=np.uint8), col(const_tt))


# ---------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("table", nargs="?")
    ap.add_argument("--definable-control", metavar="OUT.npy")
    ap.add_argument("--max-arity", type=int, default=4, choices=(3, 4))
    ap.add_argument("--workers", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--time-limit", type=float, default=540,
                    help="seconds for the whole run (default 540); arity 4 stops there "
                         "and the report is partial")
    ap.add_argument("--first", action="store_true",
                    help="stop arity 4 at the first violated class (enough for the score)")
    ap.add_argument("--json", metavar="OUT.json")
    ap.add_argument("--check-d2", action="store_true",
                    help="also compare D2 with sieber_cpu.definable_D2 (about 20 s)")
    args = ap.parse_args()
    setup()
    if args.check_d2:
        assert D2 == sorted(C.definable_D2(D1)), "D2 differs from sieber_cpu.definable_D2"
        print("D2 agrees with sieber_cpu.definable_D2")
    if args.definable_control:
        np.save(args.definable_control, definable_control())
        args.table = args.definable_control
    if not args.table:
        ap.error("give a table or --definable-control")
    h = np.load(args.table).astype(np.uint8)
    assert h.shape == (N,) and set(h.tolist()) <= {BOT, TT, FF}, "expected 355 values in {0,1,2}"
    t0 = T_START
    deadline = t0 + args.time_limit
    print(f"{args.table}: support {int((h != BOT).sum())}, values {sorted(set(h.tolist()))}")

    mono = monotonicity(h)
    print(f"(a) monotone: {not mono}" + (f" (e.g. {mono[0]})" if mono else ""))

    n3, v3 = arity3(h)
    print(f"(b) arity 3: violates {len(v3)} of {n3} tests ({time.perf_counter() - t0:.0f}s)")
    for r in v3[:10]:
        print(f"    {r['test']} (arity {r['arity']}): {r['witness']} -> {r['outputs']}")
    if len(v3) > 10:
        print(f"    ... {len(v3) - 10} more")

    n4, c4, v4 = None, 0, []
    if args.max_arity >= 4:
        n4, c4, v4 = arity4(h, args.workers, deadline, args.first)
        print(f"(c) arity 4: {c4}/{n4} classes checked, {len(v4)} violated "
              f"({time.perf_counter() - t0:.0f}s)" + ("" if c4 == n4 else " [partial]"))
        for r in v4[:10]:
            print(f"    {r['test']} (arity {r['arity']}): {r['witness']} -> {r['outputs']}")
        if len(v4) > 10:
            print(f"    ... {len(v4) - 10} more")

    arities = [r["arity"] for r in v3 + v4] + ([2] if mono else [])
    killed = min(arities) if arities else None
    complete4 = args.max_arity >= 4 and c4 == n4
    if killed:
        score = killed - 1
        print(f"(d) score {score}: killed at arity {killed}")
    else:
        score = 4 if complete4 else 3
        print(f"(d) score >= {score}: no violation among the tests checked "
              f"(arity 3 complete, arity-4 classes checked: {c4}/{n4 or 1027})")
    print("    all witnesses re-verified directly")
    if args.json:
        json.dump({"table": args.table, "monotone": not mono, "monotonicity_violations": mono[:20],
                   "arity3_tests": n3, "arity3_violations": v3,
                   "arity4_classes": n4, "arity4_checked": c4, "arity4_violations": v4,
                   "score": score, "killed_at": killed, "max_arity_checked": args.max_arity},
                  open(args.json, "w"), indent=1)


if __name__ == "__main__":
    main()
