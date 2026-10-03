"""Arity-4 violation oracle for a table h : D2 -> B (values bot/tt/ff).

For each arity-4 test (one per permutation class), z3 searches for an
R-related 4-tuple of D2 whose image under h lies outside R.  Witnesses are
re-verified directly.  Tests that produced a violation before are tried first.
"""
import os, sys
from itertools import product
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arity4_h3

W = 4
GT = list(product(range(3), repeat=W))
# m4's tables (its numbering of D2), cached: importing m4 takes ~20 s per process
_TABLES = os.environ.get("M4_TABLES", os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "m4_tables.npz"))
if not os.path.exists(_TABLES):
    import m4
    np.savez(_TABLES, A=m4.A, D1=np.array(m4.D1, dtype=np.uint8))
_z = np.load(_TABLES)
A = _z["A"]; D1 = _z["D1"]; N, M = A.shape
REPS = sorted(arity4_h3.canonical_tests())
_rel1 = {}
_h = None


def rel1(mask):
    if mask not in _rel1:
        Rarr = np.array([(mask >> k) & 1 for k in range(len(GT))], dtype=bool).reshape((3,) * W)
        gt = np.argwhere(Rarr)
        Phis = np.array(list(product(range(M), repeat=W)))
        ok = Rarr[tuple(D1[Phis[:, None, i], gt[None, :, i]] for i in range(W))].all(axis=1)
        _rel1[mask] = (Rarr, Phis[ok])
    return _rel1[mask]


def solve(mask):
    import z3
    h = _h
    Rarr, r1 = rel1(mask)
    pats = [p for p in product(range(3), repeat=W) if not Rarr[p]]
    # a pattern is reachable only if every value it uses is a value of h
    vals = set(np.unique(h).tolist())
    pats = [p for p in pats if set(p) <= vals]
    if not pats:
        return None
    s = z3.SolverFor("QF_FD")
    sel = [[z3.Bool(f"x{i}_{F}") for F in range(N)] for i in range(W)]
    val = [[[z3.Bool(f"v{i}_{a}_{v}") for v in range(3)] for a in range(M)] for i in range(W)]
    for i in range(W):
        s.add(z3.PbEq([(b, 1) for b in sel[i]], 1))
        for a in range(M):
            for v in range(3):
                s.add(val[i][a][v] == z3.Or([sel[i][F] for F in np.nonzero(A[:, a] == v)[0]]))
    forbidden = [g for g in GT if not Rarr[g]]
    for phi in r1:
        for g in forbidden:
            s.add(z3.Or([z3.Not(val[i][phi[i]][g[i]]) for i in range(W)]))
    out = [[z3.Or([sel[i][F] for F in np.nonzero(h == v)[0]] or [z3.BoolVal(False)]) for v in range(3)] for i in range(W)]
    s.add(z3.Or([z3.And([out[i][p[i]] for i in range(W)]) for p in pats]))
    if s.check() != z3.sat:
        return None
    m = s.model()
    tup = [next(F for F in range(N) if z3.is_true(m.eval(sel[i][F], True))) for i in range(W)]
    assert Rarr[tuple(A[np.array(tup)[None, :], r1].T)].all(), "witness not related"
    assert not Rarr[tuple(int(h[F]) for F in tup)], "witness not violating"
    return mask, tup


def _init(h):
    global _h
    _h = h


def falsify(h, order, budget, first=True):
    """Return (violations, complete).  `order` lists test masks to try first.
    Workers are spawned (the caller may hold a z3 solver, which must not be forked)."""
    import multiprocessing as mp, time
    t0 = time.time()
    seq = list(dict.fromkeys(list(order) + REPS))
    found, done = [], 0
    with mp.get_context("spawn").Pool(os.cpu_count(), initializer=_init, initargs=(h,)) as pool:
        for r in pool.imap(solve, seq, chunksize=1):
            done += 1
            if r is not None:
                found.append(r)
                if first:
                    pool.terminate(); break
            if time.time() - t0 > budget:
                pool.terminate(); break
    falsify.done = done
    return found, done == len(seq) and not (first and found)


def falsify_subprocess(h, order, budget):
    """Run falsify in a fresh interpreter (safe from any caller, including one
    whose __main__ must not be re-imported by spawned workers)."""
    import json, subprocess, tempfile
    with tempfile.TemporaryDirectory() as d:
        hp = os.path.join(d, "h.npy"); np.save(hp, h); jp = os.path.join(d, "out.json")
        # result via a file: multiprocessing helpers can keep inherited pipes open
        # own process group with a hard deadline, so no worker outlives the caller's budget
        p = subprocess.Popen(["perl", "-e", "alarm shift; exec @ARGV", str(int(budget) + 30), sys.executable,
                              os.path.abspath(__file__), hp, str(budget), "--json=" + jp] + [hex(m) for m in order],
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
        try:
            p.wait()
        finally:
            import signal
            try: os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError: pass
        if not os.path.exists(jp): return [], False
        r = json.load(open(jp))
    return [(int(m, 16), t) for m, t in r["found"]], r["complete"]


if __name__ == "__main__":
    import json, time
    h = np.load(sys.argv[1]); t = time.time()
    order = [int(a, 16) for a in sys.argv[3:] if a.startswith("0x")]
    f, complete = falsify(h, order, float(sys.argv[2]))
    jp = next((a[len("--json="):] for a in sys.argv if a.startswith("--json=")), None)
    if jp:
        json.dump({"found": [[hex(m), tup] for m, tup in f], "complete": complete}, open(jp, "w"))
    else:
        print(f"violations {f}, complete={complete}, tests done {falsify.done}/{len(REPS)}, {time.time()-t:.1f}s")
