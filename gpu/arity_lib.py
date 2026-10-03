"""Reindexing of Sieber tests along surjections (ARITY.md).

Ground values BOT=0, TT=1, FF=2.  A test of arity w is a boolean numpy array
of shape (3,)*w.  A level is a carrier given as value tables over the
argument set of the previous level; `argrel(T, w)` returns the related
argument tuples for a test T of arity w as an (m, w) integer array.

For a surjection pi : w -> k (a tuple of length w with values 0..k-1):
  P = pi^*(R_tau)   = {x in D^k : x o pi in R_tau}
  Q = (pi^*R)_tau   lifted from the reindexed ground test pi^*R
  Q' = {x : x o pi in (R n E_pi)_tau}, E_pi = fibrewise equality (Lemma R2).
"""
import os
import sys
from itertools import product

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

V = (0, 1, 2)


# ---------------------------------------------------------------- tests

def elementary(w, A, B):
    T = np.zeros((3,) * w, dtype=bool)
    for g in product(V, repeat=w):
        T[g] = any(g[i] == 0 for i in A) or len({g[i] for i in B}) <= 1
    return T


def all_tests(w):
    """All distinct finite intersections of S^w_{A,B} (including the full relation)."""
    subs = [frozenset(i for i in range(w) if s >> i & 1) for s in range(1 << w)]
    weights = 1 << np.arange(3 ** w, dtype=object)
    def tomask(T):
        return int(sum(int(b) << i for i, b in enumerate(T.ravel())))
    gens = {tomask(elementary(w, A, B)) for A in subs for B in subs if A <= B}
    full = (1 << 3 ** w) - 1
    cl = {full}
    for g in gens:
        cl |= {r & g for r in cl}
    return sorted(cl)


def from_mask(m, w):
    n = 3 ** w
    return np.array([(m >> i) & 1 for i in range(n)], dtype=bool).reshape((3,) * w)


def pullback(R, pi, k):
    """pi^*R = {x in V^k : x o pi in R}."""
    S = np.zeros((3,) * k, dtype=bool)
    for x in product(V, repeat=k):
        S[x] = R[tuple(x[p] for p in pi)]
    return S


def fibre_equality(pi, k):
    w = len(pi)
    E = np.ones((3,) * w, dtype=bool)
    for j in range(k):
        E &= elementary(w, (), [i for i in range(w) if pi[i] == j])
    return E


def surjections(w, k):
    return [p for p in product(range(k), repeat=w) if set(p) == set(range(k))]


# ---------------------------------------------------------------- levels

def ground_argrel(T):
    w = T.ndim
    return np.array([g for g in product(V, repeat=w) if T[g]], dtype=np.int64).reshape(-1, w)


def related(elems, argrel, T, X, chunk=64):
    """Boolean mask over rows of X (n, w): is (elems[X_i])_i related, i.e. for
    every row G of argrel, (elems[X_i, G_i])_i in T?"""
    w = T.ndim
    flat = T.ravel()
    pw = 3 ** np.arange(w - 1, -1, -1)
    alive = np.arange(len(X))
    for s in range(0, len(argrel), chunk):
        if len(alive) == 0:
            break
        G = argrel[s:s + chunk]
        idx = np.zeros((len(alive), len(G)), dtype=np.int64)
        for i in range(w):
            idx += elems[X[alive, i][:, None], G[None, :, i]].astype(np.int64) * pw[i]
        alive = alive[flat[idx].all(axis=1)]
    out = np.zeros(len(X), dtype=bool)
    out[alive] = True
    return out


def all_tuples(n, w):
    return np.array(list(product(range(n), repeat=w)), dtype=np.int64).reshape(-1, w)


class Level:
    def __init__(self, name, elems, argrel):
        self.name, self.elems, self.argrel = name, np.asarray(elems, dtype=np.uint8), argrel
        self._cache = {}

    def lifted(self, T):
        """All related w-tuples of this level (full enumeration; small levels only)."""
        key = (T.shape, T.tobytes())
        if key not in self._cache:
            X = all_tuples(len(self.elems), T.ndim)
            self._cache[key] = X[related(self.elems, self.argrel(T), T, X)]
        return self._cache[key]


def level_D1():
    import sieber_cpu as C
    D1 = C.carrier_D1()
    return Level("B->B", D1, ground_argrel), D1


def level_BBB():
    """D_{B->B->B} = definable maps V^2 -> V (Sieber: order <= 2 carriers are the
    definable elements), as tables indexed by 3a+b; arguments are pairs of
    ground tuples (g, g') with g, g' in T."""
    proj = [tuple(a for a in V for b in V), tuple(b for a in V for b in V)]
    S = {tuple([v] * 9) for v in V} | set(proj)
    while True:
        arr = sorted(S)
        new = set(S)
        for c in arr:
            for a in arr:
                for b in arr:
                    new.add(tuple(0 if c[i] == 0 else (a[i] if c[i] == 1 else b[i]) for i in range(9)))
        if new == S:
            break
        S = new
    elems = sorted(S)

    def argrel(T):
        g = ground_argrel(T)
        return (3 * g[:, None, :] + g[None, :, :]).reshape(-1, T.ndim)
    return Level("B->B->B", elems, argrel)


def level_D2(D1lev, cache=os.path.join(HERE, "data", "arity_D2.npy")):
    if os.path.exists(cache):
        A = np.load(cache)
    else:
        import sieber_cpu as C
        A = np.array(sorted(C.definable_D2(C.carrier_D1())), dtype=np.uint8)
        np.save(cache, A)
    return Level("(B->B)->B", A, D1lev.lifted)


# ---------------------------------------------------------------- comparison

def compare(level, R, pi, k, X=None, check_R2=True):
    """Return (P, Q, Q2) masks over candidate k-tuples X (default: all)."""
    if X is None:
        X = all_tuples(len(level.elems), k)
    pi = np.array(pi)
    S = pullback(R, pi, k)
    P = related(level.elems, level.argrel(R), R, X[:, pi])
    Q = related(level.elems, level.argrel(S), S, X)
    Q2 = None
    if check_R2:
        RE = R & fibre_equality(tuple(pi), k)
        Q2 = related(level.elems, level.argrel(RE), RE, X[:, pi])
    return P, Q, Q2
