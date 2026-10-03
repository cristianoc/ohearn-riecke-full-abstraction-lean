"""Arity-3 violation oracle in numpy: the related triples of D2 for each
non-trivial arity-3 test, cached on disk (path from $ARITY3_CACHE)."""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sieber_cpu as C

CACHE = os.environ.get("ARITY3_CACHE", os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "arity3_triples.npz"))


class Oracle:
    def __init__(self):
        self.tests = [R for R in C.arity3_tests() if R != (1 << 27) - 1]
        if not os.path.exists(CACHE):
            from root_obstruction import lifted_triples
            tri = [t for _, t in lifted_triples()]
            np.savez(CACHE, tri=np.concatenate(tri), off=np.cumsum([0] + [len(t) for t in tri]))
        z = np.load(CACHE)
        tri, off = z["tri"].astype(np.int64), z["off"]
        self.tri = [tri[off[k]:off[k + 1]] for k in range(len(self.tests))]
        self.R = [np.array([(R >> x) & 1 for x in range(27)], dtype=bool).reshape(3, 3, 3) for R in self.tests]

    def falsify(self, h):
        """Per test: a violating related triple (i, j, k), or None."""
        out = []
        for Rarr, tri in zip(self.R, self.tri):
            p = h[tri]
            bad = np.flatnonzero(~Rarr[p[:, 0], p[:, 1], p[:, 2]])
            out.append(tuple(int(v) for v in tri[bad[0]]) if len(bad) else None)
        return out
