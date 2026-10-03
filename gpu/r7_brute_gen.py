"""Exhaustive R7 check at D2 for arity-4 tests and maps pi: 4 -> k (k=2,3).
Usage: r7_brute_gen.py SECONDS [seed]  -- samples (R, pi) cases at random."""
import sys, time, itertools, random
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, arity_lib as L
budget=float(sys.argv[1]); random.seed(int(sys.argv[2]) if len(sys.argv)>2 else 0)
t0=time.time(); w=4
masks=L.all_tests(w)
D1lev,_=L.level_D1(); D2=L.level_D2(D1lev).elems.astype(np.int64); n=len(D2)

def check(R, pi, k, cap=8.0):
    """(True, None) if P subset Q at D2; (False, witness) on a counterexample; (None, None) if capped."""
    tc=time.time()
    RD1=D1lev.lifted(R); S=L.pullback(R,pi,k); Ys=D1lev.lifted(S)
    Rflat=R.ravel(); pw=[27,9,3,1]; m=len(RD1)
    Pv=[D2[:, RD1[:, i]] for i in range(4)]
    blocks=[[i for i in range(4) if pi[i]==j] for j in range(k)]
    def contrib(j, xs):                       # (len(xs), m) index contribution of block j
        c=np.zeros((len(xs), m), dtype=np.int64)
        for i in blocks[j]: c+=Pv[i][xs]*pw[i]
        return c
    allx=np.arange(n)
    last=contrib(k-1, allx)                   # (n, m)
    mid=contrib(k-2, allx)                    # (n, m)
    for pre in itertools.product(range(n), repeat=k-2):
        if time.time()-tc>cap: return None, None
        base=np.zeros(m, dtype=np.int64)
        for j in range(k-2): base+=contrib(j, np.array([pre[j]]))[0]
        # allowed last-values per G for each middle choice: group middle choices by row of (base+mid)
        rows=base[None,:]+mid                 # (n, m)
        keys, inv=np.unique(rows, axis=0, return_inverse=True); inv=inv.ravel()
        for kid, key in enumerate(keys):
            ok=Rflat[key[None,:]+last].all(axis=1)
            if not ok.any(): continue
            mids=np.nonzero(inv==kid)[0]; cand=np.nonzero(ok)[0]
            for y in Ys:
                u=tuple(D2[pre[j], y[j]] for j in range(k-2))
                um=D2[mids, y[k-2]]; ul=D2[cand, y[k-1]]
                bad=~S[u+(um[:,None], ul[None,:])]
                if bad.any():
                    a,b=np.argwhere(bad)[0]
                    return False, (pre, mids[a], cand[b], tuple(y))
    return True, None

cases=0; slow=[]
while time.time()-t0<budget:
    R=L.from_mask(random.choice(masks),w); k=random.choice([2,3])
    pi=random.choice(L.surjections(w,k))
    t1=time.time(); ok,info=check(R,pi,k); dt=time.time()-t1
    cases+=1; slow.append((round(dt,2), int(R.sum()), k, ok))
    if ok is False:
        print("COUNTEREXAMPLE", R.sum(), pi, info); break
slow.sort(reverse=True)
print("cases",cases,"elapsed",round(time.time()-t0,1),"slowest",slow[:6])
