import sys, time, itertools
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, sieber_cpu as C, arity_lib as L
t0=time.time()
w=4; tests=[L.from_mask(m,w) for m in L.all_tests(w)]
R=[T for T in tests if T.sum()==7][0]
pi=(0,1,0,2); k=3
D1lev,_=L.level_D1(); D2lev=L.level_D2(D1lev)
D2=D2lev.elems.astype(np.int64)          # D2[x, f] in V
RD1=D1lev.lifted(R)                     # (55,4) D1 indices
S=L.pullback(R,pi,k); Ys=D1lev.lifted(S)
print("|D2|",len(D2),"|R_D1|",len(RD1),"|Q_D1|",len(Ys))
Rflat=R.ravel()
# values per G: P0[x,G]=x(G0), P1[x,G]=x(G1), P2[x,G]=x(G2), P3[x,G]=x(G3)
P=[D2[:, RD1[:, i]] for i in range(4)]
n=len(D2)
found=0; pairs=0
for a in range(n):
    sig_q = P[1]                                   # (n,55) for x1
    p0=P[0][a]; p2=P[2][a]                         # (55,)
    # for each x1: base index of (p,q,r,*) ; allowed s values per G
    base = (p0*27)[None,:] + P[1]*9 + (p2*3)[None,:]   # (n,55)
    allowed = np.stack([Rflat[base + s] for s in range(3)], axis=2)  # (n,55,3)
    # unique x1 behaviours
    keys, inv = np.unique(allowed.reshape(n,-1), axis=0, return_inverse=True)
    inv=inv.ravel()
    for kid, key in enumerate(keys):
        al = key.reshape(55,3)
        ok2 = al[np.arange(55)[None,:], P[3]].all(axis=1)   # x2 candidates (n,)
        if not ok2.any(): continue
        x1s = np.nonzero(inv==kid)[0]
        x2s = np.nonzero(ok2)[0]
        # violation: (x0 y0, x1 y1, x2 y2) not in pi*R, for some y in Ys
        for y in Ys:
            u0 = D2[a, y[0]]
            u1 = D2[x1s, y[1]]; u2 = D2[x2s, y[2]]
            bad = ~S[u0, u1[:,None], u2[None,:]]
            if bad.any():
                i,j = np.argwhere(bad)[0]
                print("COUNTEREXAMPLE x=",a,x1s[i],x2s[j]," y=",y, " u=",(u0,u1[i],u2[j]))
                found+=1; break
        if found: break
    if found or time.time()-t0>50: break
print("done" if not found else "found", "x0 scanned up to", a, "time", round(time.time()-t0,1))
