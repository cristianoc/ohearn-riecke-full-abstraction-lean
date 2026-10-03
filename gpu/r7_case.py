import sys, itertools
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, sieber_cpu as C, arity_lib as L
w=4
tests=[L.from_mask(m,w) for m in L.all_tests(w)]
R=[T for T in tests if T.sum()==7][0]
names="⊥tf"
print("R tuples:", ["".join(names[v] for v in g) for g in itertools.product(range(3),repeat=4) if R[g]])
D1=[tuple(f) for f in C.carrier_D1()]
D1lev,_=L.level_D1()
RD1=D1lev.lifted(R); print("|R_D1|", len(RD1))
pi=(0,1,0,2); S=L.pullback(R,pi,3)
print("pi*R tuples:", ["".join(names[v] for v in g) for g in itertools.product(range(3),repeat=3) if S[g]])
print("elementary supersets containing R:", [(sorted(A),sorted(B)) for A in [frozenset(i for i in range(w) if s>>i&1) for s in range(16)] for B in [frozenset(i for i in range(w) if s>>i&1) for s in range(16)] if A<=B and len(B)>=2 and (R<=L.elementary(w,A,B)).all()])
