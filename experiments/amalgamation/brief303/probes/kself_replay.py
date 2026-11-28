"""kSelf (run-28 briefer), free replay on every stored model with ZT (phi(B) != bot for high B).
Statement: p of height 2, y a landing row, S = {atoms q <= y with Tb at q and p in desc(q)}.
If S != {} and C'(p) <= S (every atom phi(X), X high, below p is in S), then lambda(y) = p.
Prints instances (hypothesis true) and violations (hypothesis true, lambda(y) != p).  A violation would refute a theorem."""
from alib import *
Ms=load(); inst=0; viol=0; models=0; bigC=0
for M in Ms:
    if not zt(M): continue
    models+=1; le=M.le; h=M.h
    tb={q:tb_at(M,q) for q in range(M.n) if h[q]==1}
    for p in range(M.n):
        if h[p]!=2: continue
        Cpp=Cp(M,p)
        for y in range(M.n):
            if M.lam(y) is None: continue
            S=[q for q in tb if tb[q] and le[q][y] and p in M.desc(q)]
            if S and set(Cpp)<=set(S):
                inst+=1; bigC+= len(Cpp)>=3
                if M.lam(y)!=p: viol+=1; print('VIOLATION',M.src,p,y,S,Cpp)
print(f'kSelf replay: {models} stored models with ZT; {inst} instances (|C\'(p)|>=3 in {bigC}); {viol} violations')
