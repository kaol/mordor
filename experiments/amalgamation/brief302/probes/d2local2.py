"""Free analysis on the 428 stored relaxed-world models (pairselfM predicate). Instance: colour c0, lambda(c0)=m pair-join,
c0 <= m.  PairLocal: lambda(m) != m ==> some colour c' <= m (c' != c0) with c0 not <= lambda(c')."""
import collections
from wlib import relaxed
C=collections.Counter(); ex=[]
for M in relaxed():
    le=M.le
    for c0 in M.cols:
        m=M.lam(c0)
        if m not in M.pjs or not le[c0][m]: continue
        lm=M.lam(m); others=[c for c in M.C(m) if c!=c0]
        bad=[c for c in others if not le[c0][M.lam(c)]]
        C[('inst','lam(m)=m' if lm==m else 'lam(m)!=m','|C(m)|=%d'%len(M.C(m)),'all others c0<=lam' if not bad else 'some other c0 not<=lam')]+=1
        if lm!=m and not bad: ex.append((M.src,c0,m))
        for c in others:
            l1=M.lam(c)
            C[('c\' type', 'c0<=lam(c\')' if le[c0][l1] else 'c0 not<=', 'lamc\' in Z' if l1 in M.Zs else ('exit to c0' if M.phi[l1]==c0 else 'exit other'), 'lam(c\')=m' if l1==m else '-', 'lam(m)=m' if lm==m else 'lam(m)!=m')]+=1
for k,v in sorted(C.items(), key=lambda t:str(t[0])): print(' ',v,k)
print('PairLocal counterexamples:', ex)
