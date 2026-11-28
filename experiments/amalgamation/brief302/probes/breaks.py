"""Free analysis (no search): SCL breaks on staircases (x colour row, y colour row or pair-join row) in the stored
relaxed-world models (pairselfM predicate) and in stored W0 models.  For each break corner A = c v a (c carried colour
of K(y), a = e = phi(B) outside K(y)) record: lambda(A) vs A, whether x <= A, lambda(c), lambda(a) relations."""
import collections, pickle, sys
from mlib import Mod, scl_walk
which=sys.argv[1] if len(sys.argv)>1 else 'relaxed'
pk={'relaxed':'pairselfM_models.pkl','w0':'w0_models.pkl'}[which]
ms=[Mod(s,F,src) for (src,s,F) in pickle.load(open(pk,'rb'))]
C=collections.Counter(); ex=[]
for M in ms:
    le=M.le; R=M.cols+M.pjs
    for x in M.cols:
        for y in R:
            r=scl_walk(M,x,y)
            if r is None: C['no landing']+=1; continue
            C[('pair', 'y colour' if y in M.cols else 'y pj', r[0])]+=1
            if r[0]!='break': continue
            d=r[2]; A=d['A']; a=d['e']; c=d['carried'][0]
            lA=M.lam(A)
            key=('y colour' if y in M.cols else 'y pj', 'A in Z' if A in M.Zs else 'A notZ', 'lam(A)<=A' if lA is not None and le[lA][A] else 'lam(A) not<=A',
                 'x<=A' if le[x][A] else 'x not<=A', 'x=c' if x==c else ('x=a' if x==a else 'x other'),
                 'c<=lam(c)' if le[c][M.lam(c)] else 'c not<=lam(c)', 'lam(c)=A' if M.lam(c)==A else '', 'lam(a)=A' if M.lam(a)==A else '')
            C[key]+=1
            if len(ex)<6: ex.append((M.src,x,y,r[1],d))
for k,v in sorted(C.items(), key=lambda t:str(t[0])): print(' ',v,k)
print(ex)
