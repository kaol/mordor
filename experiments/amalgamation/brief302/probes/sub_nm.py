"""Free analysis, relaxed-world models: instances c0, c' colours, m = c0 v c' in Z, lambda(c0) = m, c0 <= lambda(c').
Records F(c0,m), F(c',m), F(m,m) (as 'bot', 'c0', "c'", 'm', other), landing indices, and whether the joint row
G = F(c0,.) v F(c',.) has m below its gfp."""
import collections
from wlib import relaxed
C=collections.Counter()
def nm(M,v,c0,c1,m):
    return 'bot' if v==M.bot else 'c0' if v==c0 else "c'" if v==c1 else 'm' if v==m else ('atom' if M.h[v]==1 else 'h%d'%M.h[v])
for M in relaxed():
    le=M.le; F=M.F; n=M.n
    for c0 in M.cols:
        m=M.lam(c0)
        if m not in M.pjs or not le[c0][m]: continue
        for c1 in M.C(m):
            if c1==c0 or not le[c0][M.lam(c1)]: continue
            g=M.top; seen=[]
            while g not in seen: seen.append(g); g=M.join[F[c0][g]][F[c1][g]]
            gf=seen[-1]
            key=('lam(c1)=m' if M.lam(c1)==m else 'lam(c1)!=m', 'F(c0,m)='+nm(M,F[c0][m],c0,c1,m), "F(c',m)="+nm(M,F[c1][m],c0,c1,m), 'F(m,m)='+nm(M,F[m][m],c0,c1,m),
                 'm<=gfpG' if le[m][gf] else 'm not<=gfpG', 'i(m) vs i0,i1: %s'%('>' if M.lidx(m)>max(M.lidx(c0),M.lidx(c1)) else '<=max'))
            C[key]+=1
for k,v in sorted(C.items(), key=lambda t:-t[1]): print(' ',v,k)
