"""Free replay (no search) of the paper lemma SelfLand on every distinct stored model with ZT (high elements have
F(bot, .) != bot):  q an atom, Tb at row q (F(q, B) not <= q for every high B), lambda(q) = p of height 2 with q < p;
y any element with y >= q whose row lands and q <= lambda(y).  Claim: lambda(y) = p.
No other hypothesis (no a(bot) = bot, no NoFix, no ColourGain).  Prints instances, violations (must be 0)."""
import collections
from mlib import load_all, tb_at
ms=load_all(['holding/*.json','bank/*.json','brief*/**/*.json','direct*/**/*.json','*.json'])
C=collections.Counter(); viol=[]
for M in ms:
    h=M.h; le=M.le; n=M.n
    if any(M.phi[y]==M.bot for y in range(n) if h[y]>2): continue
    C['models (ZT)']+=1
    for q in range(n):
        if h[q]!=1 or not tb_at(M,q): continue
        p=M.lam(q)
        if p is None or h[p]!=2 or not le[q][p]: continue
        for y in range(n):
            if not le[q][y] or y==q: continue
            ly=M.lam(y)
            if ly is None or not le[q][ly]: continue
            C[('inst','y in Z' if y in M.Zs else 'y not in Z','p in Z' if p in M.Zs else 'p exits')]+=1
            if ly!=p: viol.append((M.src,q,p,y,ly))
for k,v in sorted(C.items(), key=lambda t:str(t[0])): print(' ',v,k)
print('violations', len(viol), viol[:10])
