"""Free analysis over all distinct stored models with a(bot)=bot and ZT: the raw local statement
PairLocal_raw: colours c0 != c', m = c0 v c' in Z, lambda(c0) = m, c' and c0 land, c0 <= lambda(c'), Tb at rows c0 and c'
  ==> lambda(m) <= m.   Reports failures by which extra hypotheses hold (NoFix, Tb at m)."""
import collections
from mlib import load_all, tb_at
from rstages import a_of
ms=load_all(['holding/*.json','bank/*.json','brief*/**/*.json','direct*/**/*.json','*.json'])
C=collections.Counter(); bad=[]
for M in ms:
    h=M.h; le=M.le
    if a_of(M.L,M.F,M.bot)!=M.bot or any(h[z]>2 for z in M.Z): continue
    for c0 in M.cols:
        m=M.lam(c0)
        if m is None or m not in M.Zs or h[m]!=2 or not le[c0][m]: continue
        for c1 in M.C(m):
            if c1==c0: continue
            n=M.lam(c1)
            if n is None or not le[c0][n]: continue
            tb=tb_at(M,c0) and tb_at(M,c1)
            lm=M.lam(m)
            ok = lm is not None and le[lm][m]
            C[('Tb c0,c\'' if tb else 'no Tb', 'holds' if ok else 'FAILS', 'nofix' if M.nofix() else 'fix', 'Tb m' if tb_at(M,m) else 'no Tb m', 'lam(m) None' if lm is None else '')]+=1
            if tb and not ok: bad.append((M.src,c0,c1,m))
for k,v in sorted(C.items(), key=lambda t:str(t[0])): print(' ',v,k)
print('failures with Tb at c0,c\':', len(bad), bad[:8])
