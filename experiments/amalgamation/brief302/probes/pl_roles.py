"""Free analysis, all distinct stored models with a(bot)=bot, ZT: role of Tb at c0 vs Tb at c' in PairLocal_raw
(lambda(c0) = m = c0 v c' in Z, c0 <= lambda(c'), rows c', m land  ==> lambda(m) <= m)."""
import collections
from mlib import load_all, tb_at
from rstages import a_of
ms=load_all(['holding/*.json','bank/*.json','brief*/**/*.json','direct*/**/*.json','*.json'])
C=collections.Counter()
for M in ms:
    h=M.h; le=M.le
    if a_of(M.L,M.F,M.bot)!=M.bot or any(h[z]>2 for z in M.Z): continue
    for c0 in M.cols:
        m=M.lam(c0)
        if m is None or m not in M.Zs or h[m]!=2 or not le[c0][m]: continue
        lm=M.lam(m)
        if lm is None: continue
        for c1 in M.C(m):
            if c1==c0: continue
            n=M.lam(c1)
            if n is None: continue
            C[('c0<=lam(c\')' if le[c0][n] else 'c0 not<=lam(c\')', 'Tb c0' if tb_at(M,c0) else '-', "Tb c'" if tb_at(M,c1) else '-', 'holds' if le[lm][m] else 'FAILS')]+=1
for k,v in sorted(C.items(), key=lambda t:str(t[0])): print(' ',v,k)
