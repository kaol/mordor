"""Free replay over all distinct stored models with ZT: SwapPair -- atoms a != b of Z with Tb at rows a and b,
lambda(a) = b, lambda(b) = a, m = a v b in Z (height 2) and row m lands  ==>  lambda(m) = m.  Also the one-sided
variant lambda(a) = b, b <= ... recorded by kind."""
import collections
from mlib import load_all, tb_at
ms=load_all(['holding/*.json','bank/*.json','brief*/**/*.json','direct*/**/*.json','*.json'])
C=collections.Counter(); viol=[]
for M in ms:
    h=M.h; le=M.le; n=M.n
    if any(M.phi[y]==M.bot for y in range(n) if h[y]>2): continue
    at=[q for q in M.atoms]
    for a in at:
        for b in at:
            if a>=b: continue
            if M.lam(a)!=b or M.lam(b)!=a: continue
            m=M.join[a][b]
            if m not in M.Zs or h[m]!=2 or M.lam(m) is None: continue
            tb=tb_at(M,a) and tb_at(M,b)
            ok=M.lam(m)==m
            C[('Tb a,b' if tb else 'no Tb', 'holds' if ok else 'FAILS', 'nofix' if M.nofix() else 'fix')]+=1
            if tb and not ok: viol.append((M.src,a,b,m,M.lam(m)))
for k,v in sorted(C.items(), key=lambda t:str(t[0])): print(' ',v,k)
print('violations with Tb', len(viol), viol[:6])
