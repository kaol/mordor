"""Free replay (no search) of two statements.
CrossPair (all distinct stored models with ZT): colours a != b, m = a v b in Z (height 2), b <= lambda(a), a <= lambda(b),
  Tb at rows a and b, row m lands  ==>  lambda(m) = m.
CrossExists (stored relaxed-world models, pairselfM predicate): some colours a != b with a v b in Z, b <= lambda(a),
  a <= lambda(b)."""
import collections
from mlib import load_all, tb_at
from wlib import relaxed
ms=load_all(['holding/*.json','bank/*.json','brief*/**/*.json','direct*/**/*.json','*.json'])
C=collections.Counter(); viol=[]
for M in ms:
    h=M.h; le=M.le; n=M.n
    if any(M.phi[y]==M.bot for y in range(n) if h[y]>2): continue
    for a in M.cols:
        for b in M.cols:
            if a>=b: continue
            m=M.join[a][b]
            if m not in M.Zs or h[m]!=2: continue
            la,lb,lm=M.lam(a),M.lam(b),M.lam(m)
            if la is None or lb is None or lm is None: continue
            if not (le[b][la] and le[a][lb]): continue
            tb=tb_at(M,a) and tb_at(M,b)
            kind='lam(a)=lam(b)=m' if la==m==lb else ('swap' if la==b and lb==a else ('one lands at m' if m in (la,lb) else 'other'))
            C[('Tb a,b' if tb else 'no Tb', 'holds' if lm==m else 'FAILS', kind, 'nofix' if M.nofix() else 'fix')]+=1
            if tb and lm!=m: viol.append((M.src,a,b,m,lm))
for k,v in sorted(C.items(), key=lambda t:str(t[0])): print(' ',v,k)
print('CrossPair violations with Tb:', len(viol), viol[:8])
R=relaxed(); E=collections.Counter()
for M in R:
    le=M.le
    cr=[(a,b) for a in M.cols for b in M.cols if a<b and M.join[a][b] in M.Zs and le[b][M.lam(a)] and le[a][M.lam(b)]]
    E['cross pair exists' if cr else 'NO cross pair']+=1
print('CrossExists on', len(R), 'relaxed models:', dict(E))
