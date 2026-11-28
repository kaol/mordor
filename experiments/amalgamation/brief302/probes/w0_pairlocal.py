"""Free analysis (no search) on every distinct stored W0 model (W0 checked via (T): a(bot)=bot, ZT, n1, Ta and Tb at
every row of Z).  PairLocal instances: colours c0 != c', m = c0 v c' in Z, lambda(c0) = m, c0 <= lambda(c').
In W0 lambda(m) != m always, so every instance must be paid for by a mu-fixed atom (PairLocal says so).
Records: where the fixed atoms q are (q = c0, q = c', q in C(m), q below lambda(c') ...), ColourGain at c0, c'."""
import collections, pickle
from mlib import load_all
ms=load_all(['holding/*.json','bank/*.json','brief*/**/*.json','direct*/**/*.json','*.json'])
W=[M for M in ms if M.w0()]
print('distinct models',len(ms),'W0 models',len(W))
pickle.dump([(M.src,M.sets,M.F) for M in W], open('w0_models.pkl','wb'))
C=collections.Counter()
for M in W:
    le=M.le
    fx=[q for q in M.atoms if M.fixed(q)]
    for c0 in M.cols:
        m=M.lam(c0)
        if m not in M.pjs or not le[c0][m]: continue
        for c1 in M.C(m):
            if c1==c0 or not le[c0][M.lam(c1)]: continue
            n=M.lam(c1)
            where=tuple(sorted(set(('c0' if q==c0 else "c'" if q==c1 else 'in C(lam(c\'))' if le[q][n] else 'colour' if q in M.cols else 'atom') for q in fx)))
            cg0=any(le[g][m] and not le[g][c0] for g in M.cols); cg1=any(le[g][n] and not le[g][c1] for g in M.cols)
            C[('n=m' if n==m else ('n in Z' if n in M.Zs else 'n exits to '+('c0' if M.phi[n]==c0 else 'other')), 'fixed:'+str(where), 'CG c0' if cg0 else 'no CG c0', "CG c'" if cg1 else "no CG c'", 'nofix' if not fx else 'fix')]+=1
for k,v in sorted(C.items(), key=lambda t:-t[1]): print(' ',v,k)
