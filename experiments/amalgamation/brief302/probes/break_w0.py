"""Free analysis (no search): SCL breaks (x colour row, y colour or pair-join row) in stored W0 models (all have a
mu-fixed atom).  BreakSelfCol: break at corner A ==> lambda(A) <= A or some colour u <= A has lambda(u) = A.
In W0 lambda(A) <= A is impossible.  For W0 breaks violating BreakSelfCol: where is the fixed atom q (q in {c, a, x},
q below A, lambda(q) vs A), and does ColourGain fail at x or y."""
import collections, pickle
from mlib import Mod, scl_walk
ms=[Mod(s,F,src) for (src,s,F) in pickle.load(open('w0_models.pkl','rb'))]
C=collections.Counter()
for M in ms:
    le=M.le
    if not M.pjs: continue
    fx=[q for q in M.atoms if M.fixed(q)]
    for x in M.cols:
        for y in M.cols+M.pjs:
            r=scl_walk(M,x,y)
            if not r or r[0]!='break': continue
            A=r[2]['A']; a=r[2]['e']; c=r[2]['carried'][0]
            bsc = le[M.lam(A)][A] or any(M.lam(u)==A for u in M.C(A))
            cgx=any(le[g][M.lam(x)] and not le[g][x] for g in M.cols); cgy=any(le[g][M.lam(y)] and not le[g][y] for g in M.cols)
            rel=tuple(sorted(set(('q=c' if q==c else 'q=a' if q==a else 'q=x' if q==x else 'q<=A' if le[q][A] else 'q<=lam(y)' if le[q][M.lam(y)] else 'q other') for q in fx)))
            C[('BSC holds' if bsc else 'BSC fails', rel, 'CG x' if cgx else 'noCG x', 'CG y' if cgy else 'noCG y')]+=1
for k,v in sorted(C.items(), key=lambda t:-t[1]): print(' ',v,k)
