"""Free analysis (no search), stored W0 models: at each SCL break (x colour, y colour or pair-join; corner A = c v a,
c carried in K(y), a = boundary value outside K(y)), describe the rows c and a: their landings relative to A, c, a,
and their exits (fixed = exit to itself)."""
import collections, pickle
from mlib import Mod, scl_walk
ms=[Mod(s,F,src) for (src,s,F) in pickle.load(open('w0_models.pkl','rb'))]
C=collections.Counter()
def desc(M,u,A,c,a):
    p=M.lam(u); le=M.le
    s='Z' if p in M.Zs else ('exit->'+('c' if M.phi[p]==c else 'a' if M.phi[p]==a else 'other'))
    return s+(' lam=A' if p==A else '')+(' >=c' if le[c][p] else '')+(' >=a' if le[a][p] else '')
for M in ms:
    if not M.pjs: continue
    for x in M.cols:
        for y in M.cols:
            r=scl_walk(M,x,y)
            if not r or r[0]!='break': continue
            A=r[2]['A']; a=r[2]['e']; c=r[2]['carried'][0]
            C[('row c: '+desc(M,c,A,c,a), 'row a: '+desc(M,a,A,c,a), 'y exits' if M.lam(y) not in M.Zs else 'y in Z', 'x=c' if x==c else 'x=a' if x==a else 'x other')]+=1
for k,v in sorted(C.items(), key=lambda t:-t[1]): print(' ',v,k)
