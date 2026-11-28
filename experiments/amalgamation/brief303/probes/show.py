"""Print the colour/landing anatomy of stored W-models: colours, lambda, K, pair-joins, C(m), C'(m), lambda(m)."""
from alib import *
import sys, json
def show(M):
    le=M.le; h=M.h
    print('src',M.src,'n',M.n,'H',h[M.top],'cols',M.cols,'Z',M.Z)
    print(' sets',[bin(s)[2:] for s in M.sets])
    for x in [M.bot]+M.atoms+[z for z in M.Z if h[z]==2]:
        p=M.lam(x)
        tag='col' if x in M.cols else ('pj' if x in M.pjs else ('bot' if x==M.bot else ('atom' if h[x]==1 else 'm2')))
        print(f'  row {x:3d} {tag:4s} lam={p} h={h[p] if p is not None else None} inZ={p in M.Zs if p is not None else None} K={M.K(x)} desc={M.desc(x)} C(x)={M.C(x)} Cp={Cp(M,x) if h[x]==2 else ""}', end='')
        if p is not None and p not in M.Zs: print(' exit', M.phi[p], end='')
        print()
if __name__=='__main__':
    for f in sys.argv[1:]:
        D=json.load(open(f)); D=D if isinstance(D,list) else [D]
        for d in D: show(Mod(d['sets'],d['F'],f))
