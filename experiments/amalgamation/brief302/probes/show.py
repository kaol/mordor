"""Print one stored model in full detail (read-only)."""
import sys
from mlib import load_all
def show(M, rows=None):
    le=M.le; h=M.h
    print(f'{M.src} n={M.n} H={h[M.top]} cols={M.cols} pjs={M.pjs} Z={M.Z} atomsZ={M.atoms} nofix={M.nofix()} unb={M.unb()}')
    print('  elements by height:', {k:[x for x in range(M.n) if h[x]==k] for k in range(h[M.top]+1)})
    print('  covers (x: up-covers):', {x:M.L.covers_up[x] for x in range(M.n) if h[x]<=3})
    print('  phi:', {y:M.phi[y] for y in range(M.n)})
    for x in (rows or (M.Z)):
        d=M.desc(x); i=M.lidx(x)
        print(f'  row {x} h{h[x]} C{M.C(x)}: desc {d} lam={M.lam(x)} idx={i} K={M.K(x)} exit={M.phi[M.lam(x)] if M.lam(x) is not None and M.lam(x) not in M.Zs else None}')
if __name__=='__main__':
    ms=load_all([sys.argv[1]]); k=int(sys.argv[2]); show(ms[k])
