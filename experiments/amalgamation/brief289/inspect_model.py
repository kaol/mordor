import sys, os, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'amalg'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'separation'))
import bank
from rstages import a_of
def show(m):
    L=m.L; h=m.h; n=m.n
    print('n',n,'H',L.height,'bot',m.bot,'top',m.top,'branch',m.branch,'d',m.d,'N',m.N)
    print('heights', {x:h[x] for x in range(n)})
    cov=[(x,y) for x in range(n) for y in range(n) if m.le[x][y] and x!=y and h[y]==h[x]+1]
    print('covers', cov)
    print('Z',m.Z,'atoms',m.atoms,'M2',m.M2)
    print('bot-desc', m.desc(m.bot))
    for x in m.Z:
        print(f' row {x} (h{h[x]}): desc {m.desc(x)} lam {m.lam(x)} idx {m.lidx(x)} exits {m.exits(x)} mu {m.mu(x)} a {a_of(L,m.F,x)} good {m.good(x)} fixed {m.fixed(x)}')
    hi2=[p for p in range(n) if h[p]==2 and p not in m.Z]
    print('height-2 outside Z:', [(p, m.F[m.bot][p]) for p in hi2])
if __name__=='__main__':
    for f in sys.argv[1:]:
        ms=json.load(open(f)); ms = ms if isinstance(ms,list) else [ms]
        for mf in ms:
            m=bank.M(mf['sets'],mf['F']); show(m); print()
