"""Print a stored model (sets, F) and, for every row of Z, its (T) violations: Tb cells (F(x,y) <= x, h(y) >= 3) and
Ta cells (y <= F(x,y), h(y) >= 3), plus descent, landing, mu.  Reads only the JSON given."""
import sys, os, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'amalg'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'separation'))
import bank
from rstages import a_of
for fn in sys.argv[1:]:
    mf = json.load(open(fn)); mf = mf[0] if isinstance(mf, list) else mf
    m = bank.M(mf['sets'], mf['F']); L = m.L; h = m.h; F = m.F; n = m.n; le = m.le
    print(fn, 'n', n, 'H', L.height, 'branch', m.branch, 'd', m.d, 'N', m.N, 'relax', mf.get('relaxation'))
    print(' heights', {x: h[x] for x in range(n)})
    print(' covers', [(x, y) for x in range(n) for y in L.covers_up[x]])
    print(' Z', m.Z, 'atoms', m.atoms, 'M2', m.M2, 'bot-desc', m.desc(m.bot))
    for x in m.Z:
        tb = [(y, F[x][y]) for y in range(n) if h[y] >= 3 and le[F[x][y]][x]]
        ta = [(y, F[x][y]) for y in range(n) if h[y] >= 3 and le[y][F[x][y]]]
        print(f'  row {x} h{h[x]} desc {m.desc(x)} lam {m.lam(x)} mu {m.mu(x)} a {a_of(L, F, x)} | Tb-viol {tb} Ta-viol {ta}')
    print(' height-2 outside Z with F(bot,p):', [(p, F[m.bot][p]) for p in range(n) if h[p] == 2 and p not in m.Z])
