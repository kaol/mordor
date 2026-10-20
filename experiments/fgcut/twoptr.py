"""Two-pointer lemma on bounded posets P1, P2: monotone f: P1×P2→P1, g: P1×P2→P2 with no interior witness
(x≠⊥, y≠⊤: x ≰ f, g ≰ y). `forbid(x,y)` says where (f,g)=(⊥,⊤) is excluded; UNSAT = the lemma with that conclusion."""
import sys, itertools
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'sat'))
import lat
from pysat.solvers import Cadical153

class P:
    def __init__(s, n, rel, name):
        leq = [[x == y for y in range(n)] for x in range(n)]
        for x, y in rel: leq[x][y] = True
        for k in range(n):
            for i in range(n):
                if leq[i][k]:
                    for j in range(n):
                        if leq[k][j]: leq[i][j] = True
        s.n, s.leq, s.name = n, leq, name
        s.bot = next(x for x in range(n) if all(leq[x][y] for y in range(n)))
        s.top = next(x for x in range(n) if all(leq[y][x] for y in range(n)))
bowtie = P(6, [(0,2),(0,3),(2,4),(2,5),(3,4),(3,5),(4,1),(5,1)], 'bowtie')
W = P(7, [(0,2),(0,3),(0,4),(2,5),(3,5),(3,6),(4,6),(5,1),(6,1)], 'W')
Mp = P(7, [(0,2),(0,3),(2,4),(3,4),(2,5),(3,6),(4,1),(5,1),(6,1)], 'M')
def atoms(L): return [x for x in range(L.n) if x != L.bot and not any(z not in (L.bot, x) and L.leq[z][x] for z in range(L.n))]
def coatoms(L): return [y for y in range(L.n) if y != L.top and not any(z not in (L.top, y) and L.leq[y][z] for z in range(L.n))]

def test(L1, L2, forbid, model=False):
    n1, n2 = L1.n, L2.n; cells = [(x, y) for x in range(n1) for y in range(n2)]
    v = {}
    def var(k):
        if k not in v: v[k] = len(v) + 1
        return v[k]
    S = Cadical153()
    for c in cells:
        S.add_clause([var(('f', c, a)) for a in range(n1)]); S.add_clause([var(('g', c, b)) for b in range(n2)])
        for a, a2 in itertools.combinations(range(n1), 2): S.add_clause([-var(('f', c, a)), -var(('f', c, a2))])
        for b, b2 in itertools.combinations(range(n2), 2): S.add_clause([-var(('g', c, b)), -var(('g', c, b2))])
        x, y = c
        if x != L1.bot and y != L2.top:
            for a in range(n1):
                if L1.leq[x][a]: S.add_clause([-var(('f', c, a))])
            for b in range(n2):
                if L2.leq[b][y]: S.add_clause([-var(('g', c, b))])
            if forbid(x, y): S.add_clause([-var(('f', c, L1.bot)), -var(('g', c, L2.top))])
    for c in cells:
        for c2 in cells:
            if c != c2 and L1.leq[c[0]][c2[0]] and L2.leq[c[1]][c2[1]]:
                for a in range(n1):
                    for a2 in range(n1):
                        if not L1.leq[a][a2]: S.add_clause([-var(('f', c, a)), -var(('f', c2, a2))])
                for b in range(n2):
                    for b2 in range(n2):
                        if not L2.leq[b][b2]: S.add_clause([-var(('g', c, b)), -var(('g', c2, b2))])
    r = S.solve()
    if r and model:
        m = set(l for l in S.get_model() if l > 0)
        return {c: (next(a for a in range(n1) if var(('f', c, a)) in m), next(b for b in range(n2) if var(('g', c, b)) in m)) for c in cells}
    return r

if __name__ == '__main__':
    Ps = [lat.chain(3), lat.powerset(2), lat.M(3), lat.N5(), bowtie, W, Mp, lat.powerset(3)]
    for mode in ['all', 'atom-coatom', 'fix-coatom', 'fix-atom']:
        print(mode)
        for A in Ps:
            row = []
            for B in Ps:
                at, co = atoms(A), coatoms(B)
                fb = {'all': lambda x, y: True, 'atom-coatom': lambda x, y: x in at and y in co,
                      'fix-coatom': lambda x, y: y == co[0], 'fix-atom': lambda x, y: x == at[0]}[mode]
                row.append(B.name + ':' + ('SAT' if test(A, B, fb) else 'unsat'))
            print('  ', A.name, ' '.join(row), flush=True)
