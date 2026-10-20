"""Which monotonicity directions the labelling lemma needs (log §34.3m): dropping any one makes (2,2) satisfiable."""
import sys, itertools
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pysat.solvers import Cadical153
from labelling import subsets

def solve(k, l, aA=True, aB=True, bA=True, bB=True):
    cells = [(A, B) for A in subsets(k) for B in subsets(l)]
    v = {}
    def var(key):
        if key not in v: v[key] = len(v) + 1
        return v[key]
    S = Cadical153()
    for c in cells:
        A, B = c
        a = [var(('a', c, i)) for i in range(k)]; b = [var(('b', c, j)) for j in range(l)]
        S.add_clause(a + b)
        S.add_clause([-a[i] for i in A]); S.add_clause([-b[j] for j in B])
    for c in cells:
        for c2 in cells:
            (A, B), (A2, B2) = c, c2
            if c == c2 or not (A >= A2 and B <= B2): continue
            # c <= c2 : alpha(c) ⊇ alpha(c2), beta(c) ⊆ beta(c2)
            okA = (B == B2 and aA) or (A == A2 and aB) or (aA and aB)
            okB = (B == B2 and bA) or (A == A2 and bB) or (bA and bB)
            if okA:
                for i in range(k): S.add_clause([-var(('a', c2, i)), var(('a', c, i))])
            if okB:
                for j in range(l): S.add_clause([-var(('b', c, j)), var(('b', c2, j))])
    return S.solve()

for name, kw in [('alpha only in A', dict(aB=False)), ('alpha only in B', dict(aA=False)),
                 ('alpha in A, beta in B', dict(aB=False, bA=False)), ('alpha in B, beta in A', dict(aA=False, bB=False))]:
    print(name, [(k, l, 'SAT' if solve(k, l, **kw) else 'UNSAT') for k, l in [(1,1),(2,1),(1,2),(2,2),(3,2),(2,3),(3,3)]])
