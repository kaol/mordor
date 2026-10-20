"""Labelling variants (log §34.3m): without D/U exclusivity, and with boundary cells A = ∅ or B = ∅ added. Both stay UNSAT."""
import sys, itertools
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pysat.solvers import Cadical153
from labelling import subsets

def solve(k, l, excl=True, boundary=False, gen=True):
    allA = subsets(k) + ([frozenset()] if boundary else []); allB = subsets(l) + ([frozenset()] if boundary else [])
    cells = [(A, B) for A in allA for B in allB]
    v = {}
    def var(key):
        if key not in v: v[key] = len(v) + 1
        return v[key]
    S = Cadical153()
    for c in cells:
        A, B = c; d = var(('D', c))
        a = [var(('a', c, i)) for i in range(k)]; b = [var(('b', c, j)) for j in range(l)]
        if gen: S.add_clause([-d] + a); S.add_clause([d] + b)
        if A and B:
            S.add_clause([-a[i] for i in A]); S.add_clause([-b[j] for j in B])
        if excl:
            for x in a: S.add_clause([-x, d])
            for x in b: S.add_clause([-x, -d])
    for c in cells:
        for c2 in cells:
            (A, B), (A2, B2) = c, c2
            if c != c2 and A >= A2 and B <= B2:
                for i in range(k): S.add_clause([-var(('a', c2, i)), var(('a', c, i))])
                for j in range(l): S.add_clause([-var(('b', c, j)), var(('b', c2, j))])
    r = S.solve()
    return r, S.get_model() if r else None, v

for k, l in [(1,1),(2,1),(1,2),(2,2),(3,2),(2,3),(3,3)]:
    print((k, l), 'noexcl:', 'SAT' if solve(k, l, excl=False)[0] else 'UNSAT', ' boundary:', 'SAT' if solve(k, l, boundary=True)[0] else 'UNSAT')
