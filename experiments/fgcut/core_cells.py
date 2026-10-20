"""Minimal sets of cells needed for the labelling contradiction (selector per cell, deletion-based MUS)."""
import sys, itertools
from pysat.solvers import Cadical153
from labelling import subsets

def build(k, l, keep):
    As, Bs = subsets(k), subsets(l); cells = [c for c in ((A, B) for A in As for B in Bs) if c in keep]
    v = {}; nv = [0]
    def var(key):
        if key not in v: nv[0] += 1; v[key] = nv[0]
        return v[key]
    S = Cadical153()
    for c in cells:
        A, B = c; d = var(('D', c))
        a = [var(('a', c, i)) for i in range(k)]; b = [var(('b', c, j)) for j in range(l)]
        S.add_clause([-d] + a); S.add_clause([-d] + [-a[i] for i in A])
        S.add_clause([d] + b); S.add_clause([d] + [-b[j] for j in B])
        for x in a: S.add_clause([-x, d])
        for x in b: S.add_clause([-x, -d])
    for c in cells:
        for c2 in cells:
            (A, B), (A2, B2) = c, c2
            if c != c2 and A >= A2 and B <= B2:
                for i in range(k): S.add_clause([-var(('a', c2, i)), var(('a', c, i))])
                for j in range(l): S.add_clause([-var(('b', c, j)), var(('b', c2, j))])
    return S.solve()

def mus(k, l):
    keep = set((A, B) for A in subsets(k) for B in subsets(l))
    for c in sorted(keep, key=lambda c: (-len(c[0]) - len(c[1]))):
        trial = keep - {c}
        if not build(k, l, trial): keep = trial
    return keep

fmt = lambda S, nm: '{' + ','.join(nm + str(i + 1) for i in sorted(S)) + '}'
for k, l in [(2, 1), (2, 2), (3, 1), (3, 2), (3, 3)]:
    K = mus(k, l)
    print(f"({k},{l}): {len(K)} cells:", ' '.join(f"({fmt(A,'p')},{fmt(B,'u')})" for A, B in sorted(K, key=lambda c: (len(c[0]), sorted(c[0]), len(c[1]), sorted(c[1])))), flush=True)
