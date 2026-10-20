"""Kernel-lemma test (Cat Bialgebra E19 ↔ Cut on products; log §34.3u).

On a finite product L = L1 × L2, look for a monotone F and a cut D such that no witness (x ∈ D, y ∉ D,
F(x, y) ≤ x or y ≤ F(x, y)) lies on an axis-parallel slice (x1 = y1 or x2 = y2). Finite Cut (cl_finite) guarantees
some witness, so if SAT, every witness is "mixed": no reduction that solves Cut inside slices {·} × L2 / L1 × {·} of
a product can work in general. Variants:
  mode 'slice'   : forbid witnesses with x1 = y1 or x2 = y2;
  mode 'coord'   : forbid witnesses with x, y comparable in some coordinate (x1 ≤≥ y1 or x2 ≤≥ y2).
M3 × M3 has 4386 cuts; a fixed random sample of 40 is tested.

Results (cuts admitting F with no witness of the forbidden kind):
  slice: C2×C2 2/4, C3×C3 14/18, M3×C2 35/44, M3×M3 40/40 sampled.
  coord: M3×C2 0/44 (vacuous: every pair is comparable in the C2 coordinate), M3×M3 0/40 sampled.
Monotonicity uses the order encoding g(c, u) ⟺ u ≤ F(c); a one-hot pairwise encoding gave identical counts.
"""
import itertools, sys
from pysat.solvers import Cadical153

def chain(k): return list(range(k)), lambda a, b: a <= b

def m3():
    E = ['0', 'a', 'b', 'c', '1']
    return E, lambda x, y: x == y or x == '0' or y == '1'

def product(L1, L2):
    E1, le1 = L1; E2, le2 = L2
    E = [(a, b) for a in E1 for b in E2]
    return E, lambda x, y: le1(x[0], y[0]) and le2(x[1], y[1])

def downsets(E, le):
    """all down-sets D with ⊥ ∈ D, ⊤ ∉ D, by recursion along a linear extension."""
    bot = [e for e in E if all(le(e, f) for f in E)][0]; top = [e for e in E if all(le(f, e) for f in E)][0]
    order = sorted([e for e in E if e not in (bot, top)], key=lambda e: sum(1 for f in E if le(f, e)))
    def rec(i, D):
        if i == len(order): yield set(D); return
        e = order[i]
        yield from rec(i + 1, D)
        if all(f in D for f in E if le(f, e) and f != e): yield from rec(i + 1, D | {e})
    yield from rec(0, {bot})

def search(E, le, mode, le1c=None, le2c=None, sample=None):
    n = len(E); idx = {e: i for i, e in enumerate(E)}
    cells = [(x, y) for x in E for y in E]; cellset = set(cells)
    covers = [(a, b) for a in E for b in E if a != b and le(a, b) and not any(c not in (a, b) and le(a, c) and le(c, b) for c in E)]
    def forbidden(x, y):
        if mode == 'slice': return x[0] == y[0] or x[1] == y[1]
        return le1c(x[0], y[0]) or le1c(y[0], x[0]) or le2c(x[1], y[1]) or le2c(y[1], x[1])
    found, total, shown = 0, 0, []
    cuts = list(downsets(E, le))
    if sample:
        import random; random.Random(0).shuffle(cuts); cuts = cuts[:sample]
    for D in cuts:
        s = Cadical153(); var = {}
        v = lambda c, u: var.setdefault((c, u), len(var) + 1)
        for c in cells:
            s.add_clause([v(c, u) for u in range(n)])
            for u, w in itertools.combinations(range(n), 2): s.add_clause([-v(c, u), -v(c, w)])
        # order encoding: g(c, u) ⟺ E[u] ≤ F(c); then F(c) ≤ F(c') ⟺ ∀u. g(c, u) → g(c', u)
        g = lambda c, u: var.setdefault(('g', c, u), len(var) + 1)
        for c in cells:
            for u in range(n):
                ups = [w for w in range(n) if le(E[u], E[w])]
                for w in ups: s.add_clause([-v(c, w), g(c, u)])
                s.add_clause([-g(c, u)] + [v(c, w) for w in ups])
        for (x, y) in cells:   # monotone along covers in each argument
            for (a, b) in covers:
                for c1, c2 in (((a, y), (b, y)), ((x, a), (x, b))):
                    if c1 in cellset and c2 in cellset:
                        for u in range(n): s.add_clause([-g(c1, u), g(c2, u)])
        for (x, y) in cells:
            if x in D and y not in D and forbidden(x, y):
                for u in range(n):
                    if le(E[u], x) or le(y, E[u]): s.add_clause([-v((x, y), u)])
        if s.solve():
            m = set(l for l in s.get_model() if l > 0)
            F = {key[0]: E[key[1]] for key, k in var.items() if k in m and key[0] != 'g'}
            wit = [(x, y) for x in E for y in E if x in D and y not in D and (le(F[(x, y)], x) or le(y, F[(x, y)]))]
            found += 1
            if len(D) >= 3 and found <= 50 and not shown:
                print('    e.g. D =', sorted(D, key=str), ' witnesses only at', wit[:3]); shown.append(1)
        total += 1
        s.delete()
    return found, total

if __name__ == '__main__':
    cases = [('C2 x C2', chain(2), chain(2)), ('C3 x C3', chain(3), chain(3)), ('M3 x C2', m3(), chain(2)),
             ('M3 x M3', m3(), m3())]
    for name, L1, L2 in cases:
        E, le = product(L1, L2)
        for mode in ('slice', 'coord'):
            if mode == 'coord' and name.startswith('C'): continue
            f, t = search(E, le, mode, L1[1], L2[1], sample=40 if name == 'M3 x M3' else None)
            print(f'{name} mode={mode}: {f} of {t} cuts admit F with no witness of that kind')
