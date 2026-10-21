"""Zones with tameness (see zones_check.py for the base model).

A value class (k, p, q) -- an S_k value at a cell with row layer p, column layer q --
is *tame* (finitely many values, or none) when
  T1  k <= p and q <= k                      (core; core_finite, or no such cells)
  T2  k <= p and some j outside Ne has j <= q (wall: z >= G(s_k, s_j), and G(s_k,s_j) has
                                              first coordinate != bot or a layer not <= k)
  T3  q <= k and some j in Fu has p <= j      (dual wall: z <= G(t_j, t_k))
Tame values lie in the guide set, so they need no zone and cause no conflict.
"""
import itertools, sys
from z3 import Bool, Solver, Not, And, sat
exec(open(__file__.replace('zones2.py', 'zones_check.py')).read().replace('if __name__ == "__main__"', 'if False'))

def solve_tame(K, le, name, extra_tame=None):
    bot = [a for a in K if all(le(a, b) for b in K)][0]
    top = [a for a in K if all(le(b, a) for b in K)][0]
    mid = [k for k in K if k not in (bot, top)]
    ds = downsets(K, le); bad = []
    for Fu in ds:
        for Ne in ds:
            if not Fu <= Ne or bot not in Ne or top in Fu: continue
            cells = [(p, q) for p in Ne for q in K if q not in Fu]
            def tame(k, c):
                p, q = c
                if le(k, p) and le(q, k): return True
                if le(k, p) and any(le(j, q) for j in K if j not in Ne): return True
                if le(q, k) and any(le(p, j) for j in Fu): return True
                return bool(extra_tame and extra_tame(k, c, Fu, Ne))
            s = Solver(); var = {}
            def zone(k, c):
                if tame(k, c): return 'T'
                p, q = c
                lo, ra = not le(k, p), not le(q, k)
                if lo and not ra: return 'L'
                if ra and not lo: return 'R'
                if (k, c) not in var: var[(k, c)] = Bool(f"low_{k}_{c}")
                return var[(k, c)]
            isL = lambda k, c: (lambda z: z if not isinstance(z, str) else z == 'L')(zone(k, c))
            isR = lambda k, c: (lambda z: Not(z) if not isinstance(z, str) else z == 'R')(zone(k, c))
            cle = lambda c, d: le(c[0], d[0]) and le(c[1], d[1])
            for k in mid:
                for k2 in mid:
                    if not le(k, k2): continue
                    for c in cells:
                        for d in cells:
                            if not cle(c, d): continue
                            if k != k2 and le(k, c[0]) and le(d[1], k2): continue
                            s.add(Not(And(isR(k, c), isL(k2, d))))
            if s.check() != sat: bad.append((sorted(Fu), sorted(Ne)))
    print(name, "all cut types OK" if not bad else f"{len(bad)} bad: {bad[:8]}")
    return bad

if __name__ == "__main__":
    for n in range(3, 9): solve_tame(*chain(n), f"C{n}")
    solve_tame(*boolean(3), "B3")
    C3sq = list(itertools.product(range(3), range(3)))
    solve_tame(C3sq, lambda a, b: a[0] <= b[0] and a[1] <= b[1], "C3xC3")
