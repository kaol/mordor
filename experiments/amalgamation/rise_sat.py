"""Exact test of the Rise conjecture (log §34.3z¹⁵⁷).

Rise(F): b(⊤) ≠ ⊤, or x ↦ F(x, x) has a fixed point ∉ {⊥, ⊤}, or some good x (x ∈ R_{h(x)}) has x < a(x).
(x = ⊥ covers a(⊥) ≠ ⊥.) With the lower heights, each alternative gives ⊤ ∈ R_H (HeightInduction.lean), so Rise
at every height gives the orbit-height property, hence Cut, by induction on height.
'local': Rise-local — some x with F(x, x) ≤ x < a(x) (orbit-free; such x < ⊤ is good given the lower heights).
'both': violate Rise and Rise-local simultaneously (the reduction with both kinds of witness).
Query: a monotone F violating Rise (SAT = counterexample, re-checked in Python); 'ctl' drops the no-rise
constraint (rigid maps only; should be SAT).  python3 rise_sat.py [ctl] (sweep P NMAX | closure K M SEED COUNT)
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from rstages import stages, a_of, b_of
from tight_probe import lattices

def query(L, ctl, mode='rise'):
    n = L.n; le = L.le; rk = L.rank; H = L.height
    E = Enc(L, H); r = lambda j, z: E.v('r', j, z); f = lambda x, y, v: E.v('f', x, y, v)
    E.S.add_clause([E.v('B', L.top, L.top)])
    for c in range(n):
        if c not in (L.bot, L.top): E.S.add_clause([-f(c, c, c)])
    if not ctl:
        for x in range(n):
            for g in range(n):
                if g != x and le[x][g]:
                    if mode in ('rise', 'both'): E.S.add_clause([-r(rk[x], x), -E.v('A', x, g)])
                    if mode in ('local', 'both'):
                        E.S.add_clause([-E.v('A', x, g)] + [f(x, x, v) for v in range(n) if not le[v][x]])
    if not E.S.solve(): E.S.delete(); return False
    F = E.decode(); E.S.delete(); st = stages(L, F)
    assert b_of(L, F, L.top) == L.top and not any(F[c][c] == c for c in range(n) if c not in (L.bot, L.top))
    if not ctl:
        rise = [x for x in range(n) if le[x][a_of(L, F, x)] and a_of(L, F, x) != x]
        if mode in ('rise', 'both'): assert not any(st[x] is not None and st[x] <= rk[x] for x in rise)
        if mode in ('local', 'both'): assert not any(le[F[x][x]][x] for x in rise)
    return F

if __name__ == '__main__':
    ctl = 'ctl' in sys.argv; mode = next((m for m in ('local', 'both') if m in sys.argv), 'rise')
    args = [a for a in sys.argv[1:] if a not in ('ctl', 'local', 'both')]
    C = collections.Counter(); best = None
    for L in lattices(args):
        if L.height < 1: continue
        F = query(L, ctl, mode)
        C['model' if F else 'none'] += 1
        if F and (best is None or L.n < best[0].n): best = (L, F)
    print(f"{mode}{' ctl' if ctl else ''}: {dict(C)}" + (f"; smallest |L| = {best[0].n}" if best else ''), flush=True)
    if best and not ctl: json.dump(dict(sets=best[0].S, F=best[1]), open(f'{mode}_fail_min{best[0].n}.json', 'w'))
