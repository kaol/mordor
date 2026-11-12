"""Exact test of the Rise conjecture (log §34.3z¹⁵⁷).

Rise(F): b(⊤) ≠ ⊤, or x ↦ F(x, x) has a fixed point ∉ {⊥, ⊤}, or some good x (x ∈ R_{h(x)}) has x < a(x).
(x = ⊥ covers a(⊥) ≠ ⊥.) With the lower heights, each alternative gives ⊤ ∈ R_H (HeightInduction.lean), so Rise
at every height gives the orbit-height property, hence Cut, by induction on height.
'local': Rise-local — some x with F(x, x) ≤ x < a(x) (orbit-free; such x < ⊤ is good given the lower heights).
'kc'  : KC (§34.3z¹⁵⁸) — rigid F (a(⊥) = ⊥ too) with some bad element of the column-⊤ Kleene chain ⊥, F(⊥, ⊤), …
'kclast': the same for the last chain element x_n < ⊤ (F(x_n, ⊤) = ⊤), which alone gives Rise.
'shallow=J': Rise with witnesses restricted to τ(x) ≤ min(h(x), J) or F(x, x) ≤ x (diagonal pre-fixed, good
           given the lower heights) — the witnesses a finite case analysis can reach.
'hmax=h': only lattices of height ≤ h.
'both': violate Rise and Rise-local simultaneously (the reduction with both kinds of witness).
Query: a monotone F violating Rise (SAT = counterexample, re-checked in Python); 'ctl' drops the no-rise
constraint (rigid maps only; should be SAT).  python3 rise_sat.py [ctl] (sweep P NMAX | closure K M SEED COUNT)
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from rstages import stages, a_of, b_of
from tight_probe import lattices as _lattices
import random, itertools
import separator_stages as ss

def lattices(args):
    if args and args[0] == 'h3':            # height-3 lattices: ∅, singletons, M random 2-sets, full set
        k, m, sd, cnt = (int(x) for x in args[1:5]); rng = random.Random(sd)
        pairs = list(itertools.combinations(range(k), 2))
        for _ in range(cnt):
            P = rng.sample(pairs, min(m, len(pairs)))
            S = sorted({0, (1 << k) - 1} | {1 << i for i in range(k)} | {(1 << i) | (1 << j) for i, j in P})
            yield ss.Lat(S)
    else:
        yield from _lattices(args)

J = 0
def query(L, ctl, mode='rise'):
    n = L.n; le = L.le; rk = L.rank; H = L.height
    E = Enc(L, H); r = lambda j, z: E.v('r', j, z); f = lambda x, y, v: E.v('f', x, y, v)
    E.S.add_clause([E.v('B', L.top, L.top)])
    for c in range(n):
        if c not in (L.bot, L.top): E.S.add_clause([-f(c, c, c)])
    if mode in ('kc', 'kclast'):
        E.S.add_clause([E.v('A', L.bot, L.bot)])
        kc = lambda i, z: E.v('kc', i, z)
        for z in range(n): E.S.add_clause([kc(0, z)] if z == L.bot else [-kc(0, z)])
        for i in range(H):
            for w in range(n):
                lits = []
                for z in range(n):
                    o = E.v('kcs', i, z, w); E.iff_and(o, [kc(i, z), f(z, L.top, w)]); lits.append(o)
                E.iff_or(kc(i + 1, w), lits)
        bad = []
        for i in range(H + 1):
            for z in range(n):
                if z == L.top: continue
                o = E.v('kcbad', i, z)
                E.iff_and(o, [kc(i, z), -r(rk[z], z)] + ([f(z, L.top, L.top)] if mode == 'kclast' else [])); bad.append(o)
        E.S.add_clause(bad)
    if not ctl and mode not in ('kc', 'kclast'):
        for x in range(n):
            for g in range(n):
                if g != x and le[x][g]:
                    if mode in ('rise', 'both'): E.S.add_clause([-r(rk[x], x), -E.v('A', x, g)])
                    if mode == 'shallow':
                        E.S.add_clause([-r(min(rk[x], J), x), -E.v('A', x, g)])
                        if x != L.top: E.S.add_clause([-E.v('A', x, g)] + [f(x, x, v) for v in range(n) if not le[v][x]])
                    if mode in ('local', 'both'):
                        E.S.add_clause([-E.v('A', x, g)] + [f(x, x, v) for v in range(n) if not le[v][x]])
    if not E.S.solve(): E.S.delete(); return False
    F = E.decode(); E.S.delete(); st = stages(L, F)
    assert b_of(L, F, L.top) == L.top and not any(F[c][c] == c for c in range(n) if c not in (L.bot, L.top))
    if mode in ('kc', 'kclast'):
        x = L.bot; chain = [x]
        while F[x][L.top] != L.top: x = F[x][L.top]; chain.append(x)
        good = lambda z: st[z] is not None and st[z] <= rk[z]
        assert a_of(L, F, L.bot) == L.bot and (not good(chain[-1]) if mode == 'kclast' else not all(good(c) for c in chain))
    elif mode == 'shallow':
        rise = [x for x in range(n) if le[x][a_of(L, F, x)] and a_of(L, F, x) != x]
        assert not any(st[x] is not None and st[x] <= min(rk[x], J) for x in rise) and not any(le[F[x][x]][x] for x in rise if x != L.top)
    elif not ctl:
        rise = [x for x in range(n) if le[x][a_of(L, F, x)] and a_of(L, F, x) != x]
        if mode in ('rise', 'both'): assert not any(st[x] is not None and st[x] <= rk[x] for x in rise)
        if mode in ('local', 'both'): assert not any(le[F[x][x]][x] for x in rise)
    return F

if __name__ == '__main__':
    ctl = 'ctl' in sys.argv; mode = next((m for m in ('local', 'both', 'kclast', 'kc') if m in sys.argv), 'rise')
    if any(a.startswith('shallow=') for a in sys.argv):
        mode = 'shallow'; J = next(int(a[8:]) for a in sys.argv if a.startswith('shallow='))
    hmax = next((int(a[5:]) for a in sys.argv if a.startswith('hmax=')), None)
    args = [a for a in sys.argv[1:] if a not in ('ctl', 'local', 'both', 'kc', 'kclast') and not a.startswith('hmax=') and not a.startswith('shallow=')]
    C = collections.Counter(); best = None
    for L in lattices(args):
        if L.height < 1 or (hmax is not None and L.height > hmax): continue
        F = query(L, ctl, mode)
        C['model' if F else 'none'] += 1
        if F and (best is None or L.n < best[0].n): best = (L, F)
    print(f"{mode}{' ctl' if ctl else ''}: {dict(C)}" + (f"; smallest |L| = {best[0].n}" if best else ''), flush=True)
    if best and not ctl: json.dump(dict(sets=best[0].S, F=best[1]), open(f'{mode}_fail_min{best[0].n}.json', 'w'))
