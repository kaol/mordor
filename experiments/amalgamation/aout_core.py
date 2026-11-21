"""Cores of 'aout' (log §34.3z²⁵³): R_2 tightness instances as assumptions; minimal cores; near-models (all instances but one).
Configuration: m' ∈ R_2 \\ R_1 of height 2, m' < m, F(m', m) ≤ m', m ∈ R_3 \\ R_2, pure A-route (b(m') ∉ R_1), and no x ≤ m' in R_1 with a(x) = m'.
  python3 aout_core.py (sweep N MAX | closure K M SEED CNT) [show]"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from rstages import stages, a_of, b_of
SHOW = 'show' in sys.argv; args = [a for a in sys.argv[1:] if a != 'show']
C = collections.Counter(); shown = 0
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; top = L.top
    for m in range(n):
        if h[m] != 3 or L.height <= 3: continue
        for mp in range(n):
            if h[mp] != 2 or not le[mp][m]: continue
            E = Enc(L, 3); fle, yle, ic = helpers(E, L); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
            add([r(3, m)]); add([-r(2, m)]); add([r(2, mp)]); add([fle(mp, m, mp)])
            T = {}
            for z in range(n):
                if h[z] > 2: T[z] = E.v('T', z); add([-T[z], -r(2, z)])
            for g in range(n): add([-E.v('B', mp, g), -r(1, g)])
            for x in range(n):
                if le[x][mp]: add([-r(1, x), -E.v('A', x, mp)])
            allz = list(T)
            if E.S.solve(assumptions=[T[z] for z in allz]): C['SAT(full)'] += 1; E.S.delete(); continue
            if not E.S.solve(): C['vacuous w/o tightness'] += 1; E.S.delete(); continue
            core = list(allz)
            for z0 in list(core):
                tr = [x for x in core if x != z0]
                if not E.S.solve(assumptions=[T[x] for x in tr]): core = tr
            C['core %d' % len(core)] += 1
            for z0 in core:
                if not E.S.solve(assumptions=[T[x] for x in allz if x != z0]): C['near UNSAT'] += 1; continue
                F = E.decode(); st = stages(L, F)
                R1 = [x for x in range(n) if st[x] is not None and st[x] <= 1]
                via = []
                for x in R1:
                    if le[z0][a_of(L, F, x)]: via.append('a(%s)' % ('m\'' if x == mp else 'atom' if h[x] == 1 else 'h%d' % h[x]))
                    if le[F[x][z0]][x]: via.append('low(%s%s)' % ('atom' if h[x] == 1 else 'h%d' % h[x], '=' if F[x][z0] == x else ''))
                    if le[z0][F[x][z0]]: via.append('up(%s)' % ('atom' if h[x] == 1 else 'h%d' % h[x]))
                C['z0=' + ('m' if z0 == m else 'h%d' % h[z0]) + ' via ' + ','.join(sorted(set(via)))] += 1
                if SHOW and shown < 4:
                    shown += 1
                    name = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
                    print('n', n, 'm', name(m), "m'", name(mp), 'excluded', name(z0), 'via', via, 'R1', [name(x) for x in R1])
                    for x in R1:
                        print('   x', name(x), 'a', name(a_of(L, F, x)), 'F(x,z0)', name(F[x][z0]), 'F(x,m)', name(F[x][m]), "F(x,m')", name(F[x][mp]))
            E.S.delete()
for k_, v in sorted(C.items()): print(k_, v)
