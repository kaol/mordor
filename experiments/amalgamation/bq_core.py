"""Cores of bq over the uniqueness instances (log §34.3z²⁵⁴).
SingletonLower configuration at k = 2 (R_2, R_3 tight, m ∈ R_3 \\ R_2, feeder m' with F(m', m) ≤ m', ⊤ ∉ R_4), B-route q = b(m') ∈ R_1,
m' off the row-q descent; uniqueness of m as one assumption 'z ∉ R_3' per height-3 z ≠ m. Deletion-minimal cores; near-models with all
uniqueness instances but one. Reports how the excluded z enters R_3 and its relation to u (drop column), v = F(q, u), x0 (the element
of the row-q descent just before q, if the descent meets q).
  python3 bq_core.py (sweep N MAX | closure K M SEED CNT) [show]"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from rstages import stages, a_of, b_of
SHOW = 'show' in sys.argv; args = [a for a in sys.argv[1:] if a != 'show']
C = collections.Counter(); shown = 0
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; top = L.top; NO = L.height + 1
    for m in range(n):
        if h[m] != 3 or L.height <= 3: continue
        for mp in range(n):
            if h[mp] != 2 or not le[mp][m]: continue
            E = Enc(L, 4); fle, yle, ic = helpers(E, L); f = lambda a, b_, u: E.v('f', a, b_, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
            add([-r(4, top)]); add([r(3, m)]); add([-r(2, m)]); add([r(2, mp)]); add([fle(mp, m, mp)])
            T = {}
            for z in range(n):
                if h[z] > 2: add([-r(2, z)])
                if h[z] > 3: add([-r(3, z)])
                if h[z] == 3 and z != m: T[z] = E.v('T', z); add([-T[z], -r(3, z)])
            sel = []
            for q in range(n):
                if not le[q][mp] or q == mp: continue
                D = lambda i, z, q=q: E.v('DD', q, i, z)
                for z in range(n): add([D(0, z)] if z == top else [-D(0, z)])
                for i in range(NO):
                    for z in range(n):
                        lits = []
                        for v in range(n): o = E.v('DDs', q, i, v, z); E.iff_and(o, [D(i, v), f(q, v, z)]); lits.append(o)
                        E.iff_or(D(i + 1, z), lits)
                o = E.v('bq', q); sel.append(o); add([-o, E.v('B', mp, q)]); add([-o, r(1, q)])
                for i in range(NO + 1): add([-o, -D(i, mp)])
            add(sel)
            allz = list(T)
            if E.S.solve(assumptions=[T[z] for z in allz]): C['SAT(full)'] += 1; E.S.delete(); continue
            if not E.S.solve(): C['vacuous'] += 1; E.S.delete(); continue
            core = list(allz)
            for z0 in list(core):
                tr = [x for x in core if x != z0]
                if not E.S.solve(assumptions=[T[x] for x in tr]): core = tr
            C['core %d' % len(core)] += 1
            for z0 in core:
                if not E.S.solve(assumptions=[T[x] for x in allz if x != z0]): C['near UNSAT'] += 1; continue
                F = E.decode(); st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j
                q = b_of(L, F, mp)
                v_ = top; ds = []
                while v_ not in ds: ds.append(v_); v_ = F[q][v_]
                u = [x for x in ds if le[mp][x]][-1]; w = F[q][u]
                x0 = next((ds[i] for i in range(len(ds) - 1) if ds[i + 1] == q and ds[i] != q), None)
                R2 = [x for x in range(n) if inR(x, 2)]
                role = lambda x: 'q' if x == q else "m'" if x == mp else 'v' if x == w else 'x0' if x == x0 else 'h%d' % h[x]
                tags = []
                for x in R2:
                    if le[z0][a_of(L, F, x)]: tags.append('a(%s)' % role(x))
                    if any(le[z0][y] and le[F[x][y]][x] for y in range(n)): tags.append('low(%s)' % role(x))
                rel = []
                if z0 == u: rel.append('z=u')
                elif le[z0][u]: rel.append('z<u')
                if le[mp][z0]: rel.append("z>m'")
                if x0 is not None and le[x0][z0]: rel.append('z>x0')
                if le[w][z0]: rel.append('z>v')
                C['rel ' + ','.join(rel) + ' | via ' + ','.join(sorted(set(tags)))] += 1
                if SHOW and shown < 4:
                    shown += 1
                    name = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
                    print('n', n, 'm', name(m), "m'", name(mp), 'q', name(q), 'excluded', name(z0), 'desc q', [name(x) for x in ds], 'u', name(u), 'v', name(w), 'x0', name(x0) if x0 is not None else None, 'via', tags)
            E.S.delete()
for k_, v_ in sorted(C.items(), key=lambda t: -t[1]): print(v_, k_)
