"""Cores of GoodBase at j = 1 (log §34.3z²⁴⁸): which R_2-tightness instances does "some atom of R_1 is good" use?
Near-models keep every tightness instance except the excluded one.
Hypotheses: a(⊥) = ⊥, h(⊤) ≥ 4, R_2 tight (as assumptions, one per z with h(z) > 2), claim negated as in gb1.py 'any'.
For each UNSAT lattice: a minimal core (deletion-minimized). Then a near-model (all instances but one core instance):
report the excluded z, its height, how it enters R_2 (via a(x), x ∈ R_1; via a lower cell F(x, z) ≤ x, x ∈ R_1; or below one),
and the atoms of R_1 with their descents.
  python3 gb1_core.py (sweep N MAX | closure K M SEED CNT) [show]
"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import lattices
from rstages import stages, a_of
SHOW = 'show' in sys.argv; DTWO = 'dtwo' in sys.argv; args = [a for a in sys.argv[1:] if a not in ('show', 'dtwo')]   # dtwo: claim = some atom ≤ d is good, where h(d) = 2
C = collections.Counter(); shown = 0
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top
    if L.height < 4: continue
    E = Enc(L, 2); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
    A_ = lambda x, g: E.v('A', x, g); NO = L.height + 1
    add([A_(bot, bot)])
    sel = {}
    for z in range(n):
        if h[z] > 2: sel[z] = E.v('T', z); add([-sel[z], -r(2, z)])
    atoms = [p for p in range(n) if h[p] == 1]
    if DTWO:
        D = lambda i, z: E.v('DD', i, z)
        for z in range(n): add([D(0, z)] if z == top else [-D(0, z)])
        for i in range(NO):
            for z in range(n):
                lits = []
                for v in range(n): o = E.v('DDs', i, v, z); E.iff_and(o, [D(i, v), f(bot, v, z)]); lits.append(o)
                E.iff_or(D(i + 1, z), lits)
        isd = {}
        for z in range(n):
            if h[z] != 2: continue
            on = E.v('onB', z); E.iff_or(on, [D(i, z) for i in range(NO + 1)])
            isd[z] = E.v('isd', z); E.iff_and(isd[z], [on, f(bot, z, bot)])
        add(list(isd.values()))
    for p in atoms:
        P = lambda i, z: E.v('PP', p, i, z)
        for z in range(n): add([P(0, z)] if z == top else [-P(0, z)])
        for i in range(NO):
            for z in range(n):
                lits = []
                for v in range(n): o = E.v('PPs', p, i, v, z); E.iff_and(o, [P(i, v), f(p, v, z)]); lits.append(o)
                E.iff_or(P(i + 1, z), lits)
        guard = [-r(1, p)] if not DTWO else []
        dl = [] if not DTWO else [-isd[z] for z in isd if le[p][z]]
        if DTWO and not dl: continue
        for dz in (dl if DTWO else [None]):
            g0 = guard + ([dz] if dz is not None else [])
            for i in range(NO + 1): add(g0 + [-P(i, p)])
            for g in range(n):
                if le[p][g]: add(g0 + [-A_(p, g)])
    allz = list(sel)
    if E.S.solve(assumptions=[sel[z] for z in allz]): C['SAT(full)'] += 1; E.S.delete(); continue
    core = list(allz)
    for z in list(core):
        trial = [x for x in core if x != z]
        if not E.S.solve(assumptions=[sel[x] for x in trial]): core = trial
    C['core size %d' % len(core)] += 1
    C['core heights ' + ','.join(str(h[z]) for z in sorted(core, key=lambda z: h[z]))] += 1
    for z0 in core:
        if not E.S.solve(assumptions=[sel[x] for x in allz if x != z0]): C["near UNSAT (other instances suffice)"] += 1; continue
        F = E.decode(); st = stages(L, F)
        inR1 = lambda x: st[x] is not None and st[x] <= 1
        R1 = [x for x in range(n) if inR1(x)]
        via = []
        if any(le[z0][a_of(L, F, x)] for x in R1): via.append('a')
        if any(le[F[x][z0]][x] for x in R1): via.append('lowcell')
        if any(le[z0][w] and le[F[x][w]][x] for x in R1 for w in range(n) if w != z0): via.append('below-lowcell')
        C['near via ' + '+'.join(via)] += 1
        lx = [x for x in R1 if le[F[x][z0]][x]]
        C['near lowcell rows: ' + ','.join(sorted(('atom' if h[x] == 1 else 'h%d' % h[x]) + ('' if F[x][z0] != x else '=') for x in lx))] += 1
        if SHOW and shown < 3:
            shown += 1
            name = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
            def desc(p):
                v = top; seen = []
                while v not in seen: seen.append(v); v = F[p][v]
                return seen
            print('n', n, 'excluded', name(z0), 'h', h[z0], 'R1', [name(x) for x in R1], 'lowcell rows', [(name(x), name(F[x][z0])) for x in lx])
            for p in atoms:
                if inR1(p): print('   atom', name(p), 'desc', [name(x) for x in desc(p)], 'a', name(a_of(L, F, p)))
            print('   bd', [name(x) for x in desc(bot)])
    E.S.delete()
for k, v in sorted(C.items()): print(k, v)
