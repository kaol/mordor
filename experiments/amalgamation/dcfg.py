"""The configuration of D1 (log §34.3z²⁵¹): R_2 tight, h(⊤) ≥ 4, a(⊥) = ⊥, d the last nonzero element of the ⊥-descent
from ⊤ with h(d) = 2, z the drop column of the row-d descent from ⊤ (z ≥ d on it, F(d, z) ≱ d), q an atom with q < d and
q ≤ F(⊥, z).  Each mode asserts the negation of a claim; SAT = a counterexample (replayed in Python).
  D1  — q is good (q ≤ a(q), or the row-q descent from ⊤ meets q)
  A1  — z lies on the row-q descent from ⊤
  A3  — every x > q on the row-q descent has q ≤ F(⊥, x)
  A5  — every x ≥ q on the row-q descent satisfies x ≥ z or x ≤ F(d, z)
  A7  — every x > q on the row-q descent has x ≥ d
  A10 — every x > q on the row-q descent with x ≱ z has F(q, x) = q
  Ca  — every x > q on the row-q descent has x ≥ F(q, z)
  Cb  — q ≤ F(⊥, F(q, z))
  B1  — the row-q descent from z never drops below q (no x > q on it with F(q, x) ≱ q)
  B3  — F(q, z) is a lower cover (F(q, F(q, z)) = q) or post-fixed in row q
  vac — the configuration only
  python3 dcfg.py MODE (sweep N MAX | closure K M SEED CNT)
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import lattices
from rstages import stages, a_of
MODE = sys.argv[1]; CORE = 'core' in sys.argv; args = [a for a in sys.argv[2:] if a != 'core']   # core: R_2 tightness as assumptions; deletion-minimal cores + near-models
C = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top
    if L.height < 4: continue
    E = Enc(L, 2); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
    A_ = lambda x, g: E.v('A', x, g); NO = L.height + 1
    T = {}
    for z in range(n):
        if h[z] > 2:
            if CORE: T[z] = E.v('T', z); add([-T[z], -r(2, z)])
            else: add([-r(2, z)])
    add([A_(bot, bot)])
    def descvars(p):
        D = lambda i, z: E.v('DD', p, i, z)
        for z in range(n): add([D(0, z)] if z == top else [-D(0, z)])
        for i in range(NO):
            for z in range(n):
                lits = []
                for v in range(n): o = E.v('DDs', p, i, v, z); E.iff_and(o, [D(i, v), f(p, v, z)]); lits.append(o)
                E.iff_or(D(i + 1, z), lits)
        return lambda z: E.v('on', p, z) if ('on', p, z) in E.vars else (E.iff_or(E.v('on', p, z), [D(i, z) for i in range(NO + 1)]) or E.v('on', p, z))
    onB = descvars(bot)
    sel = []
    for dd in range(n):
        if h[dd] != 2: continue
        onD = descvars(dd)
        for z in range(n):
            if not le[dd][z]: continue
            for q in range(n):
                if h[q] != 1 or not le[q][dd]: continue
                onQ = descvars(q)
                s_ = E.v('cfg', dd, z, q); sel.append(s_)
                add([-s_, onB(dd)]); add([-s_, f(bot, dd, bot)]); add([-s_, onD(z)])
                for w in range(n):
                    if le[dd][w]: add([-s_, -f(dd, z, w)])
                add([-s_] + [f(bot, z, v) for v in range(n) if le[q][v]])
                if MODE == 'D1':
                    add([-s_, -onQ(q)])
                    for g in range(n):
                        if le[q][g]: add([-s_, -A_(q, g)])
                elif MODE == 'A1': add([-s_, -onQ(z)])
                elif MODE == 'B3':                                   # F(q, F(q, z)) ≠ q and F(q, z) ≰ F(q, F(q, z))
                    for sv in range(n):
                        for w in range(n):
                            if w == q or le[sv][w]: continue
                            o = E.v('b3', dd, z, q, sv, w); add([-o, f(q, z, sv)]); add([-o, f(q, sv, w)])
                    add([-s_] + [E.v('b3', dd, z, q, sv, w) for sv in range(n) for w in range(n) if not (w == q or le[sv][w])])
                elif MODE == 'B1':                                   # the row-q descent from z drops below q
                    Dz = lambda i, x: E.v('Dz', z, q, i, x)
                    if ('Dz', z, q, 0, 0) not in E.vars:
                        for x in range(n): add([Dz(0, x)] if x == z else [-Dz(0, x)])
                        for i in range(NO):
                            for x in range(n):
                                ls = []
                                for v in range(n): o = E.v('Dzs', z, q, i, v, x); E.iff_and(o, [Dz(i, v), f(q, v, x)]); ls.append(o)
                                E.iff_or(Dz(i + 1, x), ls)
                    lits = []
                    for i in range(NO):
                        for x in range(n):
                            if not le[q][x] or x == q: continue
                            for v in range(n):
                                if le[q][v]: continue
                                o = E.v('b1', z, q, i, x, v); add([-o, Dz(i, x)]); add([-o, f(q, x, v)]); lits.append(o)
                    add([-s_] + lits)
                elif MODE == 'Cb':                                   # q ≰ F(⊥, F(q, z))
                    for sv in range(n):
                        o = E.v('cb', z, q, sv); add([-o, f(q, z, sv)])
                        for w in range(n):
                            if le[q][w]: add([-o, -f(bot, sv, w)])
                    add([-s_] + [E.v('cb', z, q, sv) for sv in range(n)])
                elif MODE == 'Ca':                                   # some x > q on the row-q descent with x ≱ F(q, z)
                    xs = []
                    for x in range(n):
                        if not le[q][x] or x == q: continue
                        for sv in range(n):
                            if le[sv][x]: continue
                            o = E.v('ca', z, q, x, sv); E.iff_and(o, [onQ(x), f(q, z, sv)]); xs.append(o)
                    add([-s_] + xs)
                elif MODE in ('A7', 'A10'):
                    xs = []
                    for x in range(n):
                        if not le[q][x] or x == q: continue
                        if MODE == 'A7' and le[dd][x]: continue
                        if MODE == 'A10' and le[z][x]: continue
                        o = E.v('bx', dd, z, q, x)
                        if MODE == 'A7': E.iff_and(o, [onQ(x)])
                        else: E.iff_and(o, [onQ(x), -f(q, x, q)])
                        xs.append(o)
                    add([-s_] + xs)
                elif MODE in ('A3', 'A5'):
                    xs = []
                    for x in range(n):
                        if not le[q][x] or x == q: continue
                        if MODE == 'A5' and le[z][x]: continue
                        o = E.v('bx', dd, z, q, x)
                        if MODE == 'A3': E.iff_and(o, [onQ(x)] + [-f(bot, x, v) for v in range(n) if le[q][v]])
                        else: E.iff_and(o, [onQ(x)] + [-f(dd, z, t) for t in range(n) if le[x][t]])
                        xs.append(o)
                    add([-s_] + xs)
    if not sel: E.S.delete(); continue
    add(sel)
    if CORE:
        allz = list(T)
        if E.S.solve(assumptions=[T[z] for z in allz]): C['SAT(full)'] += 1; E.S.delete(); continue
        core = list(allz)
        for z0 in list(core):
            tr = [x for x in core if x != z0]
            if not E.S.solve(assumptions=[T[x] for x in tr]): core = tr
        C['core %d' % len(core)] += 1
        name = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
        for z0 in core:
            if not E.S.solve(assumptions=[T[x] for x in allz if x != z0]): C['near UNSAT'] += 1; continue
            F = E.decode(); st = stages(L, F)
            R1 = [x for x in range(n) if st[x] is not None and st[x] <= 1]
            def desc(p):
                v = top; seen = []
                while v not in seen: seen.append(v); v = F[p][v]
                return seen
            bd = desc(bot); dd = next(x for x in bd if x != bot and F[bot][x] == bot)
            zs = [z for z in desc(dd) if le[dd][z] and not le[dd][F[dd][z]]]
            via = []
            for x in R1:
                if le[z0][a_of(L, F, x)]: via.append('a(%s)' % ('q' if h[x] == 1 and le[x][dd] else 'd' if x == dd else 'h%d' % h[x]))
                if le[F[x][z0]][x]: via.append('low(%s%s)' % ('q' if h[x] == 1 and le[x][dd] else 'd' if x == dd else 'h%d' % h[x], '=' if F[x][z0] == x else ''))
            C['via ' + ','.join(sorted(set(via)))] += 1
            if C['shown'] < 4:
                C['shown'] += 1
                print('n', n, 'excluded', name(z0), 'd', name(dd), 'z', [name(z) for z in zs], 'via', via)
                for q in range(n):
                    if h[q] == 1 and le[q][dd]: print('   q', name(q), 'desc', [name(x) for x in desc(q)], 'a', name(a_of(L, F, q)), 'F(⊥,z)', [name(F[bot][z]) for z in zs])
                print('   d desc', [name(x) for x in desc(dd)], 'bd', [name(x) for x in bd])
        E.S.delete(); continue
    if E.S.solve():
        F = E.decode(); st = stages(L, F)
        def desc(p):
            v = top; seen = []
            while v not in seen: seen.append(v); v = F[p][v]
            return seen
        gd = lambda p: p in desc(p) or le[p][a_of(L, F, p)]
        bd = desc(bot); dd = next(x for x in bd if x != bot and F[bot][x] == bot)
        ok = a_of(L, F, bot) == bot and h[dd] == 2 and all(h[x] <= 2 for x in range(n) if st[x] is not None and st[x] <= 2)
        zs = [z for z in desc(dd) if le[dd][z] and not le[dd][F[dd][z]]]
        cf = [(z, q) for z in zs for q in range(n) if h[q] == 1 and le[q][dd] and le[q][F[bot][z]]]
        if MODE == 'D1': ok = ok and any(not gd(q) for z, q in cf)
        elif MODE == 'A1': ok = ok and any(z not in desc(q) for z, q in cf)
        elif MODE == 'A7': ok = ok and any(any(le[q][x] and x != q and not le[dd][x] for x in desc(q)) for z, q in cf)
        elif MODE == 'A10': ok = ok and any(any(le[q][x] and x != q and not le[z][x] and F[q][x] != q for x in desc(q)) for z, q in cf)
        elif MODE == 'Cb': ok = ok and any(not le[q][F[bot][F[q][z]]] for z, q in cf)
        elif MODE == 'Ca': ok = ok and any(any(le[q][x] and x != q and not le[F[q][z]][x] for x in desc(q)) for z, q in cf)
        elif MODE == 'B3': ok = ok and any(F[q][F[q][z]] != q and not le[F[q][z]][F[q][F[q][z]]] for z, q in cf)
        elif MODE == 'B1':
            def descs(p, s0):
                v = s0; seen = []
                while v not in seen: seen.append(v); v = F[p][v]
                return seen
            ok = ok and any(any(le[q][x] and x != q and not le[q][F[q][x]] for x in descs(q, z)) for z, q in cf)
        elif MODE == 'A3': ok = ok and any(any(le[q][x] and x != q and not le[q][F[bot][x]] for x in desc(q)) for z, q in cf)
        elif MODE == 'A5': ok = ok and any(any(le[q][x] and x != q and not le[z][x] and not le[x][F[dd][z]] for x in desc(q)) for z, q in cf)
        elif MODE == 'vac': ok = ok and bool(cf)
        else: raise SystemExit('unknown mode ' + MODE)
        assert ok, 'SAT/Python mismatch'
        C['SAT'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else: C['UNSAT'] += 1
    E.S.delete()
print(MODE, dict(C), 'smallest', best[0] if best else None)
if best and MODE != 'vac': json.dump(best[1], open(f'dcfg_{MODE}_min{best[0]}.json', 'w'))
