"""Good DL atoms of the zero fibre (log §34.3z²⁵⁸). World W0: a(⊥) = ⊥, R_2 tight, ⊤ ∉ R_2 (so R_1 = Z = {y : F(⊥,y) = ⊥}).
A DL atom is an atom p ∈ R_1 with DL(⊥, p): ∀ y ≰ p, ¬(y ≤ F(⊥, p ⊔ y)). 'p good' = p ≤ a(p) or the row-p descent from ⊤ meets p.
d = the last nonzero element of the ⊥-descent from ⊤; dep(x) = max{i : x ≤ (F ⊥)^i(⊤)}.
  vac      — W0 only
  baddl    — some bad DL atom
  goodatom — every atom of R_1 bad                (SAT refutes BackGood1 at k = 1)
  dlgood   — every DL atom of R_1 bad            (SAT refutes DLGood)
  uniq     — two good DL atoms                    (SAT refutes uniqueness)
  uniqany  — two good atoms of R_1 (mutant: DL dropped)
  dpart    — an atom p ≤ d is bad and no good DL atom q ≠ p has p ⊔ q ∈ Z   (SAT refutes DPartner)
  dpartX   — mutant of dpart: the partner condition p ⊔ q ∈ Z flipped
  exch4    — a bad DL atom p with no DL partner q (p ⊔ q ∈ Z) that is good or deeper   (SAT refutes DepthExchange)
  exch4R   — mutant: 'deeper' reversed;  exchA — mutant: partner must be good
  gdnotd   — a good DL atom of R_1 that is not below d (SAT refutes 'the good DL atom lies below d')
  dlnotd   — a DL atom of R_1 that is not below d (goodness not required)
  lg / lgP — no good atom of R_1 below λ(d) / below F(d, λ(d)), λ(e) = the first element of height ≤ 2 on the row-e descent
             (SAT refutes LandGood / LandGood⁺, §34.3z²⁶¹)
  lgB / lgPP — mutants: λ(⊥) in place of λ(d); one more descent step F(d, F(d, λ(d)))
  coP     — no atom q ≤ d ∧ λ(d) whose descent lands at λ(d) (SAT refutes CoLand; use with hd2)
  coC     — no good atom q ≤ d ∧ λ(d) (use with hd2)
  coM1 / coM2 — mutants: some atom below d does not co-land / has F(p, λ(d)) ≱ p
  allbadbelowd — every atom below d is bad (SAT refutes 'some atom below d is good')
  badbelowd — some atom below d is bad (mutant-like control for gdnotd)
Flags: n1 (R_1 non-tight), r1t (R_1 tight), not2 (drop R_2 tightness: mutant), h3 (only h(⊤) = 3), h4 (only h(⊤) ≥ 4),
       hd1 / hd2 (h(d) = 1 / 2), dbad (d is bad).
  python3 dlatoms.py MODE (sweep N MAX | closure K M SEED CNT) [flags]"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import lattices
from rstages import stages, a_of
FLG = {'n1', 'r1t', 'not2', 'h3', 'h4', 'hd1', 'hd2', 'dbad'}
MODES = {'vac', 'baddl', 'goodatom', 'dlgood', 'uniq', 'uniqany', 'dpart', 'dpartX', 'exch4', 'exch4R', 'exchA', 'gdnotd', 'badbelowd', 'dlnotd', 'allbadbelowd', 'lg', 'lgP', 'lgB', 'lgPP', 'coP', 'coC', 'coM1', 'coM2'}
MODE = sys.argv[1]; FL = {a for a in sys.argv[2:] if a in FLG}; args = [a for a in sys.argv[2:] if a not in FLG]
if MODE not in MODES: raise SystemExit('unknown mode')
C = collections.Counter(); INFO = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; top = L.top; bot = L.bot; NO = L.height + 1; jn = L.join
    if L.height < 3 or ('h3' in FL and L.height != 3) or ('h4' in FL and L.height < 4): continue
    E = Enc(L, 2); f = lambda a, b, u: E.v('f', a, b, u); r = lambda i, z: E.v('r', i, z); add = E.S.add_clause
    A = lambda x, g: E.v('A', x, g)
    add([A(bot, bot)]); add([-r(2, top)])
    if 'not2' not in FL:
        for z in range(n):
            if h[z] > 2: add([-r(2, z)])
    if 'n1' in FL: add([r(1, z) for z in range(n) if h[z] > 1])
    if 'r1t' in FL:
        for z in range(n):
            if h[z] > 1: add([-r(1, z)])
    atoms = [p for p in range(n) if h[p] == 1]
    def descvars(p):
        D = lambda i, z: E.v('DD', p, i, z)
        if ('DD', p, 0, top) in E.vars: return D
        for z in range(n): add([D(0, z)] if z == top else [-D(0, z)])
        for i in range(NO):
            for z in range(n):
                lits = []
                for v in range(n): o = E.v('DDs', p, i, v, z); E.iff_and(o, [D(i, v), f(p, v, z)]); lits.append(o)
                E.iff_or(D(i + 1, z), lits)
        return D
    def gd(p):
        o = E.v('gd', p)
        if ('gdset', p) not in E.vars:
            E.v('gdset', p); D = descvars(p)
            E.iff_or(o, [A(p, v) for v in range(n) if le[p][v]] + [D(i, p) for i in range(NO + 1)])
        return o
    def DL(p):
        o = E.v('DL', p)
        if ('DLset', p) not in E.vars:
            E.v('DLset', p); ts = []
            for y in range(n):
                if le[y][p]: continue
                t = E.v('DLt', p, y); E.iff_or(t, [f(bot, jn[p][y], g) for g in range(n) if le[y][g]]); ts.append(-t)
            E.iff_and(o, ts)
        return o
    Db = descvars(bot)
    def isd(z):
        o = E.v('isd', z)
        if ('isdset', z) not in E.vars:
            E.v('isdset', z); w = E.v('onb', z); E.iff_or(w, [Db(i, z) for i in range(NO + 1)])
            E.iff_and(o, [w, f(bot, z, bot)])
        return o
    def belowd(p):
        o = E.v('bd', p); E.iff_or(o, [isd(z) for z in range(n) if le[p][z] and z != bot]); return o
    def Pd(x, i):
        o = E.v('Pd', x, i)
        if ('Pdset', x, i) not in E.vars: E.v('Pdset', x, i); E.iff_or(o, [Db(i, z) for z in range(n) if le[x][z]])
        return o
    def deeper(q, p):
        o = E.v('deeper', q, p)
        if ('deepset', q, p) not in E.vars:
            E.v('deepset', q, p); ls = []
            for i in range(NO + 1):
                t = E.v('deepi', q, p, i); E.iff_and(t, [Pd(q, i), -Pd(p, i)]); ls.append(t)
            E.iff_or(o, ls)
        return o
    if 'hd1' in FL: add([isd(z) for z in range(n) if h[z] == 1])
    if 'hd2' in FL: add([isd(z) for z in range(n) if h[z] == 2])
    if 'dbad' in FL:
        for z in range(n):
            if z != bot: add([-isd(z), -gd(z)])
    LAND = ('lg', 'lgP', 'lgB', 'lgPP', 'coP', 'coC', 'coM1', 'coM2')
    if MODE in LAND:
        low = [z for z in range(n) if h[z] <= 2]
        def on(e, z):
            o = E.v('on', e, z)
            if ('onset', e, z) not in E.vars: E.v('onset', e, z); D = descvars(e); E.iff_or(o, [D(i, z) for i in range(NO + 1)])
            return o
        def lam(e, z):
            o = E.v('lam', e, z)
            if ('lamset', e, z) not in E.vars:
                E.v('lamset', e, z); E.iff_and(o, [on(e, z)] + [-on(e, w) for w in low if le[z][w] and w != z])
            return o
        lamd = {}
        for z in low:
            o = E.v('lamd', z); ls = []
            for e in range(n):
                if e == bot: continue
                t = E.v('lamdt', e, z); E.iff_and(t, [isd(e), lam(e, z)]); ls.append(t)
            E.iff_or(o, ls); lamd[z] = o
        pd = {}
        if MODE in ('lgP', 'lgPP', 'coM2'):
            for v in range(n):
                o = E.v('pd', v); ls = []
                for e in range(n):
                    if e == bot: continue
                    for z in low:
                        t = E.v('pdt', e, z, v); E.iff_and(t, [isd(e), lam(e, z), f(e, z, v)]); ls.append(t)
                E.iff_or(o, ls); pd[v] = o
        pdd = {}
        if MODE == 'lgPP':
            for v2 in range(n):
                o = E.v('pdd', v2); ls = []
                for e in range(n):
                    if e == bot: continue
                    for v in range(n):
                        t = E.v('pddt', e, v, v2); E.iff_and(t, [isd(e), pd[v], f(e, v, v2)]); ls.append(t)
                E.iff_or(o, ls); pdd[v2] = o
        def region(p):
            o = E.v('reg', p)
            if MODE in ('lg', 'coP', 'coC', 'coM1'): E.iff_or(o, [lamd[z] for z in low if le[p][z]])
            elif MODE == 'lgP': E.iff_or(o, [pd[v] for v in range(n) if le[p][v]])
            elif MODE == 'lgPP': E.iff_or(o, [pdd[v] for v in range(n) if le[p][v]])
            elif MODE == 'lgB': E.iff_or(o, [on(bot, z) for z in low if le[p][z] and z != bot])
            return o
        if MODE in ('lg', 'lgP', 'lgB', 'lgPP'):
            for p in atoms: add([-r(1, p), -region(p), -gd(p)])
        elif MODE in ('coP', 'coC'):
            for q in atoms:
                sel = E.v('sel', q); E.iff_and(sel, [r(1, q), belowd(q), region(q)])
                if MODE == 'coP':
                    col = E.v('col', q); ls = []
                    for z in low:
                        t = E.v('colt', q, z); E.iff_and(t, [lamd[z], lam(q, z)]); ls.append(t)
                    E.iff_or(col, ls); add([-sel, -col])
                else: add([-sel, -gd(q)])
        elif MODE in ('coM1', 'coM2'):
            ss_ = []
            for p in atoms:
                o = E.v('sm', p); ss_.append(o); add([-o, r(1, p)]); add([-o, belowd(p)])
                if MODE == 'coM1':
                    for z in low: add([-o, -lamd[z], -lam(p, z)])
                else:
                    ls = []
                    for z in low:
                        t = E.v('cm2', p, z); E.iff_and(t, [lamd[z], E.v('cm2v', p, z)])
                        E.iff_or(E.v('cm2v', p, z), [f(p, z, v) for v in range(n) if not le[p][v]]); ls.append(t)
                    add([-o] + ls)
            add(ss_)
    if MODE == 'allbadbelowd':
        for p in atoms: add([-belowd(p), -gd(p)])
        add([belowd(p) for p in atoms])
    if MODE in ('gdnotd', 'badbelowd', 'dlnotd'):
        sel = []
        for p in atoms:
            o = E.v('s', p); sel.append(o)
            if MODE == 'gdnotd': add([-o, r(1, p)]); add([-o, DL(p)]); add([-o, gd(p)]); add([-o, -belowd(p)])
            elif MODE == 'dlnotd': add([-o, r(1, p)]); add([-o, DL(p)]); add([-o, -belowd(p)])
            else: add([-o, belowd(p)]); add([-o, -gd(p)])
        add(sel)
    if MODE == 'baddl':
        sel = []
        for p in atoms:
            o = E.v('s', p); sel.append(o); add([-o, r(1, p)]); add([-o, DL(p)]); add([-o, -gd(p)])
        add(sel)
    elif MODE == 'goodatom':
        for p in atoms: add([-r(1, p), -gd(p)])
    elif MODE == 'dlgood':
        for p in atoms: add([-r(1, p), -DL(p), -gd(p)])
    elif MODE in ('uniq', 'uniqany'):
        sel = []
        for i, p in enumerate(atoms):
            for q in atoms[i + 1:]:
                o = E.v('pr', p, q); sel.append(o)
                for x in (p, q):
                    add([-o, r(1, x)]); add([-o, gd(x)])
                    if MODE == 'uniq': add([-o, DL(x)])
        add(sel)
    elif MODE in ('dpart', 'dpartX'):
        sel = []
        for p in atoms:
            o = E.v('s', p); sel.append(o); add([-o, belowd(p)]); add([-o, -gd(p)])
            for q in atoms:
                if q == p: continue
                z = f(bot, jn[p][q], bot)
                add([-o, -r(1, q), -DL(q), (-z if MODE == 'dpart' else z), -gd(q)])
        add(sel)
    elif MODE in ('exch4', 'exch4R', 'exchA'):
        sel = []
        for p in atoms:
            o = E.v('s', p); sel.append(o); add([-o, r(1, p)]); add([-o, DL(p)]); add([-o, -gd(p)])
            for q in atoms:
                if q == p: continue
                z = f(bot, jn[p][q], bot)
                if MODE == 'exchA': add([-o, -r(1, q), -DL(q), -z, -gd(q)])
                else:
                    dq = deeper(q, p) if MODE == 'exch4' else deeper(p, q)
                    add([-o, -r(1, q), -DL(q), -z, -gd(q)]); add([-o, -r(1, q), -DL(q), -z, -dq])
        add(sel)
    if E.S.solve():
        F = E.decode(); st = stages(L, F); inR = lambda x, i: st[x] is not None and st[x] <= i
        def desc(p):
            v = top; seen = []
            while v not in seen: seen.append(v); v = F[p][v]
            return seen
        good = lambda p: le[p][a_of(L, F, p)] or p in desc(p)
        dl = lambda p: not any(not le[y][p] and le[y][F[bot][jn[p][y]]] for y in range(n))
        bd = desc(bot); dd = [z for z in bd if z != bot and F[bot][z] == bot]
        d = dd[0] if dd else None
        dep = lambda x: max([i for i, z in enumerate(bd) if le[x][z]], default=-1)
        Zin = lambda x: F[bot][x] == bot
        R1 = [p for p in atoms if inR(p, 1)]
        ok = a_of(L, F, bot) == bot and not inR(top, 2)
        if 'not2' not in FL: ok = ok and all(h[z] <= 2 for z in range(n) if inR(z, 2))
        if 'n1' in FL: ok = ok and any(h[z] > 1 for z in range(n) if inR(z, 1))
        if 'r1t' in FL: ok = ok and all(h[z] <= 1 for z in range(n) if inR(z, 1))
        if 'hd1' in FL: ok = ok and d is not None and h[d] == 1
        if 'hd2' in FL: ok = ok and d is not None and h[d] == 2
        if 'dbad' in FL: ok = ok and d is not None and not good(d)
        if MODE in ('lg', 'lgP', 'lgB', 'lgPP', 'coP', 'coC', 'coM1', 'coM2'):
            lamf = lambda e: next(z for z in desc(e) if h[z] <= 2)
            ld = lamf(d)
            if MODE == 'lg': reg = lambda p: le[p][ld]
            elif MODE == 'lgP': reg = lambda p: le[p][F[d][ld]]
            elif MODE == 'lgPP': reg = lambda p: le[p][F[d][F[d][ld]]]
            elif MODE == 'lgB': reg = lambda p: le[p][lamf(bot)]
            else: reg = lambda p: le[p][ld]
            if MODE in ('lg', 'lgP', 'lgB', 'lgPP'): ok = ok and not any(reg(p) and good(p) for p in R1)
            elif MODE == 'coP': ok = ok and not any(le[q][d] and reg(q) and lamf(q) == ld for q in R1)
            elif MODE == 'coC': ok = ok and not any(le[q][d] and reg(q) and good(q) for q in R1)
            elif MODE == 'coM1': ok = ok and any(le[p][d] and lamf(p) != ld for p in R1)
            elif MODE == 'coM2': ok = ok and any(le[p][d] and not le[p][F[p][ld]] for p in R1)
        if MODE == 'gdnotd': ok = ok and any(dl(p) and good(p) and not (d is not None and le[p][d]) for p in R1)
        elif MODE == 'dlnotd': ok = ok and any(dl(p) and not (d is not None and le[p][d]) for p in R1)
        elif MODE == 'allbadbelowd': ok = ok and d is not None and not any(le[p][d] and good(p) for p in atoms)
        elif MODE == 'badbelowd': ok = ok and any(d is not None and le[p][d] and not good(p) for p in atoms)
        if MODE == 'baddl': ok = ok and any(dl(p) and not good(p) for p in R1)
        elif MODE == 'goodatom': ok = ok and not any(good(p) for p in R1)
        elif MODE == 'dlgood': ok = ok and not any(dl(p) and good(p) for p in R1)
        elif MODE in ('uniq', 'uniqany'): ok = ok and sum(1 for p in R1 if good(p) and (MODE == 'uniqany' or dl(p))) >= 2
        elif MODE in ('dpart', 'dpartX'):
            flip = MODE == 'dpartX'
            ok = ok and any(d is not None and le[p][d] and not good(p) and not any(q != p and dl(q) and good(q) and (Zin(jn[p][q]) != flip) for q in R1) for p in atoms)
        elif MODE in ('exch4', 'exch4R', 'exchA'):
            def par(p, q):
                if not (dl(q) and Zin(jn[p][q])): return False
                if good(q): return True
                if MODE == 'exchA': return False
                return dep(q) > dep(p) if MODE == 'exch4' else dep(p) > dep(q)
            ok = ok and any(dl(p) and not good(p) and not any(q != p and par(p, q) for q in R1) for p in R1)
        assert ok, 'SAT/Python mismatch'
        C['SAT'] += 1; INFO[f'h{L.height}'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else: C['UNSAT'] += 1
    E.S.delete()
print(MODE, ' '.join(sorted(FL)), args, dict(C), 'smallest', best[0] if best else None, dict(INFO))
if best and MODE != 'vac':
    json.dump(best[1], open(f'dlatoms_{MODE}{"".join("_" + x for x in sorted(FL))}_min{best[0]}.json', 'w'))
