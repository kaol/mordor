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
  lgE     — no good atom of R_1 below F(⊥, u), u = the last element of height ≥ 3 on the row-d descent (λ(d) = F(d, u))
  lgPart  — no good atom q ≤ λ(d), q ≠ d, with d ⊔ q ∈ Z (use with hd1 dbad)
  lamZ    — λ(d) is not an element of Z of height 2 above d (use with hd1 dbad)
  lamF0   — F(d, λ(d)) ≠ ⊥ (use with hd1 dbad)
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
LANDMODES = ('lg', 'lgP', 'lgB', 'lgPP', 'coP', 'coC', 'coM1', 'coM2', 'lgE', 'lamZ', 'lamF0', 'lgPart', 'botup', 'botupL', 'cellup', 'botupM1', 'botupM2', 'lamz1', 'btz', 'btall', 'btstep', 'btstepP', 'btstepT', 'btbase', 'rowdrop', 'lamnz')
FLG = {'n1', 'r1t', 'not2', 'h3', 'h4', 'hd1', 'hd2', 'dbad', 'dgood', 'xT', 'xQ', 'xP', 'xD', 'xC', 'cov', 'pre', 'lo2', 'hyp', 'dump', 'N2', 'mz', 'N3', 'xbd', 'xad'}
DUMP = []
MODES = {'vac', 'baddl', 'goodatom', 'dlgood', 'uniq', 'uniqany', 'dpart', 'dpartX', 'exch4', 'exch4R', 'exchA', 'gdnotd', 'badbelowd', 'dlnotd', 'allbadbelowd', 'lg', 'lgP', 'lgB', 'lgPP', 'coP', 'coC', 'coM1', 'coM2', 'lgE', 'lamZ', 'lamF0', 'lgPart', 'botup', 'botupL', 'cellup', 'botupM1', 'botupM2', 'lamz1', 'btz', 'btall', 'btstep', 'btstepP', 'btstepT', 'btbase', 'rowdrop', 'lamnz'}
MODE = sys.argv[1]; FL = {a for a in sys.argv[2:] if a in FLG}; args = [a for a in sys.argv[2:] if a not in FLG]
if MODE not in MODES: raise SystemExit('unknown mode')
MEANING = {
    'vac': 'SAT = the world has a model (hypothesis only)',
    'baddl': 'SAT = some DL atom of R_1 is bad',
    'goodatom': 'SAT = every atom of R_1 is bad (refutes GoodAtom1)',
    'dlgood': 'SAT = every DL atom of R_1 is bad (refutes DLGood)',
    'uniq': 'SAT = two DL atoms of R_1 are good (refutes ExactlyOne uniqueness)',
    'uniqany': 'SAT = two atoms of R_1 are good (mutant: DL dropped)',
    'dpart': 'SAT = some atom p <= d is bad and no good DL atom q != p has p v q in Z (refutes DPartner)',
    'dpartX': 'SAT = mutant of dpart with p v q not in Z',
    'exch4': 'SAT = some bad DL atom has no DL partner (p v q in Z) that is good or deeper (refutes DepthExchange)',
    'exch4R': 'SAT = mutant: deeper reversed', 'exchA': 'SAT = mutant: partner must be good',
    'gdnotd': 'SAT = some good DL atom of R_1 is not below d',
    'badbelowd': 'SAT = SOME atom below d is bad (not: every)',
    'allbadbelowd': 'SAT = EVERY atom below d is bad',
    'dlnotd': 'SAT = some DL atom of R_1 is not below d',
    'lg': 'SAT = no good atom of R_1 lies below lambda(d) (refutes LandGood)',
    'lgP': 'SAT = no good atom of R_1 lies below F(d, lambda(d)) (refutes LandGood+)',
    'lgB': 'SAT = no good atom below lambda(bot) (mutant)', 'lgPP': 'SAT = no good atom below F(d, F(d, lambda(d))) (mutant)',
    'lgE': 'SAT = no good atom below F(bot, u), u the high predecessor of lambda(d) (refutes LandGoodE)',
    'lgPart': 'SAT = no good atom q != d, q <= lambda(d), with d v q in Z (refutes PartLand)',
    'coP': 'SAT = no atom q <= d ^ lambda(d) lands at lambda(d) (refutes CoLand)',
    'coC': 'SAT = no good atom q <= d ^ lambda(d)',
    'coM1': 'SAT = some atom below d does not co-land (mutant)', 'coM2': 'SAT = some atom p below d has F(p, lambda(d)) not >= p (mutant)',
    'lamZ': 'SAT = lambda(d) is not an element of Z of height 2 above d', 'lamF0': 'SAT = F(d, lambda(d)) != bot',
    'botup': 'SAT = no x in Z with d <= x has an atom q <= x with q <= F(bot, lambda(x)) (refutes BotUp)',
    'botupL': 'SAT = as botup, with q also <= lambda(d) required (refutes BotUpL)',
    'cellup': 'SAT = no x in Z with d <= x has an atom q <= x with q <= F(q, lambda(x)) (refutes CellUp)',
    'botupM1': 'SAT = as botup with the column F(x, lambda(x)) (mutant M1step)',
    'botupM2': 'SAT = no x in Z of height 2 with d not <= x has an atom q <= x, q <= F(bot, lambda(x)) (mutant M2anchor)',
    'btz': 'SAT = case (a): no atom q <= d with q <= F(bot, z) and q <= F(bot, lambda(d)), z = last row-d descent element >= d (refutes BotTrack endpoint)',
    'btall': 'SAT = case (a): no atom q <= d with q <= F(bot, y) for every row-d descent element y with lambda(d) <= y <= z (refutes BotTrack)',
    'btstep': 'SAT = case (a): some atom q <= d and some y of height >= 3 with q <= F(bot, y) but q not <= F(bot, F(d, y)) (refutes the local BotTrack step)',
    'btstepP': 'SAT = case (a): some atom q <= d, some y of height >= 3 with F(d, y) <= y and q <= F(bot, y) but q not <= F(bot, F(d, y))',
    'lamnz': '[hyp asserts no claim] SAT = the landing lambda(d) of row d lies in Z, i.e. F(bot, lambda(d)) = bot (refutes LamNZ)',
    'rowdrop': '[flags: N2 / N3 require N >= 2 / 3; hyp asserts no claim; not2 drops R_2 tightness (mutant); xbd adds F(d, s) not <= d for s = F(bot, (F d)^(N-1) top); xad (with xbd) adds s not <= F(d, s)] SAT = case (a): d = (F bot)^N top, and F(bot, (F d)^(N-1) top) not <= d (refutes RowDrop)',
    'btbase': '[flags: N2 requires d != F(bot, top); mz tests F(bot, z) instead; hyp asserts no claim] SAT = case (a): z = last row-d descent element >= d, t = F(d, z), and F(bot, t) not <= d (refutes BaseD)',
    'btstepT': '[flags: xC drops q <= F(bot, y); cov tests q <= F(bot, y) itself; pre tests F(bot, d v F(bot, y)) <= F(bot, y); hyp asserts no claim (SAT = the hypothesis has a model)] SAT = case (a): z = last row-d descent element >= d, t = F(d, z), q an atom <= d ^ F(bot, z); some y of height >= 3 with y <= t, d not <= y, q <= y, q <= F(bot, y), F(d, y) <= y, but q not <= F(bot, F(d, y))',
    'lamz1': 'SAT = d bad atom, row d lands at the index N of d on the bot-descent (b1), and lambda(d) not in Z (refutes LamZ1)',
}
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
    if 'dgood' in FL:
        for z in range(n):
            if z != bot: add([-isd(z), gd(z)])
    LAND = LANDMODES
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
        pe = {}
        if MODE == 'lgE':
            for v in range(n):
                o = E.v('pe', v); ls = []
                for e in range(n):
                    if e == bot: continue
                    for u in range(n):
                        if h[u] < 3: continue
                        for z in low:
                            t = E.v('pet', e, u, z, v); E.iff_and(t, [isd(e), on(e, u), f(e, u, z), f(bot, u, v)]); ls.append(t)
                E.iff_or(o, ls); pe[v] = o
        def region(p):
            o = E.v('reg', p)
            if MODE in ('lg', 'coP', 'coC', 'coM1'): E.iff_or(o, [lamd[z] for z in low if le[p][z]])
            elif MODE == 'lgP': E.iff_or(o, [pd[v] for v in range(n) if le[p][v]])
            elif MODE == 'lgPP': E.iff_or(o, [pdd[v] for v in range(n) if le[p][v]])
            elif MODE == 'lgB': E.iff_or(o, [on(bot, z) for z in low if le[p][z] and z != bot])
            elif MODE == 'lgE': E.iff_or(o, [pe[v] for v in range(n) if le[p][v]])
            elif MODE == 'lgPart':
                t1 = E.v('lpr1', p); E.iff_or(t1, [lamd[z] for z in low if le[p][z]])
                t2 = E.v('lpr2', p); E.iff_or(t2, [E.v('lprd', p, e) for e in range(n) if e != bot and e != p])
                for e in range(n):
                    if e != bot and e != p: E.iff_and(E.v('lprd', p, e), [isd(e), f(bot, jn[p][e], bot)])
                E.iff_and(o, [t1, t2])
            return o
        if MODE == 'btstepT':
            sel = []
            for e in range(n):
                if h[e] != 2: continue
                De = descvars(e)
                onv = {z: on(e, z) for z in range(n)}
                for z in range(n):
                    if not le[e][z]: continue
                    zdv = E.v('tzd', e, z); E.iff_and(zdv, [onv[z]] + [-onv[w] for w in range(n) if le[e][w] and le[w][z] and w != z])
                    for tt in range(n):
                        for q in atoms:
                            if not (le[q][e] and le[q][tt]): continue
                            for y in range(n):
                                if h[y] < (2 if 'lo2' in FL else 3) or y == q or ('xD' not in FL and le[e][y]) or ('xT' not in FL and not le[y][tt]) or not le[q][y]: continue
                                # pre with xP: y2 is unconstrained, so one selector per y (F total makes OR_y2 f(e,y,y2) true)
                                for y2 in ([None] if ('pre' in FL and 'xP' in FL) else range(n)):
                                    if y2 is not None and 'xP' not in FL and not le[y2][y]: continue
                                    o = E.v('bsT', e, z, tt, q, y, y2); sel.append(o)
                                    add([-o, isd(e)]); add([-o, zdv]); add([-o, f(e, z, tt)])
                                    if y2 is not None: add([-o, f(e, y, y2)])
                                    if 'xQ' not in FL: add([-o] + [f(bot, z, v) for v in range(n) if le[q][v]])
                                    if 'hyp' in FL: continue
                                    if 'pre' in FL:
                                        # violation witness: F(bot, y) = w and F(bot, e v w) = w2 with w2 not <= w
                                        vs = []
                                        for w in range(n):
                                            for w2 in range(n):
                                                if le[w2][w]: continue
                                                pv = E.v('prv', e, y, w, w2); E.iff_and(pv, [f(bot, y, w), f(bot, L.join[e][w], w2)]); vs.append(pv)
                                        add([-o] + vs)
                                        continue
                                    if 'cov' in FL:
                                        for v in range(n):
                                            if le[q][v]: add([-o, -f(bot, y, v)])
                                        continue
                                    if 'xC' not in FL: add([-o] + [f(bot, y, v) for v in range(n) if le[q][v]])
                                    for v in range(n):
                                        if le[q][v]: add([-o, -f(bot, y2, v)])
            add(sel)
        if MODE == 'btbase':
            sel = []
            for e in range(n):
                if h[e] != 2: continue
                onv = {z: on(e, z) for z in range(n)}
                if 'N2' in FL: add([-isd(e), -f(bot, top, e)])
                for z in range(n):
                    if not le[e][z]: continue
                    zdv = E.v('tzd', e, z); E.iff_and(zdv, [onv[z]] + [-onv[w] for w in range(n) if le[e][w] and le[w][z] and w != z])
                    for tt in range(n):
                        o = E.v('bbs', e, z, tt); sel.append(o)
                        add([-o, isd(e)]); add([-o, zdv]); add([-o, f(e, z, tt)])
                        if 'hyp' in FL: continue
                        col = z if 'mz' in FL else tt
                        add([-o] + [f(bot, col, v) for v in range(n) if not le[v][e]])
            add(sel)
        if MODE == 'lamnz':
            sel = []
            for z in low:
                o = E.v('lnz', z); sel.append(o); add([-o, lamd[z]])
                if 'hyp' not in FL: add([-o, f(bot, z, bot)])
            add(sel)
        if MODE == 'rowdrop':
            sel = []
            for e in range(n):
                if h[e] != 2: continue
                De = descvars(e)
                if 'N2' in FL or 'N3' in FL: add([-isd(e), -Db(1, e)])
                if 'N3' in FL: add([-isd(e), -Db(2, e)])
                for i in range(NO):
                    for w in range(n):
                        o = E.v('rds', e, i, w); sel.append(o)
                        add([-o, isd(e)]); add([-o, Db(i + 1, e)]); add([-o, De(i, w)])
                        if 'hyp' in FL: continue
                        if 'xbd' in FL:   # s = F(bot, w) with s not <= e and F(e, s) not <= e
                            for sv in range(n):
                                if le[sv][e]: continue
                                o2 = E.v('rdx', e, i, w, sv); add([-o2, f(bot, w, sv)]); add([-o2] + [f(e, sv, x) for x in range(n) if not le[x][e]])
                                if 'xad' in FL: add([-o2] + [f(e, sv, x) for x in range(n) if not le[sv][x]])   # s not <= F(e, s)
                            add([-o] + [E.v('rdx', e, i, w, sv) for sv in range(n) if not le[sv][e]])
                            continue
                        add([-o] + [f(bot, w, v) for v in range(n) if not le[v][e]])
            add(sel)
        if MODE in ('btstep', 'btstepP'):
            sel = []
            for e in range(n):
                if h[e] != 2: continue
                for q in atoms:
                    if not le[q][e]: continue
                    for y in range(n):
                        if h[y] < 3: continue
                        for y2 in range(n):
                            t = E.v('bst', e, q, y, y2); sel.append(t)
                            add([-t, isd(e)]); add([-t, f(e, y, y2)])
                            if MODE == 'btstepP' and not le[y2][y]: add([-t])
                            add([-t] + [f(bot, y, v) for v in range(n) if le[q][v]])
                            for v in range(n):
                                if le[q][v]: add([-t, -f(bot, y2, v)])
            add(sel)
        if MODE in ('btz', 'btall'):
            for e in range(n):
                if h[e] != 2: continue
                De = descvars(e)
                onv = {z: on(e, z) for z in range(n)}
                # zd(z): z is the last descent element >= e (smallest such)
                zd = {}
                for z in range(n):
                    if not le[e][z]: continue
                    o = E.v('btzd', e, z); E.iff_and(o, [onv[z]] + [-onv[w] for w in range(n) if le[e][w] and le[w][z] and w != z]); zd[z] = o
                qs = [q for q in atoms if le[q][e]]
                ok_q = []
                for q in qs:
                    cov = lambda y: E.v('btcov', q, y)
                    for y in range(n): E.iff_or(cov(y), [f(bot, y, v) for v in range(n) if le[q][v]])
                    if MODE == 'btz':
                        t = E.v('btq', e, q); ls = []
                        for z in zd:
                            for w in low:
                                tt = E.v('btqz', e, q, z, w); E.iff_and(tt, [zd[z], lam(e, w), cov(z), cov(w)]); ls.append(tt)
                        E.iff_or(t, ls); ok_q.append(t)
                    else:
                        # for every y on the descent between lambda(e) and z: cov(y)
                        t = E.v('btq', e, q); conds = []
                        for z in zd:
                            for w in low:
                                if not le[w][z]: continue
                                bad = []
                                for y in range(n):
                                    if le[w][y] and le[y][z]:
                                        b_ = E.v('btbad', e, q, z, w, y); E.iff_and(b_, [onv[y], -cov(y)]); bad.append(b_)
                                nb = E.v('btnb', e, q, z, w); E.iff_or(nb, bad)
                                tt = E.v('btqz', e, q, z, w); E.iff_and(tt, [zd[z], lam(e, w), -nb]); conds.append(tt)
                        E.iff_or(t, conds); ok_q.append(t)
                for t in ok_q: add([-isd(e), -t])
        if MODE in ('botup', 'botupL', 'cellup', 'botupM1', 'botupM2'):
            for x in range(n):
                if x == bot or x == top: continue
                if MODE == 'botupM2' and h[x] != 2: continue
                qs = [q for q in atoms if le[q][x]]
                if not qs: continue
                ls = []
                for z in low:
                    for q in qs:
                        if MODE == 'botupM1':
                            for z2 in range(n):
                                t = E.v('bu1', x, z, q, z2); E.iff_and(t, [lam(x, z), f(x, z, z2), E.v('bucv', z2, q)]); ls.append(t)
                                E.iff_or(E.v('bucv', z2, q), [f(bot, z2, v) for v in range(n) if le[q][v]])
                        else:
                            cv = E.v('bucc', x, z, q)
                            row = q if MODE == 'cellup' else bot
                            E.iff_or(cv, [f(row, z, v) for v in range(n) if le[q][v]])
                            parts = [lam(x, z), cv]
                            if MODE == 'botupL': parts.append(E.v('bul', q)); E.iff_or(E.v('bul', q), [lamd[w] for w in low if le[q][w]])
                            t = E.v('bu', x, z, q); E.iff_and(t, parts); ls.append(t)
                cx = E.v('bux', x); E.iff_or(cx, ls)
                dl_ = E.v('budle', x); E.iff_or(dl_, [isd(e) for e in range(n) if e != bot and le[e][x]])
                add([-f(bot, x, bot), (dl_ if MODE == 'botupM2' else -dl_), -cx])
        if MODE == 'lamz1':
            sel = []
            for e in range(n):
                if e == bot: continue
                De = descvars(e)
                for i in range(NO + 1):
                    for z in low:
                        for w in low:
                            t = E.v('lz1', e, i, z, w); sel.append(t)
                            add([-t, isd(e)]); add([-t, Db(i, e)]); add([-t, De(i, z)]); add([-t, lam(e, w)]); add([-t, -f(bot, w, bot)])
            add(sel)
        if MODE in ('lamZ', 'lamF0'):
            sel = []
            for e in range(n):
                if e == bot: continue
                for z in low:
                    t = E.v('lzs', e, z); sel.append(t); add([-t, isd(e)]); add([-t, lam(e, z)])
                    if MODE == 'lamF0': add([-t, -f(e, z, bot)])
                    elif le[e][z] and h[z] == 2: add([-t, -f(bot, z, bot)])
            add(sel)
        if MODE in ('lg', 'lgP', 'lgB', 'lgPP', 'lgE', 'lgPart'):
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
        if 'dgood' in FL: ok = ok and d is not None and good(d)
        if MODE in LANDMODES:
            lamf = lambda e: next((z for z in desc(e) if h[z] <= 2), None)   # None only without R_2 tightness (not2)
            ld = lamf(d)
            if MODE == 'lg': reg = lambda p: ld is not None and le[p][ld]   # no landing (only without tightness): empty region
            elif MODE == 'lgP': reg = lambda p: le[p][F[d][ld]]
            elif MODE == 'lgPP': reg = lambda p: le[p][F[d][F[d][ld]]]
            elif MODE == 'lgB': reg = lambda p: le[p][lamf(bot)]
            elif MODE == 'lgPart': reg = lambda p: p != d and le[p][ld] and F[bot][jn[p][d]] == bot
            elif MODE == 'lgE':
                dsd = desc(d); uu = dsd[dsd.index(ld) - 1]; ev = F[bot][uu]
                reg = lambda p: le[p][ev]
            else: reg = lambda p: le[p][ld]
            if MODE in ('lg', 'lgP', 'lgB', 'lgPP', 'lgE', 'lgPart'): ok = ok and not any(reg(p) and good(p) for p in R1)
            elif MODE == 'coP': ok = ok and not any(le[q][d] and reg(q) and lamf(q) == ld for q in R1)
            elif MODE == 'coC': ok = ok and not any(le[q][d] and reg(q) and good(q) for q in R1)
            elif MODE == 'coM1': ok = ok and any(le[p][d] and lamf(p) != ld for p in R1)
            elif MODE in ('botup', 'botupL', 'cellup', 'botupM1', 'botupM2'):
                def holds_x(x):
                    if x in (bot, top) or F[bot][x] != bot: return False
                    if MODE == 'botupM2':
                        if h[x] != 2 or le[d][x]: return False
                    elif not le[d][x]: return False
                    lx = lamf(x); col = F[x][lx] if MODE == 'botupM1' else lx
                    for q in atoms:
                        if not le[q][x]: continue
                        val = F[q][col] if MODE == 'cellup' else F[bot][col]
                        if le[q][val] and (MODE != 'botupL' or le[q][ld]): return True
                    return False
                ok = ok and not any(holds_x(x) for x in range(n))
            elif MODE == 'btstepT':
                dsd = desc(d); zz = [y for y in dsd if le[d][y]][-1]; tt = F[d][zz]
                ok = ok and h[d] == 2 and any(le[q][d] and ('xQ' in FL or le[q][F[bot][zz]]) and h[y] >= (2 if 'lo2' in FL else 3) and y != q and ('xT' in FL or le[y][tt]) and ('xD' in FL or not le[d][y]) and le[q][y]
                                              and ('hyp' in FL or ('pre' in FL and not le[F[bot][L.join[d][F[bot][y]]]][F[bot][y]]) or ('cov' in FL and not le[q][F[bot][y]]) or ('cov' not in FL and 'pre' not in FL and ('xC' in FL or le[q][F[bot][y]]) and ('xP' in FL or le[F[d][y]][y]) and not le[q][F[bot][F[d][y]]])) for q in atoms for y in range(n))
            elif MODE == 'lamnz':
                ok = ok and ld is not None and ('hyp' in FL or F[bot][ld] == bot)
            elif MODE == 'rowdrop':
                Nd = bd.index(d); vv = top
                for _ in range(Nd - 1): vv = F[d][vv]
                ok = ok and h[d] == 2 and ('N2' not in FL or Nd >= 2) and ('N3' not in FL or Nd >= 3) and ('hyp' in FL or not le[F[bot][vv]][d])
                if 'xbd' in FL: ok = ok and not le[F[d][F[bot][vv]]][d]
                if 'xad' in FL: ok = ok and not le[F[bot][vv]][F[d][F[bot][vv]]]
            elif MODE == 'btbase':
                dsd = desc(d); zz = [y for y in dsd if le[d][y]][-1]; tt = F[d][zz]
                ok = ok and h[d] == 2 and ('N2' not in FL or F[bot][top] != d) and ('hyp' in FL or not le[F[bot][zz if 'mz' in FL else tt]][d])
            elif MODE in ('btstep', 'btstepP'):
                ok = ok and h[d] == 2 and any(le[q][d] and h[y] >= 3 and (MODE == 'btstep' or le[F[d][y]][y]) and le[q][F[bot][y]] and not le[q][F[bot][F[d][y]]] for q in atoms for y in range(n))
            elif MODE in ('btz', 'btall'):
                dsd = desc(d); zz = [y for y in dsd if le[d][y]][-1]
                def okq(q):
                    if not le[q][d]: return False
                    if MODE == 'btz': return le[q][F[bot][zz]] and le[q][F[bot][ld]]
                    return all(le[q][F[bot][y]] for y in dsd if le[ld][y] and le[y][zz])
                ok = ok and h[d] == 2 and not any(okq(q) for q in atoms)
            elif MODE == 'lamz1':
                N = bd.index(d); it = top
                for _ in range(N): it = F[d][it]
                ok = ok and h[it] <= 2 and F[bot][ld] != bot
            elif MODE == 'lamZ': ok = ok and not (le[d][ld] and h[ld] == 2 and F[bot][ld] == bot)
            elif MODE == 'lamF0': ok = ok and F[d][ld] != bot
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
        if 'dump' in FL: DUMP.append(dict(sets=L.S, F=F))
        C['SAT'] += 1; INFO[f'h{L.height}'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else: C['UNSAT'] += 1
    E.S.delete()
print(MODE, '|', MEANING.get(MODE, '?'), '|', ' '.join(sorted(FL)), args, dict(C), 'smallest', best[0] if best else None, dict(INFO))
if DUMP: json.dump(DUMP, open(f'dump_{MODE}{"".join("_" + x for x in sorted(FL))}.json', 'w'))
if best and MODE != 'vac':
    json.dump(best[1], open(f'dlatoms_{MODE}{"".join("_" + x for x in sorted(FL))}_min{best[0]}.json', 'w'))
