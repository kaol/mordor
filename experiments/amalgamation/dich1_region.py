"""Dichotomy(1) as a statement about one monotone map (log §34.3z²²⁶).  rank(m) = 2.

G(y) = F(F(⊥, y), y);  Y₁ = {y : m ≰ y, F(⊥, y) an atom < y}.  Under the Dichotomy(1) hypotheses (dich_net.py, with
nopostlayer) a certificate is exactly a G-comparable point of Y₁ (the fibre collapses to a point under R₁ tightness).
Claims (violation searched, re-checked in Python):
  region — some y ∈ Y₁ is G-comparable (= Dichotomy(1) under nopostlayer)
  maxall — every maximal element of Y₁ is G-comparable
  maxex  — some maximal element of Y₁ is G-comparable
  minall / minex — the same for minimal elements of Y₁
  minh2  — some height-2 element of Y₁ (a cover of its atom F(⊥, y)) is G-comparable, i.e. not a gap
  python3 dich1_region.py CLAIM (sweep N MAX | closure K M SEED CNT) [nonpl] [nofeed notop not1 not2 icok]
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
CLAIM = sys.argv[1]; NONPL = 'nonpl' in sys.argv; ABL = {a for a in sys.argv if a in ('nofeed', 'notop', 'not1', 'not2', 'icok', 'icj', 'ictop', 'icorb', 'icorb1', 'icstar')}
args = [a for a in sys.argv[2:] if a != 'nonpl' and a not in ABL]
C = collections.Counter(); best = None
def sc_ystar(L, F, m):                                 # greatest post-fixed point of u ↦ m ⊔ F(m, u) by iteration from ⊤
    u = L.top
    while True:
        v = L.join[m][F[m][u]]
        if v == u: return u
        u = v
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0)
    for m in range(n):
        if h[m] != 2 or L.height <= 2: continue
        feeders = [p for p in L.covers_dn[m] if h[p] == 1]
        if not feeders: continue
        E = Enc(L, 3); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
        add([r(2, m)]); add([-r(1, m)])
        if 'icorb' in ABL or 'icorb1' in ABL or 'icstar' in ABL:   # 'icstar': F(m, u_i) ≰ m for all i, and only at the limit y* = u_N: y* ≰ F(m, y*)          # ¬IC(m) only along m's column orbit u_0 = ⊤, u_{n+1} = m ⊔ F(m, u_n) ('icorb1': u_0, u_1 only)
            U = lambda i, z: E.v('U', i, z); NO = 2 if 'icorb1' in ABL else L.height + 1
            for z in range(n): add([U(0, z)] if z == L.top else [-U(0, z)])
            for i in range(NO - 1):
                for z in range(n):
                    lits = []
                    for v in range(n):
                        for g in range(n):
                            if L.join[m][g] == z: o = E.v('Ust', i, v, g); E.iff_and(o, [U(i, v), f(m, v, g)]); lits.append(o)
                    E.iff_or(U(i + 1, z), lits)
            for i in range(NO):
                for z in range(n):
                    if le[m][z] and z != m:
                        add([-U(i, z), -fle(m, z, m)])
                        if 'icstar' not in ABL or i == NO - 1: add([-U(i, z), -yle(m, z)])
        elif 'icj' in ABL or 'ictop' in ABL:             # ¬IC(m) only at ⊤ ('ictop') or at J = {⊤} ∪ {m ∨ y : h(y) = 2} ('icj')
            J = {L.top} | ({L.join[m][y] for y in range(n) if h[y] == 2 and not le[m][y]} if 'icj' in ABL else set())
            for z in J: add([-fle(m, z, m)]); add([-yle(m, z)])
        elif 'icok' not in ABL: add([-ic(m)])
        if 'notop' not in ABL: add([-r(3, L.top)])
        low = []
        for p in feeders: o = E.v('low', p); E.iff_and(o, [r(1, p), fle(p, m, p)]); low.append(o)
        if 'nofeed' not in ABL: add(low)
        for z in range(n):
            if h[z] > 2 and 'not2' not in ABL: add([-r(2, z)])
            if h[z] > 1 and 'not1' not in ABL: add([-r(1, z)])
            if h[z] == 1 and not NONPL: add([-r(1, z), -yle(z, z)])   # 'nonpl': drop nopostlayer
        atoms = [c for c in range(n) if h[c] == 1]
        inY, comp = {}, {}
        for y in range(n):
            if le[m][y]: continue
            cs = [c for c in atoms if le[c][y] and c != y]
            if not cs: continue
            o = E.v('inY', y); E.iff_or(o, [f(bot, y, c) for c in cs]); inY[y] = o
            lits = []
            for c in cs:
                for t in (fle(c, y, y), yle(c, y)): q = E.v('cmp', y, c, t); E.iff_and(q, [f(bot, y, c), t]); lits.append(q)
            o = E.v('comp', y); E.iff_or(o, lits); comp[y] = o
        ext = {}
        for y in inY:
            others = [y2 for y2 in inY if y2 != y and (le[y][y2] if CLAIM.startswith('max') else le[y2][y])]
            o = E.v('ext', y); E.iff_and(o, [inY[y]] + [-inY[y2] for y2 in others]); ext[y] = o
        if CLAIM == 'region': add([E.v('true')]); [add([-inY[y], -comp[y]]) for y in inY]
        elif CLAIM in ('maxall', 'minall'): add([E.v('sel', y) for y in inY]); [add([-E.v('sel', y), ext[y]]) or add([-E.v('sel', y), -comp[y]]) for y in inY]
        elif CLAIM in ('maxex', 'minex'): [add([-ext[y], -comp[y]]) for y in inY]
        elif CLAIM == 'minh2': [add([-inY[y], -comp[y]]) for y in inY if h[y] == 2]      # some height-2 point of Y₁ is comparable
        elif CLAIM in ('descpred', 'descw', 'descy'):     # pre-fixed fibre column of c* at a canonical column: the descent predecessor ('descpred'), w ('descw'), y* ('descy')
            D = lambda i, z: E.v('D', i, z)
            for z in range(n):
                lits = []
                for yv in range(n): o = E.v('D0', yv, z); E.iff_and(o, [U(NO - 1, yv), f(m, yv, z)]); lits.append(o)
                E.iff_or(D(0, z), lits)
            for i in range(NO):
                for z in range(n):
                    lits = []
                    for v in range(n): o = E.v('Ds', i, v, z); E.iff_and(o, [D(i, v), f(bot, v, z)]); lits.append(o)
                    E.iff_or(D(i + 1, z), lits)
            viol = []
            for i in range(NO):
                for v in range(n):
                    for c in range(n):
                        if h[c] != 1 or v == c or not le[c][v]: continue
                        if CLAIM == 'descpred': o = E.v('pv', i, v, c); E.iff_and(o, [D(i, v), f(bot, v, c), -fle(c, v, v)]); viol.append(o)
            if CLAIM in ('descw', 'descy'):            # c* = F(⊥, w) [x an atom]; is F(c*, w) ≤ w / F(c*, y*) ≤ y*?
                for yv in range(n):
                    for wv in range(n):
                        for c in range(n):
                            if h[c] != 1: continue
                            col = wv if CLAIM == 'descw' else yv
                            o = E.v('pw', yv, wv, c); E.iff_and(o, [U(NO - 1, yv), f(m, yv, wv), f(bot, wv, c), -fle(c, col, col)]); viol.append(o)
            add(viol)
        elif CLAIM in ('descrc', 'descpre', 'descpre2'):                          # the atom c* on the ⊥-descent from w has a RegionCell (z ≱ m, F(⊥, z) = c*, cell of row c* at z)
            D = lambda i, z: E.v('D', i, z)
            for z in range(n):
                lits = []
                for yv in range(n): o = E.v('D0', yv, z); E.iff_and(o, [U(NO - 1, yv), f(m, yv, z)]); lits.append(o)
                E.iff_or(D(0, z), lits)
            for i in range(NO):
                for z in range(n):
                    lits = []
                    for v in range(n): o = E.v('Ds', i, v, z); E.iff_and(o, [D(i, v), f(bot, v, z)]); lits.append(o)
                    E.iff_or(D(i + 1, z), lits)
            At = {}
            for c in range(n):
                if h[c] == 1: At[c] = E.v('datom', c); E.iff_or(At[c], [D(i, c) for i in range(NO + 1)])
            add([E.v('dsel', c) for c in At])
            for c in At:
                add([-E.v('dsel', c), At[c]])
                for z in range(n):
                    if not le[c][z] or z == c or le[m][z]: continue
                    if CLAIM == 'descpre2' and h[z] != 2: continue
                    if CLAIM in ('descpre', 'descpre2'): add([-E.v('dsel', c), -f(bot, z, c), -fle(c, z, z)]); continue
                    add([-E.v('dsel', c), -f(bot, z, c), -fle(c, z, c)]); add([-E.v('dsel', c), -f(bot, z, c), -yle(c, z)])
        elif CLAIM == 'xle1':                            # h(x) ≤ 1
            for yv in range(n):
                for wv in range(n): add([-U(NO - 1, yv), -f(m, yv, wv)] + [f(bot, wv, c) for c in range(n) if h[c] > 1])
        elif CLAIM == 'wcell':                           # x = F(⊥, w) = ⊥ ⟹ row w has a RegionCell (z ≱ m, F(⊥, z) = w, cell of row w at z)
            Wc = {}
            for c in range(n):
                if h[c] != 1: continue
                lits = []
                for yv in range(n):
                    o = E.v('wis0', c, yv); E.iff_and(o, [U(NO - 1, yv), f(m, yv, c), f(bot, c, bot)]); lits.append(o)
                Wc[c] = E.v('wis', c); E.iff_or(Wc[c], lits)
            add(list(Wc.values()))
            for c, wl in Wc.items():
                for z in range(n):
                    if not le[c][z] or z == c or le[m][z]: continue
                    add([-wl, -f(bot, z, c), -fle(c, z, c)]); add([-wl, -f(bot, z, c), -yle(c, z)])
        elif CLAIM == 'xnotbot':                         # x = F(⊥, w) ≠ ⊥
            for yv in range(n):
                for wv in range(n): add([-U(NO - 1, yv), -f(m, yv, wv), f(bot, wv, bot)])
        elif CLAIM == 'xatom':                           # x = F(⊥, w) is an atom
            for yv in range(n):
                for wv in range(n): add([-U(NO - 1, yv), -f(m, yv, wv)] + [f(bot, wv, c) for c in range(n) if h[c] != 1])
        elif CLAIM in ('xicw', 'xicy'):                  # x = F(⊥, w) an atom; row x has a cell in (x, w] ('xicw') / (x, y*] ('xicy')
            for yv in range(n):
                for wv in range(n):
                    for c in range(n):
                        if h[c] != 1: continue
                        base = [-U(NO - 1, yv), -f(m, yv, wv), -f(bot, wv, c)]
                        bound = wv if CLAIM == 'xicw' else yv
                        for z in range(n):
                            if le[c][z] and z != c and le[z][bound]: add(base + [-fle(c, z, c)]); add(base + [-yle(c, z)])
            add([E.v('xa', yv, wv, c) for yv in range(n) for wv in range(n) for c in range(n) if h[c] == 1])
            for yv in range(n):
                for wv in range(n):
                    for c in range(n):
                        if h[c] == 1: E.iff_and(E.v('xa', yv, wv, c), [U(NO - 1, yv), f(m, yv, wv), f(bot, wv, c)])
        elif CLAIM in ('xcell', 'xcellm', 'xic'):        # x = F(⊥, w) an atom ['xcellm': and x ≰ m]; 'xcell(m)': row x has a RegionCell; 'xic': row x has any cell z > x
            Xc = {}
            for c in range(n):
                if h[c] != 1 or (CLAIM == 'xcellm' and le[c][m]): continue
                lits = []
                for yv in range(n):
                    for wv in range(n):
                        o = E.v('xw', c, yv, wv); E.iff_and(o, [U(NO - 1, yv), f(m, yv, wv), f(bot, wv, c)]); lits.append(o)
                Xc[c] = E.v('xis', c); E.iff_or(Xc[c], lits)
            add(list(Xc.values()))
            for c, xl in Xc.items():
                for z in range(n):
                    if not le[c][z] or z == c: continue
                    if CLAIM == 'xic': add([-xl, -fle(c, z, c)]); add([-xl, -yle(c, z)]); continue
                    if le[m][z]: continue
                    add([-xl, -f(bot, z, c), -fle(c, z, c)]); add([-xl, -f(bot, z, c), -yle(c, z)])
        elif CLAIM in ('gfix', 'gfixlow'):              # 'gfix': some g ≱ m with F(F(⊥, g), g) = g and F(⊥, g) an atom ≠ g; 'gfixlow': or a lower point
            for g in range(n):
                if le[m][g]: continue
                for c in range(n):
                    if h[c] != 1 or not le[c][g] or c == g: continue
                    add([-f(bot, g, c), -f(c, g, g)])
                    if CLAIM == 'gfixlow': add([-f(bot, g, c), -f(c, g, c)])
        elif CLAIM in ('minh2in', 'minh2out'):          # witness inside ↓y* ('in') / outside ('out'); y* = u_NO−1 (needs an icorb/icstar flag)
            for y in inY:
                if h[y] != 2: continue
                for z in range(n):
                    if le[y][z] == (CLAIM == 'minh2in'): add([-U(NO - 1, z), -inY[y], -comp[y]])
        if E.S.solve():
            F = E.decode(); G = lambda y: F[F[bot][y]][y]
            Y = [y for y in range(n) if not le[m][y] and h[F[bot][y]] == 1 and le[F[bot][y]][y] and F[bot][y] != y]
            cp = lambda y: le[G(y)][y] or le[y][G(y)]
            mx = [y for y in Y if not any(y2 != y and (le[y][y2] if CLAIM.startswith('max') else le[y2][y]) for y2 in Y)]
            ys = sc_ystar(L, F, m) if CLAIM in ('minh2in', 'minh2out') else None
            gf = lambda g: not le[m][g] and h[F[bot][g]] == 1 and F[bot][g] != g and le[F[bot][g]][g] and (F[F[bot][g]][g] == g or (CLAIM == 'gfixlow' and F[F[bot][g]][g] == F[bot][g]))
            ysx = sc_ystar(L, F, m); xx = F[bot][F[m][ysx]]
            cellx = lambda z: le[xx][z] and z != xx and (le[F[xx][z]][xx] or le[z][F[xx][z]])
            ww = F[m][ysx]
            cellw = lambda z: le[ww][z] and z != ww and (le[F[ww][z]][ww] or le[z][F[ww][z]])
            def desc_atoms():
                v, seen, out = ww, set(), []
                while v not in seen:
                    seen.add(v)
                    if h[v] == 1: out.append(v)
                    v = F[bot][v]
                return out
            rc = lambda c: any(le[c][z] and z != c and not le[m][z] and F[bot][z] == c and (le[F[c][z]][c] or le[z][F[c][z]]) for z in range(n))
            pf = lambda c: any(le[c][z] and z != c and not le[m][z] and F[bot][z] == c and le[F[c][z]][z] for z in range(n))
            def desc_pred():
                v, seen = ww, set()
                while v not in seen:
                    seen.add(v); u = F[bot][v]
                    if h[u] == 1 and u != v: return v, u
                    v = u
                return None
            dp = desc_pred()
            pf2 = lambda c: any(h[z] == 2 and le[c][z] and z != c and not le[m][z] and F[bot][z] == c and le[F[c][z]][z] for z in range(n))
            ok = {'descpre2': any(not pf2(c) for c in desc_atoms()), 'descpred': dp is not None and not le[F[dp[1]][dp[0]]][dp[0]], 'descw': h[xx] == 1 and not le[F[xx][ww]][ww], 'descy': h[xx] == 1 and not le[F[xx][ysx]][ysx], 'descpre': any(not pf(c) for c in desc_atoms()), 'descrc': any(not rc(c) for c in desc_atoms()), 'xle1': h[xx] > 1, 'wcell': xx == bot and h[ww] == 1 and not any(cellw(z) and not le[m][z] and F[bot][z] == ww for z in range(n)), 'xnotbot': xx == bot, 'xatom': h[xx] != 1, 'xicw': h[xx] == 1 and not any(cellx(z) and le[z][ww] for z in range(n)), 'xicy': h[xx] == 1 and not any(cellx(z) and le[z][ysx] for z in range(n)), 'xcell': h[xx] == 1 and not any(cellx(z) and not le[m][z] and F[bot][z] == xx for z in range(n)),
                  'xcellm': h[xx] == 1 and not le[xx][m] and not any(cellx(z) and not le[m][z] and F[bot][z] == xx for z in range(n)),
                  'xic': h[xx] == 1 and not any(cellx(z) for z in range(n)), 'gfix': not any(gf(g) for g in range(n)), 'gfixlow': not any(gf(g) for g in range(n)), 'minh2in': not any(cp(y) for y in Y if h[y] == 2 and le[y][ys]) if ys is not None else True, 'minh2out': not any(cp(y) for y in Y if h[y] == 2 and not le[y][ys]) if ys is not None else True,
                  'minh2': not any(cp(y) for y in Y if h[y] == 2), 'region': not any(cp(y) for y in Y), 'maxall': any(not cp(y) for y in mx), 'minall': any(not cp(y) for y in mx),
                  'maxex': not any(cp(y) for y in mx), 'minex': not any(cp(y) for y in mx)}[CLAIM]
            assert ok, 'SAT/Python mismatch'
            C['violated'] += 1
            if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F, m=m))
        else: C['holds'] += 1
        E.S.delete()
print(CLAIM, 'nonpl' if NONPL else '', sorted(ABL), dict(C), 'smallest violation', best[0] if best else None)
if best: json.dump(best[1], open(f'dich1_{CLAIM}{"_nonpl" if NONPL else ""}{"".join("_" + a for a in sorted(ABL))}_min{best[0]}.json', 'w'))
