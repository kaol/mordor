"""§34.3z²⁶⁹ (worker re-encoding, independent of the control brief's lamchase.py): the landing map mu on Z.
World W0 at level 1 (a(bot) = bot, R_2 tight, top not in R_2) with n1 (R_1 = Z not tight).
  lambda(x) = the first element of height <= 2 on row x's descent from top;
  mu(x) = lambda(x) if lambda(x) in Z, else F(bot, lambda(x))           (x in Z; mu(bot) = d)
Encoding: exact descent iterates it(x, j, .) (one-hot, j <= height); on(x, p) = OR_j it(x, j, p); lambda(x) = the low
(h <= 2) element on the descent with no other low descent element above it; mu as a relation; a mu-closed set O.
Modes:
  botorbit  SAT = BotOrbit fails: the mu-orbit of bot never reaches a fixed point
            (a mu-closed O containing bot with no fixed point of mu in O)
  muloop    SAT = MuLoop fails: some nonempty mu-closed O inside Z \\ {bot} has no fixed point
  vac       SAT = the world has a model
  orbk K    SAT = mu^K(bot) is not a fixed point (Orbit_K fails)
  tcase 1|2|3  SAT = L1(d) fails | L1(e) fails | L2 fails (see MEAN)
Flags: not2 (mutant: R_2 tightness dropped; then descents may not land, and such rows are excluded from O);
  with not2, role facts (in tcase 3 and 8): Rd, Re, Rb = (T) at row d, e, bot; Rq = at row q = F(bot, lambda(e)) (tcase 8)
  or at row lambda(e) (tcase 3);
  with not2, partial facts: Tb (no Z-row lower cell at a high column), Ta (no Z-row upper cell at a high column), ZT (Z heights <= 2)
Every SAT model is replayed in Python (stages, a_of, direct computation of lambda, mu and the orbit).
  python3 muorbit_sat.py MODE [K] (sweep N MAX | closure K M SEED CNT) [minh H maxn N] [flags]"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import lattices
from rstages import stages, a_of
MODE = sys.argv[1]; K = 0
if MODE in ('orbk', 'tcase', 'orbdep'): K = int(sys.argv[2]); sys.argv.pop(2)
FL = {a for a in sys.argv[2:] if a in ('not2', 'Ta', 'Tb', 'ZT', 'Rd', 'Re', 'Rq', 'Rb', 'Rj', 'Rw', 'Rr', 'Rl', 'Rm', 'mBad', 'mR', 'mK', 'mTop', 'mN1', 'cT', 'cR', 'cP', 'ns', 'ex1', 'yf', 'ed')}; args = [a for a in sys.argv[2:] if a not in FL]
import os
DUMP = [] if os.environ.get('DUMP') else None
MEAN = {'botorbit': 'BotOrbit fails: the mu-orbit of bot never reaches a fixed point',
        'orbdep': ('ExactDrop fails: some x_k = mu^k(bot), k >= 1, in-steps to a non-fixed y with dep(y) <= dep(x_k) - 2' if 'ed' in sys.argv else 'OneExit fails: some x_k = mu^k(bot), k >= 1, exits to an atom that is not a fixed point of mu' if 'ex1' in sys.argv else f'StrictDep fails: within {K} steps some non-fixed element x_k = mu^k(bot), k >= 1, has a non-fixed successor x_(k+1) with dep(x_(k+1)) >= dep(x_k), dep(x) = max j with x <= t_j' + (' [nonstrict: dep(x_(k+1)) > dep(x_k)]' if 'ns' in sys.argv else '')), 'muloop': 'MuLoop fails: a nonempty mu-closed set in Z* without fixed point', 'vac': 'the world has a model', 'orbk': f'Orbit{K} fails: mu^{K}(bot) is not a fixed point of mu', 'tcase': {1: 'L1(d) fails: d exits to q = F(bot, lambda(d)) with lambda(q) != lambda(d)', 2: 'L1(e) fails: d in-steps to e, e exits to q with lambda(q) != lambda(e)', 3: 'L2 fails: d in-steps to e and e in-steps', 4: 'hypothesis of L1(e)/L2: d in-steps to e (vacuity run)', 5: 'Fix1 fails: d exits to q = F(bot, lambda(d)) and mu(q) != q', 6: 'hypothesis of Fix1: d exits (vacuity run)', 25: 'DropProp fails: w in Z* in-steps to x in Z, x in-steps to y in Z, dep(x) < dep(w) and dep(y) >= dep(x)', 24: 'ExitBelow fails: some row x lands at p, q = F(bot, p) != bot, and q is not below some element of height >= 3 on the bot-descent', 23: 'InStepU fails: the breakpoint w lands at p in Z with predecessor u >= p, and u is not below F(p, u)', 22: 'InStepUp fails: the breakpoint w lands at p in Z (predecessor u >= p), and row p has no upper cell at any high y >= p on row w descent', 21: 'BreakExit fails: d a bad atom and the breakpoint w lands in Z (in-steps)', 20: 'BreakDom fails: d a bad atom, the breakpoint w exits at p and F(bot, p) is not below w', 19: 'hypothesis of BreakCert: d is a bad atom (vacuity / data run)', 18: 'JoinCert fails: L2 fails, or for the first exiting point z with exit atom q no atom r <= z has r v q in Z with the row r v q exiting to q', 17: 'TopCell fails: d is not a good atom and no height-2 row m of Z has q = m meet lambda(m) an atom with q <= F(q, lambda(m))', 16: 'BreakCert fails: d is a bad atom, and the breakpoint w = r meet t_k (r = last element of row d descent that is >= d; t_k -> t_k+1 the step of the bot-descent where r meet t first drops to d) is not a dominated exit (or not a height-2 element of Z)', 15: 'OrbitDom fails: d in-steps twice (L2 fails), or the first exiting point z of the chain from d exits to q and no row x2 in Z* with q <= x2 exits to q', 14: 'ExitDom fails: some x in Z* exits to an atom q, and no row x2 in Z* with q <= x2 exits to q', 13: 'QEany fails: some x in Z* in-steps to y = lambda(x) in Z*, y exits at p, and F(bot, p) is not below y', 10: 'StallQ fails: some x in Z* exits at p with q = F(bot, p) <= x and F(q, p) != p', 12: 'StallQ2 fails: some x in Z* exits at p with q = F(bot, p) <= x, q != x and F(q, p) != p', 11: 'StallX fails: some x in Z* exits at p and F(x, p) != p', 9: 'DomCoLand fails: some x in Z* exits at p with q = F(bot, p) <= x and lambda(q) != p', 8: 'QE fails: d in-steps to e, e exits at p, and q = F(bot, p) is not below e', 7: 'Follow fails: d in-steps to e, e exits at p with high predecessor u, q = F(bot, p), and u is not on row q descent'}.get(K, '?')}
print(f'muorbit_sat {MODE} | SAT = {MEAN[MODE]} | world W0 + n1 | flags {sorted(FL)} | corpus {args}')
C = collections.Counter(); HH = collections.Counter(); best = None
MINH = MAXN = None
if 'minh' in args: k_ = args.index('minh'); MINH = int(args[k_ + 1]); MAXN = int(args[k_ + 3]); args = args[:k_]   # ... minh H maxn N
for L in lattices(args):
    if MINH is not None and (L.height < MINH or L.n > MAXN): continue
    n = L.n; le = L.le; h = L.rank; top = L.top; bot = L.bot; NO = L.height + 1; jn = L.join
    if L.height < 3: continue
    E = Enc(L, 2); f = lambda a, b, u: E.v('f', a, b, u); r = lambda i, z: E.v('r', i, z); add = E.S.add_clause
    add([E.v('A', bot, bot)])
    if 'mTop' not in FL: add([-r(2, top)])
    if 'not2' not in FL:
        for z in range(n):
            if h[z] > 2: add([-r(2, z)])
    if 'mN1' not in FL: add([r(1, z) for z in range(n) if h[z] > 1])
    for x in range(n):                                   # partial tightness facts (used with not2)
        for y in range(n):
            if h[y] <= 2: continue
            for w in range(n):
                if 'Tb' in FL and le[w][x]: add([-f(bot, x, bot), -f(x, y, w)])      # no lower cell of a Z-row at a high column
                if 'Ta' in FL and le[y][w]: add([-f(bot, x, bot), -f(x, y, w)])      # no upper cell of a Z-row at a high column
        if 'ZT' in FL and h[x] > 2: add([-f(bot, x, bot)])                           # Z has heights <= 2
    rows = [x for x in range(n) if h[x] <= 2 or 'not2' in FL]
    inZ = lambda x: f(bot, x, bot)
    def Trow(guard, z):                                   # role-level (T): row z has no cell at a column of height >= 3
        for w_ in range(n):
            if h[w_] <= 2: continue
            for v_ in range(n):
                if le[v_][z] or le[w_][v_]: add(guard + [-f(z, w_, v_)])
    low = [p for p in range(n) if h[p] <= 2]
    lam = {}
    for x in rows:
        it = lambda j, z: E.v('it', x, j, z)
        for z in range(n): add([it(0, z)] if z == top else [-it(0, z)])
        for j in range(NO):
            for z in range(n):
                for w in range(n): add([-it(j, z), -f(x, z, w), it(j + 1, w)])
            # at most one element per index: with it(0) = top and forward propagation this makes it(j, .) the exact iterate
            for w in range(n):
                for w2 in range(w + 1, n): add([-it(j + 1, w), -it(j + 1, w2)])
        on = {z: E.v('on', x, z) for z in range(n)}
        for z in range(n): E.iff_or(on[z], [it(j, z) for j in range(NO + 1)])
        for p in low:
            o = E.v('lam', x, p); E.iff_and(o, [on[p]] + [-on[w] for w in low if w != p and not le[w][p]]); lam[x, p] = o
            # a low descent element that is not below p cannot exist when p is the first low one (descent decreasing)
    mu = {}
    for x in rows:
        for y in range(n):
            ls = []
            if y in low:
                t = E.v('muin', x, y); E.iff_and(t, [lam[x, y], inZ(y)]); ls.append(t)
            for p in low:
                t = E.v('muex', x, p, y); E.iff_and(t, [lam[x, p], -inZ(p), f(bot, p, y)]); ls.append(t)
            o = E.v('mu', x, y); E.iff_or(o, ls); mu[x, y] = o
    O = {x: E.v('O', x) for x in range(n)}
    for x in range(n):
        if x not in rows: add([-O[x]]); continue
        add([-O[x], inZ(x)])                                   # O inside Z
        add([-O[x]] + [lam[x, p] for p in low])               # rows in O land (automatic under tightness)
        add([-O[x], -mu[x, x]])                                # no fixed point in O
        for y in range(n):
            if y in rows: add([-O[x], -mu[x, y], O[y]])        # O is mu-closed
            else: add([-O[x], -mu[x, y]])
    if MODE == 'orbdep':                                     # StrictDep: exact orbit positions; dep via the exact bot-descent
        add([-O[x] for x in range(n)])
        o = lambda k, x: E.v('ob', k, x)
        for x in range(n): add([o(0, x)] if x == bot else [-o(0, x)])
        for k in range(K):
            for x in rows:
                add([-o(k, x)] + [lam[x, p] for p in low])
                for y in range(n): add([-o(k, x), -mu[x, y], o(k + 1, y)])
            for x in range(n):
                if x not in rows: add([-o(k, x)])
            for y in range(n):
                for y2 in range(y + 1, n): add([-o(k + 1, y), -o(k + 1, y2)])
        Dge = {}
        for x in range(n):                                   # Dge(x, j) <-> x <= t_j
            for j in range(NO + 1):
                Dge[x, j] = E.v('dge', x, j); E.iff_or(Dge[x, j], [E.v('it', bot, j, t) for t in range(n) if le[x][t]])
        sel = []
        if 'ex1' in FL:                                      # OneExit fails: some x_k (k >= 1) exits to an atom y with mu(y) != y
            for k in range(1, K):
                for x in rows:
                    if x == bot: continue
                    for p in low:
                        for y in rows:
                            t = E.v('ox', k, x, p, y); sel.append(t)
                            for lit in [o(k, x), lam[x, p], -inZ(p), f(bot, p, y), -mu[y, y]]: add([-t, lit])
            add(sel); sel = None
        for k in (range(1, K) if sel is not None else []):
            for x in rows:
                if x == bot: continue
                for y in rows:
                    if y == x: continue
                    t = E.v('od', k, x, y); sel.append(t)
                    add([-t, o(k, x)]); add([-t, o(k + 1, y)]); add([-t, -mu[y, y]])   # y = mu(x) not a fixed point
                    if 'ed' in FL:                           # ExactDrop fails: x in-steps to y and dep(y) <= dep(x) - 2
                        add([-t, lam[x, y]]); add([-t, inZ(y)])
                        add([-t] + [E.v('edj', k, x, y, j) for j in range(1, NO + 1)])
                        for j in range(1, NO + 1): add([-E.v('edj', k, x, y, j), Dge[x, j]]); add([-E.v('edj', k, x, y, j), -Dge[y, j - 1]])
                        continue
                    if 'ns' in FL:                           # dep(y) > dep(x): some j with y <= t_j, x not <= t_j
                        add([-t] + [E.v('odj', k, x, y, j) for j in range(NO + 1)])
                        for j in range(NO + 1): add([-E.v('odj', k, x, y, j), Dge[y, j]]); add([-E.v('odj', k, x, y, j), -Dge[x, j]])
                    else:                                    # dep(y) >= dep(x): every j with x <= t_j has y <= t_j
                        for j in range(NO + 1): add([-t, -Dge[x, j], Dge[y, j]])
        if sel is not None: add(sel)
    if MODE == 'orbk':                                       # exact orbit positions o(k, .), k <= K
        add([-O[x] for x in range(n)])
        o = lambda k, x: E.v('ob', k, x)
        for x in range(n): add([o(0, x)] if x == bot else [-o(0, x)])
        for k in range(K):
            for x in rows:
                add([-o(k, x)] + [lam[x, p] for p in low])
                for y in range(n): add([-o(k, x), -mu[x, y], o(k + 1, y)])
            for x in range(n):
                if x not in rows: add([-o(k, x)])
            for y in range(n):
                for y2 in range(y + 1, n): add([-o(k + 1, y), -o(k + 1, y2)])
        for x in range(n):
            if x in rows: add([-o(K, x), -mu[x, x]])
            else: add([-o(K, x)])
        add([o(K, x) for x in rows])
    if MODE == 'tcase':
        add([-O[x] for x in range(n)])
        D = lambda x: E.v('tD', x); Ee = lambda x: E.v('tE', x)
        for x in range(n):
            if x not in rows or x == bot: add([-D(x)]); add([-Ee(x)]); continue
            add([-D(x), mu[bot, x]])                      # D = mu(bot) = d
        add([D(x) for x in rows if x != bot])
        def exits_badly(x):                               # x exits to q and q does not co-land
            ls = []
            for p in low:
                for q in rows:
                    t = E.v('xb', x, p, q); E.iff_and(t, [lam[x, p], -inZ(p), f(bot, p, q), -lam[q, p]]); ls.append(t)
            return ls
        if K in (10, 11, 12):
            sel = []
            for x in rows:
                if x == bot: continue
                for p in low:
                    if K == 11:
                        o = E.v('t11', x, p); sel.append(o)
                        for lit in [inZ(x), lam[x, p], -inZ(p), -f(x, p, p)]: add([-o, lit])
                        continue
                    for q in rows:
                        if not le[q][x] or q == bot or (K == 12 and q == x): continue
                        o = E.v('t10', x, p, q); sel.append(o)
                        for lit in [inZ(x), lam[x, p], -inZ(p), f(bot, p, q), -f(q, p, p)]: add([-o, lit])
            add(sel)
        elif K == 9:
            sel = []
            for x in rows:
                if x == bot: continue
                for p in low:
                    for q in rows:
                        if not le[q][x] or q == bot: continue
                        o9 = E.v('t9', x, p, q); sel.append(o9)
                        for lit in [inZ(x), lam[x, p], -inZ(p), f(bot, p, q), -lam[q, p]]: add([-o9, lit])
            add(sel)
        elif K == 17:
            sel = []
            for e in rows:
                if e == bot: continue
                o = E.v('s17', e); sel.append(o); add([-o, D(e)])
                if h[e] == 1:                                          # d an atom must be bad
                    add([-o, -E.v('on', e, e)])
                    for g in range(n):
                        if le[e][g]: add([-o, -E.v('A', e, g)])
                for m in rows:
                    if h[m] != 2: continue
                    for p in low:
                        if h[p] != 2: continue
                        q = L.meet[m][p]
                        if h[q] != 1: continue
                        for v in range(n):
                            if le[q][v]: add([-o, -inZ(m), -lam[m, p], -f(q, p, v)])
            add(sel)
        elif K == 25:                                     # DropProp fails: w in Z* in-steps to x in Z, x in-steps to y in Z,
            Dge = {}                                      # dep(x) < dep(w) and dep(y) >= dep(x)
            for x in range(n):
                for j in range(NO + 1):
                    Dge[x, j] = E.v('dge', x, j); E.iff_or(Dge[x, j], [E.v('it', bot, j, t) for t in range(n) if le[x][t]])
            sel = []
            for w in rows:
                if w == bot: continue
                for x in low:
                    if x == bot or x == w: continue
                    for y in low:
                        if y == bot or y == x: continue
                        o = E.v('s25', w, x, y); sel.append(o)
                        for lit in [inZ(w), lam[w, x], inZ(x), lam[x, y], inZ(y)] + ([-mu[y, y]] if 'yf' in FL else []): add([-o, lit])
                        add([-o] + [E.v('s25j', w, x, j) for j in range(NO + 1)])      # dep(w) > dep(x): some j, w <= t_j, x not
                        for j in range(NO + 1):
                            add([-E.v('s25j', w, x, j), Dge[w, j]]); add([-E.v('s25j', w, x, j), -Dge[x, j]])
                            add([-o, -Dge[x, j], Dge[y, j]])                            # dep(y) >= dep(x)
            add(sel)
        elif K == 24:                                     # ExitBelow fails: some row x lands at p with q = F(bot, p) != bot,
            sel = []                                      # and q is not below some high element t of the bot-descent
            for x in rows:
                for p in low:
                    for t in range(n):
                        if h[t] <= 2: continue
                        o = E.v('s24', x, p, t); sel.append(o)
                        for lit in [lam[x, p], E.v('on', bot, t)]: add([-o, lit])
                        add([-o] + [f(bot, p, q) for q in range(n) if q != bot and not le[q][t]])
            add(sel)
        elif K in (16, 19, 20, 21, 22, 23):
            sel = []
            for e in rows:
                if h[e] != 1: continue
                Ab = [E.v('A', e, g) for g in range(n) if le[e][g]]          # bad: not e <= a(e), and e not on its own descent
                for r_ in range(n):
                    if not le[e][r_]: continue
                    for tk in range(n):
                        for tk1 in range(n):
                            w = L.meet[r_][tk]
                            if w == e or (L.meet[r_][tk1] != e and 'mK' not in FL): continue
                            o = E.v('s16', e, r_, tk, tk1); sel.append(o)
                            add([-o, D(e)])
                            if 'mBad' not in FL:                            # mutant mBad: d need not be bad
                                add([-o, -E.v('on', e, e)])
                                for lit in Ab: add([-o, -lit])
                            add([-o, E.v('on', e, r_)])
                            if 'mR' not in FL:                              # mutant mR: r any descent element >= d
                                for v in range(n):
                                    if le[e][v]: add([-o, -f(e, r_, v)])   # r is the last descent element >= d
                            add([-o, E.v('on', bot, tk)])
                            if 'mK' not in FL: add([-o, f(bot, tk, tk1)])   # mutant mK: any k with r meet t_k above d
                            if 'Rw' in FL: Trow([-o], w)                    # role-level (T) at the breakpoint row w
                            if 'Rd' in FL: Trow([-o], e)                    # ... at row d
                            if 'Rb' in FL: Trow([-o], bot)                  # ... at row bot
                            if 'Rr' in FL: Trow([-o, -inZ(r_)], r_)         # ... at row r when r in Z
                            if 'Rl' in FL:                                  # (T) at row lambda(w) when lambda(w) in Z
                                for p in low: Trow([-o, -lam[w, p], -inZ(p)], p)
                            if 'Rm' in FL:                                  # (T) at row w meet lambda(w)
                                for p in low: Trow([-o, -lam[w, p]], L.meet[w][p])
                            if K == 19: continue                            # hypothesis of BreakCert only (vacuity / data)
                            if K in (20, 21, 22, 23) and w not in rows:             # w in Z by break_in_Z; Z heights <= 2 here
                                add([-o, inZ(w)]); continue
                            if K == 20:                                     # BreakDom fails: w exits at p, F(bot, p) not below w
                                add([-o] + [E.v('t20', w, p) for p in low])
                                if ('done20', w, r_, tk) in E.vars: continue
                                E.v('done20', w, r_, tk)
                                for p in low: E.iff_and(E.v('t20', w, p), [lam[w, p], -inZ(p), E.v('nd20', w, p)]); E.iff_or(E.v('nd20', w, p), [f(bot, p, v) for v in range(n) if not le[v][tk if 'cT' in FL else r_ if 'cR' in FL else w]])
                                continue
                            if K in (22, 23):                               # InStepUp fails: w lands at p in Z (predecessor u) and row p
                                ls = []                                     # has no upper cell at a high y >= p on row w descent (22) / at u (23)
                                if ('done22', w) in E.vars:
                                    add([-o, E.v('any22', w)]); continue
                                E.v('done22', w)
                                for p in low:
                                    for u in range(n):
                                        if h[u] <= 2 or not le[p][u]: continue
                                        t = E.v('t22', w, p, u); ls.append(t)
                                        for lit in [lam[w, p], inZ(p), E.v('on', w, u), f(w, u, p)]: add([-t, lit])
                                        for y in range(n):
                                            if h[y] <= 2 or not le[p][y]: continue
                                            if K == 23 and y != u: continue
                                            for v in range(n):
                                                if le[y][v]: add([-t, -E.v('on', w, y), -f(p, y, v)])
                                add([-E.v('any22', w)] + ls); add([-o, E.v('any22', w)])
                                continue
                            if K == 21:                                     # BreakExit fails: w lands at p in Z
                                add([-o] + [E.v('t21', w, p) for p in low])
                                if ('done21', w) in E.vars: continue
                                E.v('done21', w)
                                for p in low: E.iff_and(E.v('t21', w, p), [lam[w, p], inZ(p)])
                                continue
                            if w in rows:                                   # negated claim: w not a dominated exit
                                ls = []
                                for p in low:
                                    t = E.v('t16', w, p); ls.append(t)
                                    E.iff_and(t, [lam[w, p], E.v('ndom16', w, p)])
                                    E.iff_or(E.v('ndom16', w, p), [inZ(p)] + [f(bot, p, v) for v in range(n) if not le[v][w]])
                                add([-o] + ls + [-inZ(w)])
            add(sel)
        elif K in (14, 15, 18):
            Xv = {}
            for x in rows:
                if x == bot: continue
                for q in rows:
                    if q == bot: continue
                    ls = []
                    for p in low:
                        t = E.v('t14', x, p, q); E.iff_and(t, [inZ(x), lam[x, p], -inZ(p), f(bot, p, q)]); ls.append(t)
                    o = E.v('X14', x, q); E.iff_or(o, ls); Xv[x, q] = o
            sel = []
            if K in (15, 18):                                  # z = d (exits) or z = e = lambda(d) in Z (exits); or L2 fails
                for x in rows:
                    if x == bot: continue
                    for y in rows:
                        if y == bot or y not in low: continue
                        o = E.v('l2f', x, y); sel.append(o)
                        for lit in [D(x), lam[x, y], inZ(y)]: add([-o, lit])
                        add([-o] + [E.v('l2in', y, p2) for p2 in low])
                        for p2 in low: E.iff_and(E.v('l2in', y, p2), [lam[y, p2], inZ(p2)])
            for x in rows:
                for q in rows:
                    if (x, q) not in Xv: continue
                    o = E.v('s14', x, q); sel.append(o); add([-o, Xv[x, q]])
                    if K in (15, 18):                          # x is the first exiting point of the chain from d
                        zo = E.v('zfirst', x); add([-o, zo])
                        ls = [D(x)] + [E.v('zin', x2, x) for x2 in rows if x2 != bot]
                        add([-zo] + ls)
                        for x2 in rows:
                            if x2 == bot: continue
                            if x in low: E.iff_and(E.v('zin', x2, x), [D(x2), lam[x2, x], inZ(x)])
                            else: add([-E.v('zin', x2, x)])
                    if K == 18:                                # no join row r v q (r an atom <= z) in Z exits to q
                        for r_ in range(n):
                            if h[r_] != 1 or not le[r_][x]: continue
                            j = jn[r_][q]
                            if (j, q) in Xv: add([-o, -Xv[j, q]])
                        continue
                    for x2 in rows:
                        if (x2, q) in Xv and le[q][x2]: add([-o, -Xv[x2, q]])
            add(sel)
        elif K in (8, 13):
            sel = []
            for x in rows:
                for y in rows:
                    if x == bot or y == bot or y not in low: continue
                    for p in low:
                        o8 = E.v('t8', x, y, p); sel.append(o8)
                        for lit in [D(x) if K == 8 else inZ(x), lam[x, y], inZ(y), lam[y, p], -inZ(p)]: add([-o8, lit])
                        if 'Rd' in FL: Trow([-o8], x)
                        if 'Re' in FL: Trow([-o8], y)
                        if 'Rb' in FL: Trow([-o8], bot)
                        if 'Rj' in FL: Trow([-o8, -inZ(jn[x][y])], jn[x][y])
                        if 'Rq' in FL:
                            for q in range(n): Trow([-o8, -f(bot, p, q)], q)
                        for q in range(n):
                            if le[q][y]: add([-o8, -f(bot, p, q)])
            add(sel)
        elif K == 7:
            sel = []
            for x in rows:
                for y in rows:
                    if x == bot or y == bot or y not in low: continue
                    for u in range(n):
                        if h[u] <= 2: continue
                        for p in low:
                            o7 = E.v('t7', x, y, u, p); sel.append(o7)
                            for lit in [D(x), lam[x, y], inZ(y), E.v('on', y, u), f(y, u, p), lam[y, p], -inZ(p)]: add([-o7, lit])
                            for q in range(n):                    # q = F(bot, p) must not have u on its row's descent
                                add([-o7, -f(bot, p, q), -E.v('on', q, u)] if q in rows else [-o7, -f(bot, p, q)])
            add(sel)
        elif K in (5, 6):
            for x in rows:
                if x == bot: continue
                ls = []
                for p in low:
                    for q in rows:
                        t = E.v('x5', x, p, q); E.iff_and(t, [lam[x, p], -inZ(p), f(bot, p, q)] + ([-mu[q, q]] if K == 5 else [])); ls.append(t)
                add([-D(x)] + ls)
        elif K == 1:
            for x in rows:
                if x != bot: add([-D(x)] + exits_badly(x))
        else:
            sel = []
            for x in rows:
                for y in rows:
                    if x == bot or y == bot or y not in low: continue
                    o2 = E.v('tsel', x, y); sel.append(o2); add([-o2, D(x)]); add([-o2, lam[x, y]]); add([-o2, inZ(y)])
                    if 'Rd' in FL: Trow([-o2], x)
                    if 'Re' in FL: Trow([-o2], y)
                    if 'Rb' in FL: Trow([-o2], bot)
                    if 'Rj' in FL: Trow([-o2, -inZ(jn[x][y])], jn[x][y])
                    if 'Rq' in FL:
                        for p2 in low: Trow([-o2, -lam[y, p2]], p2)
                    if K == 2: add([-o2] + exits_badly(y))
                    elif K == 4: pass
                    else: add([-o2] + [E.v('tin', y, p2) for p2 in low])
                    for p2 in low:
                        if K == 3: E.iff_and(E.v('tin', y, p2), [lam[y, p2], inZ(p2)])
            add(sel)
    if MODE == 'botorbit': add([O[bot]])
    elif MODE == 'muloop': add([-O[bot]]); add([O[x] for x in rows if x != bot])
    else: add([-O[x] for x in range(n)])
    if E.S.solve():
        F = E.decode(); st = stages(L, F); inR = lambda x, i: st[x] is not None and st[x] <= i
        ok = a_of(L, F, bot) == bot and ('mTop' in FL or not inR(top, 2)) and ('mN1' in FL or any(h[z] > 1 for z in range(n) if inR(z, 1)))
        if 'not2' not in FL: ok = ok and all(h[z] <= 2 for z in range(n) if inR(z, 2))
        Zs = [x for x in range(n) if F[bot][x] == bot]
        if 'Tb' in FL: ok = ok and not any(h[y] > 2 and le[F[x][y]][x] for x in Zs for y in range(n))
        if 'Ta' in FL: ok = ok and not any(h[y] > 2 and le[y][F[x][y]] for x in Zs for y in range(n))
        if 'ZT' in FL: ok = ok and all(h[x] <= 2 for x in Zs)
        def desc(x):
            v = top; seen = []
            while v not in seen: seen.append(v); v = F[x][v]
            return seen
        def lamf(x):
            v = top; seen = []
            while v not in seen:
                if h[v] <= 2: return v
                seen.append(v); v = F[x][v]
            return None
        def muf(x):
            p = lamf(x)
            if p is None: return None
            return p if F[bot][p] == bot else F[bot][p]
        Z = [x for x in range(n) if F[bot][x] == bot]
        if MODE == 'botorbit':
            x = bot; seen = []
            while x is not None and x not in seen: seen.append(x); x = muf(x)
            ok = ok and x is not None and all(muf(y) != y for y in seen)          # orbit cycles without a fixed point
        elif MODE == 'muloop':
            cyc = False
            for s in Z:
                if s == bot: continue
                x = s; seen = []
                while x is not None and x not in seen: seen.append(x); x = muf(x)
                if x is not None and x != bot:
                    k = seen.index(x); cyc = cyc or len(seen) - k >= 2
            ok = ok and cyc
        if MODE == 'tcase':
            dd = muf(bot); lamd = lamf(dd)
            if K == 1: ok = ok and F[bot][lamd] != bot and lamf(F[bot][lamd]) != lamd
            elif K in (5, 6): ok = ok and F[bot][lamd] != bot and (K == 6 or muf(F[bot][lamd]) != F[bot][lamd])
            if K == 10:
                ok = ok and any(F[bot][x] == bot and x != bot and F[bot][lamf(x)] != bot and le[F[bot][lamf(x)]][x]
                                and F[F[bot][lamf(x)]][lamf(x)] != lamf(x) for x in range(n) if lamf(x) is not None)
            if K == 12:
                ok = ok and any(F[bot][x] == bot and x != bot and F[bot][lamf(x)] != bot and le[F[bot][lamf(x)]][x] and F[bot][lamf(x)] != x
                                and F[F[bot][lamf(x)]][lamf(x)] != lamf(x) for x in range(n) if lamf(x) is not None)
            if K == 11:
                ok = ok and any(F[bot][x] == bot and x != bot and F[bot][lamf(x)] != bot and F[x][lamf(x)] != lamf(x)
                                for x in range(n) if lamf(x) is not None)
            if K == 9:
                ok = ok and any(F[bot][x] == bot and x != bot and F[bot][lamf(x)] != bot and le[F[bot][lamf(x)]][x]
                                and lamf(F[bot][lamf(x)]) != lamf(x) for x in range(n) if lamf(x) is not None)
            if K == 17:
                dd_ = muf(bot); good_ = lambda y: le[y][a_of(L, F, y)] or y in desc(y)
                ok = ok and not (h[dd_] == 1 and good_(dd_))
                ok = ok and not any(h[m] == 2 and F[bot][m] == bot and lamf(m) is not None and h[lamf(m)] == 2
                                    and h[L.meet[m][lamf(m)]] == 1 and le[L.meet[m][lamf(m)]][F[L.meet[m][lamf(m)]][lamf(m)]]
                                    for m in range(n))
            if K == 25:
                tb_ = desc(bot); dep = lambda z: max(j for j, t in enumerate(tb_) if le[z][t]); Zs = [z for z in range(n) if z != bot and F[bot][z] == bot]
                ok = ok and any(lamf(w) in Zs and lamf(w) != w and lamf(lamf(w)) in Zs and dep(lamf(w)) < dep(w) and dep(lamf(lamf(w))) >= dep(lamf(w)) and ('yf' not in FL or muf(lamf(lamf(w))) != lamf(lamf(w)))
                                for w in Zs if lamf(w) is not None and lamf(lamf(w)) is not None)
            if K == 24:
                tb_ = desc(bot)
                ok = ok and any(lamf(x) is not None and F[bot][lamf(x)] != bot and h[t] > 2 and not le[F[bot][lamf(x)]][t]
                                for x in range(n) for t in tb_)
            if K in (16, 19, 20, 21, 22, 23):
                dd_ = muf(bot); tb_ = desc(bot)
                good_ = lambda y: le[y][a_of(L, F, y)] or y in desc(y)
                ok = ok and h[dd_] == 1 and (not good_(dd_) or 'mBad' in FL)
                de_ = desc(dd_); r_ = [y for y in de_ if le[dd_][y]][-1]
                k_ = max(k for k in range(len(tb_) - 1) if L.meet[r_][tb_[k]] != dd_ and L.meet[r_][tb_[k + 1]] == dd_)
                w = L.meet[r_][tb_[k_]]
                bad_w = F[bot][w] != bot or h[w] != 2 or lamf(w) is None or F[bot][lamf(w)] == bot or not le[F[bot][lamf(w)]][w]
                if K == 16: ok = ok and bad_w
                if K == 20 and FL & {'mR', 'mK'}:             # mutants: some admissible (r, k) gives a failing w
                    def fails20(w2): return F[bot][w2] == bot or True
                    cand = []
                    for r2 in (de_ if 'mR' in FL else [r_]):
                        if not le[dd_][r2]: continue
                        for k2 in range(len(tb_)):
                            w2 = L.meet[r2][tb_[k2]]
                            if w2 == dd_: continue
                            if 'mK' not in FL and not (k2 + 1 < len(tb_) and L.meet[r2][tb_[k2 + 1]] == dd_): continue
                            p2 = lamf(w2)
                            if p2 is not None and h[w2] <= 2 and F[bot][p2] != bot and not le[F[bot][p2]][w2]: cand.append(w2)
                    ok = ok and bool(cand)
                elif K == 20: ok = ok and lamf(w) is not None and F[bot][lamf(w)] != bot and not le[F[bot][lamf(w)]][w]
                if K == 21: ok = ok and lamf(w) is not None and F[bot][lamf(w)] == bot
                if K in (22, 23):
                    dw_ = desc(w); p_ = lamf(w); u_ = dw_[dw_.index(p_) - 1]
                    ok = ok and F[bot][p_] == bot and le[p_][u_] and not any(h[y] > 2 and le[p_][y] and le[y][F[p_][y]] and (K == 22 or y == u_) for y in dw_)
                if DUMP is not None:
                    DUMP.append(dict(sets=L.S, F=F, d=dd_, r=r_, k=k_, w=w, tb=tb_))
            if K == 18:
                dd_ = muf(bot); Zs = [x for x in range(n) if x != bot and F[bot][x] == bot and lamf(x) is not None]
                ex = {x: F[bot][lamf(x)] for x in Zs if F[bot][lamf(x)] != bot}
                if dd_ in ex: z = dd_
                elif lamf(dd_) is not None and F[bot][lamf(dd_)] == bot and lamf(dd_) in ex: z = lamf(dd_)
                else: z = None
                ok = ok and (z is None or not any(h[r_] == 1 and le[r_][z] and ex.get(jn[r_][ex[z]]) == ex[z] for r_ in range(n)))
            if K == 15:
                dd_ = muf(bot); Zs = [x for x in range(n) if x != bot and F[bot][x] == bot and lamf(x) is not None]
                ex = {x: F[bot][lamf(x)] for x in Zs if F[bot][lamf(x)] != bot}
                if dd_ in ex: z = dd_
                elif lamf(dd_) is not None and F[bot][lamf(dd_)] == bot and lamf(dd_) in ex: z = lamf(dd_)
                else: z = None
                ok = ok and (z is None or not any(ex.get(x2) == ex[z] and le[ex[z]][x2] for x2 in ex))
            if K == 14:
                Zs = [x for x in range(n) if x != bot and F[bot][x] == bot and lamf(x) is not None]
                ex = {x: F[bot][lamf(x)] for x in Zs if F[bot][lamf(x)] != bot}
                ok = ok and any(not any(ex.get(x2) == q and le[q][x2] for x2 in ex) for x, q in ex.items())
            if K == 13:
                ok = ok and any(x != bot and F[bot][x] == bot and lamf(x) is not None and lamf(x) != bot and F[bot][lamf(x)] == bot
                                and lamf(lamf(x)) is not None and F[bot][lamf(lamf(x))] != bot and not le[F[bot][lamf(lamf(x))]][lamf(x)]
                                for x in range(n))
            if K == 8:
                e = lamd; ok = ok and F[bot][e] == bot and F[bot][lamf(e)] != bot and not le[F[bot][lamf(e)]][e]
            if K == 7:
                e = lamd; de = desc(e); p_ = lamf(e); u_ = de[de.index(p_) - 1]; q_ = F[bot][p_]
                ok = ok and F[bot][e] == bot and F[bot][p_] != bot and h[u_] > 2 and u_ not in desc(q_)
            if K in (2, 3, 4):
                e = lamd; ok = ok and F[bot][e] == bot and e != bot
                if K == 2: ok = ok and F[bot][lamf(e)] != bot and lamf(F[bot][lamf(e)]) != lamf(e)
                elif K == 3: ok = ok and F[bot][lamf(e)] == bot
        if MODE == 'orbdep':
            tb_ = desc(bot); dep = lambda z: max(j for j, t in enumerate(tb_) if le[z][t])
            xs = [bot]
            for _ in range(K): xs.append(muf(xs[-1]))
            bad = False
            if 'ex1' in FL:
                for k in range(1, K):
                    x = xs[k]
                    if x is None or x == bot: continue
                    p_ = lamf(x)
                    if p_ is not None and F[bot][p_] != bot and muf(F[bot][p_]) != F[bot][p_]: bad = True
            for k in (range(1, K) if 'ex1' not in FL else []):
                x, y = xs[k], xs[k + 1]
                if x is None or y is None or y == x or muf(y) == y: continue
                if 'ed' in FL: bad = bad or (y == lamf(x) and F[bot][y] == bot and dep(y) <= dep(x) - 2); continue
                bad = bad or (dep(y) > dep(x) if 'ns' in FL else dep(y) >= dep(x))
            ok = ok and bad
        if MODE == 'orbk':
            x = bot
            for _ in range(K): x = None if x is None else muf(x)
            ok = ok and x is not None and muf(x) != x
        assert ok, 'SAT/Python mismatch'
        C['SAT'] += 1; HH[f'h{L.height}'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else: C['UNSAT'] += 1; HH[f'h{L.height}:unsat'] += 1
    E.S.delete()
if DUMP is not None:
    import json; json.dump(DUMP, open(os.environ['DUMP'], 'w'))
print(MODE, sorted(FL), args, dict(C), dict(HH), 'smallest', best[0] if best else None)
if best and MODE != 'vac':
    import json; json.dump(best[1], open(f'muorbit_{MODE}{"".join("_" + x for x in sorted(FL))}_min{best[0]}.json', 'w'))
