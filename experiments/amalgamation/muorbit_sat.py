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
  with not2, partial facts: Tb (no Z-row lower cell at a high column), Ta (no Z-row upper cell at a high column), ZT (Z heights <= 2)
Every SAT model is replayed in Python (stages, a_of, direct computation of lambda, mu and the orbit).
  python3 muorbit_sat.py MODE [K] (sweep N MAX | closure K M SEED CNT) [not2]"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import lattices
from rstages import stages, a_of
MODE = sys.argv[1]; K = 0
if MODE in ('orbk', 'tcase'): K = int(sys.argv[2]); sys.argv.pop(2)
FL = {a for a in sys.argv[2:] if a in ('not2', 'Ta', 'Tb', 'ZT')}; args = [a for a in sys.argv[2:] if a not in FL]
MEAN = {'botorbit': 'BotOrbit fails: the mu-orbit of bot never reaches a fixed point',
        'muloop': 'MuLoop fails: a nonempty mu-closed set in Z* without fixed point', 'vac': 'the world has a model', 'orbk': f'Orbit{K} fails: mu^{K}(bot) is not a fixed point of mu', 'tcase': {1: 'L1(d) fails: d exits to q = F(bot, lambda(d)) with lambda(q) != lambda(d)', 2: 'L1(e) fails: d in-steps to e, e exits to q with lambda(q) != lambda(e)', 3: 'L2 fails: d in-steps to e and e in-steps', 4: 'hypothesis of L1(e)/L2: d in-steps to e (vacuity run)', 5: 'Fix1 fails: d exits to q = F(bot, lambda(d)) and mu(q) != q', 6: 'hypothesis of Fix1: d exits (vacuity run)', 10: 'StallQ fails: some x in Z* exits at p with q = F(bot, p) <= x and F(q, p) != p', 12: 'StallQ2 fails: some x in Z* exits at p with q = F(bot, p) <= x, q != x and F(q, p) != p', 11: 'StallX fails: some x in Z* exits at p and F(x, p) != p', 9: 'DomCoLand fails: some x in Z* exits at p with q = F(bot, p) <= x and lambda(q) != p', 8: 'QE fails: d in-steps to e, e exits at p, and q = F(bot, p) is not below e', 7: 'Follow fails: d in-steps to e, e exits at p with high predecessor u, q = F(bot, p), and u is not on row q descent'}.get(K, '?')}
print(f'muorbit_sat {MODE} | SAT = {MEAN[MODE]} | world W0 + n1 | flags {sorted(FL)} | corpus {args}')
C = collections.Counter(); HH = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; top = L.top; bot = L.bot; NO = L.height + 1
    if L.height < 3: continue
    E = Enc(L, 2); f = lambda a, b, u: E.v('f', a, b, u); r = lambda i, z: E.v('r', i, z); add = E.S.add_clause
    add([E.v('A', bot, bot)]); add([-r(2, top)])
    if 'not2' not in FL:
        for z in range(n):
            if h[z] > 2: add([-r(2, z)])
    add([r(1, z) for z in range(n) if h[z] > 1])
    for x in range(n):                                   # partial tightness facts (used with not2)
        for y in range(n):
            if h[y] <= 2: continue
            for w in range(n):
                if 'Tb' in FL and le[w][x]: add([-f(bot, x, bot), -f(x, y, w)])      # no lower cell of a Z-row at a high column
                if 'Ta' in FL and le[y][w]: add([-f(bot, x, bot), -f(x, y, w)])      # no upper cell of a Z-row at a high column
        if 'ZT' in FL and h[x] > 2: add([-f(bot, x, bot)])                           # Z has heights <= 2
    rows = [x for x in range(n) if h[x] <= 2 or 'not2' in FL]
    inZ = lambda x: f(bot, x, bot)
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
        elif K == 8:
            sel = []
            for x in rows:
                for y in rows:
                    if x == bot or y == bot or y not in low: continue
                    for p in low:
                        o8 = E.v('t8', x, y, p); sel.append(o8)
                        for lit in [D(x), lam[x, y], inZ(y), lam[y, p], -inZ(p)]: add([-o8, lit])
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
        ok = a_of(L, F, bot) == bot and not inR(top, 2) and any(h[z] > 1 for z in range(n) if inR(z, 1))
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
            if K == 8:
                e = lamd; ok = ok and F[bot][e] == bot and F[bot][lamf(e)] != bot and not le[F[bot][lamf(e)]][e]
            if K == 7:
                e = lamd; de = desc(e); p_ = lamf(e); u_ = de[de.index(p_) - 1]; q_ = F[bot][p_]
                ok = ok and F[bot][e] == bot and F[bot][p_] != bot and h[u_] > 2 and u_ not in desc(q_)
            if K in (2, 3, 4):
                e = lamd; ok = ok and F[bot][e] == bot and e != bot
                if K == 2: ok = ok and F[bot][lamf(e)] != bot and lamf(F[bot][lamf(e)]) != lamf(e)
                elif K == 3: ok = ok and F[bot][lamf(e)] == bot
        if MODE == 'orbk':
            x = bot
            for _ in range(K): x = None if x is None else muf(x)
            ok = ok and x is not None and muf(x) != x
        assert ok, 'SAT/Python mismatch'
        C['SAT'] += 1; HH[f'h{L.height}'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else: C['UNSAT'] += 1; HH[f'h{L.height}:unsat'] += 1
    E.S.delete()
print(MODE, sorted(FL), args, dict(C), dict(HH), 'smallest', best[0] if best else None)
if best and MODE != 'vac':
    import json; json.dump(best[1], open(f'muorbit_{MODE}{"".join("_" + x for x in sorted(FL))}_min{best[0]}.json', 'w'))
