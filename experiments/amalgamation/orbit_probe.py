"""§34.3z²⁷⁹ (worker): StrictDep and OneExit on the mu-orbit of bot, a second encoding independent of muorbit_sat.py.
World through (T), no R-stages in the encoding: rows F(x, .) only for low x (height <= 2), one-hot, monotone in y (covers)
and in x (covers inside the low set); a(bot) = bot (no y != bot with y <= F(bot, y)); Z = {y : F(bot, y) = bot} has no
element of height >= 3 (ZT); (T) at every row x of Z: no column y of height >= 3 has F(x, y) <= x or y <= F(x, y);
n1: some height-2 element lies in Z; h(top) >= 3.  Rows of high x are the constant top in the replay.
Every SAT model is completed and replayed with rstages.stages (W0 + n1 checked from the definitions) and the claim is
re-evaluated in Python.
Exact descents it(x, j, .) (one-hot per index); landing lambda(x) = first element of height <= 2; mu(x) = lambda(x) if
lambda(x) in Z, else F(bot, lambda(x)); orbit x_k = mu^k(bot); dep(x) = max j with x <= t_j, t = the bot-descent.
Modes:
  strictdep  SAT = some x_k (1 <= k < K) has a successor y = x_(k+1) != x_k that is not a fixed point and dep(y) >= dep(x_k)
  oneexit    SAT = some x_k (1 <= k < K) exits to an atom y that is not a fixed point of mu
  orbk       SAT = mu^K(bot) is not a fixed point (OrbitK fails)
  vac        SAT = the world has a model
Flag mT (mutant world): (T) kept only at the row bot (Tb/Ta dropped at the other rows of Z).
  python3 orbit_probe.py MODE K (sweep N MAX | closure K M SEED CNT | tall K M SEED CNT) [mT]"""
import sys, itertools, collections, json
sys.path.insert(0, '../separation'); sys.path.insert(0, '.')
from pysat.solvers import Cadical153
from tight_probe import lattices
from rstages import stages, a_of
MODE = sys.argv[1]; K = int(sys.argv[2]); MT = 'mT' in sys.argv[3:]
REL = {a for a in sys.argv[3:] if a in ('Tat', 'Tm2', 'TaOnly', 'TbOnly', 'Ta1', 'Tb1', 'Ta2', 'Tb2', 'land', 'xfix')}   # relaxations of (T) at rows of Z other than bot
BR = 'a' if 'Ba' in sys.argv[3:] else ('b' if 'Bb' in sys.argv[3:] else '')   # branch: a = h(d) = 2, b = d an atom (bad)
NEX = next((int(a[1:]) for a in sys.argv[3:] if a in ('E1', 'E2', 'E3', 'E4', 'E5', 'E6')), 0)   # exact N: t_N != bot = t_(N+1)
args = [a for a in sys.argv[3:] if a not in ('mT', 'Ba', 'Bb', 'Tat', 'Tm2', 'TaOnly', 'TbOnly', 'Ta1', 'Tb1', 'Ta2', 'Tb2', 'land', 'xfix') and not (a[0] == 'E' and a[1:].isdigit())]
SAT_MEANS = {'strictdep': 'some non-fixed successor on the bot-orbit has dep >= dep of its predecessor',
             'oneexit': 'some element of the bot-orbit exits to an atom that is not a fixed point', 'vac': 'the world has a model',
             'orbk': f'mu^{K}(bot) is not a fixed point of mu (Orbit{K} fails)',
             'topcert': 'd is not a good atom and no m in Z of height 2 exits to an atom below m (TopCert fails)',
             'nmgood': 'd is not a good atom and no atom below an m in Z of height 2 is good (NMGood fails)',
             'exitm2': 'd is not a good atom and no m in Z of height 2 exits (ExitM2 fails)',
             'Mtopcert': 'MUTANT: d is not a good atom and some m in Z of height 2 does not exit to an atom below m',
             'Mnmgood': 'MUTANT: d is not a good atom and some m in Z of height 2 has no good atom below it',
             'Mexitm2': 'MUTANT: d is not a good atom and some m in Z of height 2 does not exit',
             'twofix': 'two distinct atoms of Z are fixed points of mu (AtMost1Fix fails; all branches)',
             'twogood': 'CALIBRATED MUTANT (OneGood, refuted): two distinct atoms of Z are good (all branches)',
             'fixmax': 'd is not a good atom and some mu-fixed atom of Z lies below no height-2 element of Z (FixMax fails)',
             'goodnonmax': 'CALIBRATED MUTANT (GoodNonMax): d is not a good atom and some good atom of Z lies below no height-2 element of Z'}[MODE]
print(f'orbit_probe {MODE} K={K}' + (f' RELAXED {sorted(REL)} (off g read as: d has no own-row cell)' if REL else '') + (f' N={NEX}' if NEX else '') + f' | SAT = {SAT_MEANS} | world (T) {"MUTANT mT" if MT else ""} | corpus {args}')
import os
DUMPF = os.environ.get('DUMP'); DUMPL = []
C = collections.Counter(); HH = collections.Counter(); best = None
MAXN = None
if 'maxn' in args: k_ = args.index('maxn'); MAXN = int(args[k_ + 1]); args = args[:k_] + args[k_ + 2:]   # ... maxn N: skip |L| > N
for L in lattices(args):
    if MAXN is not None and L.n > MAXN: continue
    n = L.n; le = L.le; h = L.rank; bot = L.bot; top = L.top
    if h[top] < 3: continue
    low = [x for x in range(n) if h[x] <= 2]; NO = h[top] + 1
    S = Cadical153(); V = {}
    def v(*k):
        if k not in V: V[k] = len(V) + 1
        return V[k]
    add = S.add_clause; f = lambda x, y, u: v('f', x, y, u); Z = lambda y: f(bot, y, bot)
    for x in low:
        for y in range(n):
            ls = [f(x, y, u) for u in range(n)]; add(ls)
            for a_, b_ in itertools.combinations(ls, 2): add([-a_, -b_])
        for y in range(n):
            for y2 in L.covers_up[y]:
                for u in range(n): add([-f(x, y, u)] + [f(x, y2, u2) for u2 in range(n) if le[u][u2]])
        for x2 in L.covers_up[x]:
            if h[x2] > 2: continue
            for y in range(n):
                for u in range(n): add([-f(x, y, u)] + [f(x2, y, u2) for u2 in range(n) if le[u][u2]])
    for y in range(n):                                        # a(bot) = bot
        if y == bot: continue
        for u in range(n):
            if le[y][u]: add([-f(bot, y, u)])
    for y in range(n):
        if h[y] > 2: add([-Z(y)])                             # ZT
    add([Z(y) for y in range(n) if h[y] == 2])                # n1
    for x in low:                                             # (T) at rows of Z
        if MT and x != bot: continue
        if x != bot and 'Tat' in REL and h[x] != 1: continue   # (T) only at atom rows (and bot)
        if x != bot and 'Tm2' in REL and h[x] != 2: continue   # (T) only at height-2 rows (and bot)
        for y in range(n):
            if h[y] <= 2: continue
            for u in range(n):
                if x != bot and 'TaOnly' in REL and not le[y][u]: continue      # keep only the upper-cell half
                if x != bot and 'TbOnly' in REL and not le[u][x]: continue      # keep only the lower-cell half
                if h[x] == 1 and 'Ta1' in REL and not le[y][u]: continue        # atoms: upper half only
                if h[x] == 1 and 'Tb1' in REL and not le[u][x]: continue        # atoms: lower half only
                if h[x] == 2 and 'Ta2' in REL and not le[y][u]: continue        # height-2 rows: upper half only
                if h[x] == 2 and 'Tb2' in REL and not le[u][x]: continue        # height-2 rows: lower half only
                if le[u][x] or le[y][u]: add([-Z(x), -f(x, y, u)])
    it = lambda x, j, z: v('it', x, j, z)
    for x in low:
        for z in range(n): add([it(x, 0, z)] if z == top else [-it(x, 0, z)])
        for j in range(NO):
            for z in range(n):
                for u in range(n): add([-it(x, j, z), -f(x, z, u), it(x, j + 1, u)])
            for z, z2 in itertools.combinations(range(n), 2): add([-it(x, j + 1, z), -it(x, j + 1, z2)])
    lam = {}
    for x in low:
        for p in low:
            o = v('lam', x, p); ls = []
            for j in range(NO + 1):
                t = v('lamj', x, p, j); ls.append(t); add([-t, it(x, j, p)])
                for j2 in range(j):
                    for z in low: add([-t, -it(x, j2, z)])
                add([-it(x, j, p), t] + [it(x, j2, z) for j2 in range(j) for z in low])
            add([-o] + ls)
            for t in ls: add([-t, o])
            lam[x, p] = o
    if 'land' in REL:                                         # every row of Z lands (as tightness gives)
        for x in low: add([-Z(x)] + [lam[x, p_] for p_ in low])
    mu = {}
    for x in low:
        for y in low:
            ls = []
            t = v('mi', x, y); ls.append(t); add([-t, lam[x, y]]); add([-t, Z(y)]); add([t, -lam[x, y], -Z(y)])
            for p in low:
                t = v('me', x, p, y); ls.append(t)
                for lit in (lam[x, p], -Z(p), f(bot, p, y)): add([-t, lit])
                add([t, -lam[x, p], Z(p), -f(bot, p, y)])
            o = v('mu', x, y); mu[x, y] = o
            for t in ls: add([-t, o])
            add([-o] + ls)
    ob = lambda k, x: v('ob', k, x)
    for x in range(n): add([ob(0, x)] if x == bot else [-ob(0, x)])
    for k in range(K):
        for x in low:
            for y in low: add([-ob(k, x), -mu[x, y], ob(k + 1, y)])
            add([-ob(k, x)] + [mu[x, y] for y in low])
        for x in range(n):
            if x not in low: add([-ob(k + 1, x)])
        for y, y2 in itertools.combinations(range(n), 2): add([-ob(k + 1, y), -ob(k + 1, y2)])
    dge = {}
    for x in range(n):
        for j in range(NO + 1):
            o = v('dge', x, j); dge[x, j] = o; ls = [it(bot, j, t) for t in range(n) if le[x][t]]
            for l in ls: add([-l, o])
            add([-o] + ls)
    if NEX:
        if NEX + 1 > NO: S.delete(); continue
        add([-it(bot, NEX, bot)]); add([it(bot, NEX + 1, bot)])
    sel = []
    if MODE == 'strictdep':
        for k in range(1, K):
            for x in low:
                if x == bot: continue
                for y in low:
                    if y == x: continue
                    t = v('sd', k, x, y); sel.append(t)
                    for lit in (ob(k, x), ob(k + 1, y), -mu[y, y]): add([-t, lit])
                    for j in range(NO + 1): add([-t, -dge[x, j], dge[y, j]])
    elif MODE == 'oneexit':
        for k in range(1, K):
            for x in low:
                if x == bot: continue
                for p in low:
                    for y in low:
                        t = v('ox', k, x, p, y); sel.append(t)
                        for lit in (ob(k, x), lam[x, p], -Z(p), f(bot, p, y), -mu[y, y]): add([-t, lit])
    elif MODE.lstrip('M') in ('topcert', 'nmgood', 'exitm2', 'twofix', 'twogood', 'fixmax', 'goodnonmax'):
        # d = last nonzero element of the bot-descent; off branch g: d is not a good atom (own-cell form of IsGood)
        dv = lambda z: v('dv', z)
        for z in range(n):
            if z == bot: add([-dv(z)]); continue
            add([-dv(z)] + [v('dvj', z, j) for j in range(NO)])
            for j in range(NO): add([-v('dvj', z, j), it(bot, j, z)]); add([-v('dvj', z, j), it(bot, j + 1, bot)])
        add([dv(z) for z in range(n) if z != bot])
        own = {}
        for q in low:                                         # own(q) <= some height-2 p on row q's descent with q <= F(q, p)
            if h[q] != 1: continue
            o = v('own', q); own[q] = o; wit = []
            for j in range(NO + 1):
                for p_ in low:
                    if h[p_] != 2: continue
                    for u in range(n):
                        if le[q][u]:
                            add([o, -it(q, j, p_), -f(q, p_, u)])           # a cell forces own(q)
                            t = v('ownw', q, j, p_, u); wit.append(t); add([-t, it(q, j, p_)]); add([-t, f(q, p_, u)])
            add([-o] + wit)                                                    # own(q) forces some cell
        allbr = MODE in ('twofix', 'twogood')
        if not allbr:
            for z in own: add([-dv(z), -own[z]])              # off g (a d of height 2 is never a good atom)
        if BR == 'a': add([-dv(z) for z in range(n) if h[z] == 1])
        if BR == 'b': add([-dv(z) for z in range(n) if h[z] == 2])
        M2 = [m_ for m_ in low if h[m_] == 2]
        ex = {}; exd = {}
        for m_ in M2:                                         # exits(m) / exits dominated(m), forced true by their witnesses
            ex[m_] = v('ex', m_); exd[m_] = v('exd', m_)
            for p_ in low:
                add([ex[m_], -lam[m_, p_], Z(p_)])
                for q in range(n):
                    if q != bot and le[q][m_]: add([exd[m_], -lam[m_, p_], Z(p_), -f(bot, p_, q)])
        base = MODE.lstrip('M')
        if base in ('twofix', 'twogood', 'fixmax', 'goodnonmax'):
            AT = [q for q in own]
            if 'xfix' in REL:                                  # exit-fixed: lambda(q) = p not in Z and F(bot, p) = q
                for q in own:
                    xs_ = []
                    for p_ in low:
                        t_ = v('xf', q, p_); xs_.append(t_)
                        for lit in (lam[q, p_], -Z(p_), f(bot, p_, q)): add([-t_, lit])
                    add([-v('xfx', q)] + xs_)
            prop = ((lambda q: v('xfx', q)) if 'xfix' in REL else (lambda q: mu[q, q])) if base in ('twofix', 'fixmax') else (lambda q: own[q])
            if base in ('twofix', 'twogood'):
                for q, q2 in itertools.combinations(AT, 2):
                    t = v('pair', q, q2); sel.append(t)
                    for lit in (Z(q), Z(q2), prop(q), prop(q2)): add([-t, lit])
            else:
                for q in AT:
                    t = v('mx', q); sel.append(t)
                    for lit in (Z(q), prop(q)): add([-t, lit])
                    for m_ in M2:
                        if le[q][m_]: add([-t, -Z(m_)])
            add(sel); sel = []
        elif MODE[0] != 'M':                                    # the statement fails: every top-layer row avoids it
            for m_ in M2:
                if base == 'topcert': add([-Z(m_), -exd[m_]])
                if base == 'exitm2': add([-Z(m_), -ex[m_]])
                if base == 'nmgood':
                    for q in own:
                        if le[q][m_]: add([-Z(m_), -own[q]])
        else:                                                 # mutant: some top-layer row avoids it
            for m_ in M2:
                t = v('mut', m_); sel.append(t); add([-t, Z(m_)])
                if base == 'topcert': add([-t, -exd[m_]])
                if base == 'exitm2': add([-t, -ex[m_]])
                if base == 'nmgood':
                    for q in own:
                        if le[q][m_]: add([-t, -own[q]])
            add(sel); sel = []
    elif MODE == 'orbk':
        for x in low:
            t = v('ok', x); sel.append(t); add([-t, ob(K, x)]); add([-t, -mu[x, x]])
    if MODE != 'vac' and sel: add(sel)
    if S.solve():
        m = set(l for l in S.get_model() if l > 0)
        F = [[(next(u for u in range(n) if V[('f', x, y, u)] in m) if x in low else top) for y in range(n)] for x in range(n)]
        st = stages(L, F); inR = lambda z, i: st[z] is not None and st[z] <= i
        ok = (a_of(L, F, bot) == bot and all(h[z] <= 2 for z in range(n) if inR(z, 2)) and not inR(top, 2)
              and any(h[z] > 1 for z in range(n) if inR(z, 1)))
        if MT or REL: ok = a_of(L, F, bot) == bot              # relaxed world: only the bot facts are guaranteed
        def desc(x):
            z = top; s = []
            while z not in s: s.append(z); z = F[x][z]
            return s
        def lamf(x): return next((z for z in desc(x) if h[z] <= 2), None)
        def muf(x):
            p = lamf(x)
            return None if p is None else (p if F[bot][p] == bot else F[bot][p])
        tb = desc(bot); ok = ok and (not NEX or (len(tb) == NEX + 2 and tb[-1] == bot))
        dep = lambda z: max(j for j, t in enumerate(tb) if le[z][t])
        xs = [bot]
        for _ in range(K): xs.append(None if xs[-1] is None else muf(xs[-1]))
        bad = MODE == 'vac' or (MODE == 'orbk' and xs[K] is not None and muf(xs[K]) != xs[K])
        if MODE.lstrip('M') in ('topcert', 'nmgood', 'exitm2', 'twofix', 'twogood', 'fixmax', 'goodnonmax'):
            Zs = [z for z in range(n) if F[bot][z] == bot]
            good = lambda y: le[y][a_of(L, F, y)] or y in desc(y)          # IsGood, from the definition
            dd = [t for t in tb if t != bot][-1]
            ownc = lambda y: any(h[p_] == 2 and le[y][F[y][p_]] for p_ in desc(y))            # own-row cell (= IsGood in W0)
            offg = not (h[dd] == 1 and (ownc(dd) if REL else good(dd))) and (BR != 'a' or h[dd] == 2) and (BR != 'b' or h[dd] == 1)
            M2s = [m_ for m_ in Zs if h[m_] == 2]
            exits = lambda m_: lamf(m_) is not None and F[bot][lamf(m_)] != bot
            exdom = lambda m_: exits(m_) and le[F[bot][lamf(m_)]][m_]
            gb = lambda m_: any(h[q] == 1 and le[q][m_] and good(q) for q in range(n))
            base_ = MODE.lstrip('M')
            if base_ in ('twofix', 'twogood', 'fixmax', 'goodnonmax'):
                Ats = [q for q in Zs if h[q] == 1]
                P = ((lambda q: lamf(q) is not None and F[bot][lamf(q)] == q) if 'xfix' in REL else (lambda q: muf(q) == q)) if base_ in ('twofix', 'fixmax') else good
                if base_ in ('twofix', 'twogood'): bad = sum(1 for q in Ats if P(q)) >= 2
                else: bad = offg and any(P(q) and not any(le[q][m_] for m_ in M2s) for q in Ats)
            else:
                pr = {'topcert': exdom, 'exitm2': exits, 'nmgood': gb}[base_]
                bad = offg and (not any(pr(m_) for m_ in M2s) if MODE[0] != 'M' else any(not pr(m_) for m_ in M2s))
        for k in range(1, K):
            x, y = xs[k], xs[k + 1]
            if x is None or y is None: continue
            if MODE == 'strictdep' and y != x and muf(y) != y and dep(y) >= dep(x): bad = True
            if MODE == 'oneexit':
                p = lamf(x)
                if p is not None and F[bot][p] != bot and muf(F[bot][p]) != F[bot][p]: bad = True
        assert ok and bad, 'SAT/Python mismatch'
        print(f'  lattice n={n} h={L.height}: SAT', flush=True)
        if DUMPF is not None: DUMPL.append(dict(sets=L.S, F=F))
        C['SAT'] += 1; HH[f'h{L.height}'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else:
        print(f'  lattice n={n} h={L.height}: UNSAT', flush=True); C['UNSAT'] += 1; HH[f'h{L.height}:unsat'] += 1
    S.delete()
if DUMPF: json.dump(DUMPL, open(DUMPF, 'w'))
print(MODE, K, 'mT' if MT else '', args, dict(C), dict(HH), 'smallest', best[0] if best else None)
if best and MODE != 'vac': json.dump(best[1], open(f'orbit_probe_{MODE}{"_mT" if MT else ""}_min{best[0]}.json', 'w'))
