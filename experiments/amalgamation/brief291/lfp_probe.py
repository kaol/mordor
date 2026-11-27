"""Run-17 briefer probe (exact SAT, one-hot rows; encoding written from the definitions, after lead2_probe.py's layout).
WORLD W0-flat (= W0 and n1 with Tb dropped at the height-2 rows of Z): a(bot) = bot; ZT; n1; h(top) >= 3;
  Ta at every row x != bot of Z (no high y with y <= F(x,y)); Tb at every atom row of Z (no high y with F(q,y) <= q).
  (high = height >= 3.)  Rows F(x,.) are variables for x of height <= 2; rows of high x are the constant top in the replay.
DEFINITIONS.  Y = high elements on the descents (from top) of rows of Z; Ymin = minimal elements of Y.
  b(y) = lfp F(., y); b(y) in Z <=> some x in Z has F(x, y) <= x.   mu(x) = lambda(x) if lambda(x) in Z else F(bot, lambda(x)).
MODES (quantifier: exists F in W0-flat on the lattice, with ...):
  lead : SAT = NoFix and EVERY y in Ymin has b(y) not in Z        (LfpMin fails)
  mutA : SAT = NoFix and SOME y in Ymin has b(y) not in Z         (LfpMinAll fails: calibrated mutant, the refuted relative;
                                                                   refuted by stored model direct290/nf_cl.json#18)
  gt   : SAT = NoFix and no m in M2 with lambda(m) = m             (GoodTop fails; control against lead2_probe/orbit_probe)
  uniq : SAT = at least two distinct x in Z\\bot with mu(x) = x    (AtMost1Mu fails)
  mutU : SAT = at least two distinct x in Z\\bot with mu(x) <= x   (|Low| <= 1 fails: calibrated mutant of uniq)
  nofix: SAT = NoFix                                               (vacuity run: the hypothesis world alone)
FLAGS: E1..E6 exact N (t_N != bot = t_(N+1)); maxn K (skip |L| > K).
Every SAT model is decoded and replayed in Python from the definitions (world.py, independent of the clauses); a mismatch
aborts.  Per-lattice progress is printed.  Smallest SAT model per mode -> lfp_<mode>_<tag>_min<n>.json (and every SAT model
of mode lead/uniq/gt -> lfp_<mode>_<tag>_all.json).
  python3 lfp_probe.py MODES TAG CORPUS [+ CORPUS ...] [E<k>] [maxn K]"""
import sys, os, itertools, collections, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from pysat.solvers import Cadical153
from tight_probe import lattices
from world import W

MODES = sys.argv[1].split(','); TAG = sys.argv[2]; args = sys.argv[3:]
MAXN = None
if 'maxn' in args: k_ = args.index('maxn'); MAXN = int(args[k_ + 1]); args = args[:k_] + args[k_ + 2:]
NEXS = [int(a[1:]) for a in args if a[0] == 'E' and a[1:].isdigit()] or [0]     # several E<k>: each lattice solved per N
args = [a for a in args if not (a[0] == 'E' and a[1:].isdigit())]
NEX = 0
SATM = {'lead': 'NoFix and every y in Ymin has b(y) not in Z (LfpMin FAILS)',
        'mutA': 'NoFix and some y in Ymin has b(y) not in Z (mutant LfpMinAll FAILS)',
        'gt': 'NoFix and no m in M2 lands on itself (GoodTop FAILS)',
        'uniq': 'two distinct nonzero mu-fixed points (AtMost1Mu FAILS)',
        'mutU': 'two distinct x in Z\\bot with mu(x) <= x (mutant |Low|<=1 FAILS)',
        'nofix': 'NoFix (the hypothesis world alone)'}
for M_ in MODES:
    print(f'lfp_probe {M_} | quantifier: exists F in W0-flat{" with exact N in " + str(NEXS) if NEXS != [0] else ""} | SAT = {SATM[M_]} | corpus {args}', flush=True)

def solve(L, MODE):
    n = L.n; le = L.le; h = L.rank; bot = L.bot; top = L.top
    low = [x for x in range(n) if h[x] <= 2]; hi = [y for y in range(n) if h[y] >= 3]; NO = h[top] + 1
    S = Cadical153(); V = {}
    def v(*k):
        if k not in V: V[k] = len(V) + 1
        return V[k]
    add = S.add_clause; f = lambda x, y, u: v('f', x, y, u); Z = lambda y: f(bot, y, bot)
    for x in low:
        for y in range(n):
            ls = [f(x, y, u) for u in range(n)]; add(ls)
            for a_, b_ in itertools.combinations(ls, 2): add([-a_, -b_])
            for y2 in L.covers_up[y]:
                for u in range(n): add([-f(x, y, u)] + [f(x, y2, u2) for u2 in range(n) if le[u][u2]])
        for x2 in L.covers_up[x]:
            if h[x2] > 2: continue
            for y in range(n):
                for u in range(n): add([-f(x, y, u)] + [f(x2, y, u2) for u2 in range(n) if le[u][u2]])
    for y in range(n):                                        # a(bot) = bot
        if y != bot:
            for u in range(n):
                if le[y][u]: add([-f(bot, y, u)])
    for y in hi: add([-Z(y)])                                 # ZT
    add([Z(y) for y in range(n) if h[y] == 2])                # n1
    it = lambda x, j, z: v('it', x, j, z)
    for x in low:
        for z in range(n): add([it(x, 0, z)] if z == top else [-it(x, 0, z)])
        for j in range(NO):
            for z in range(n):
                for u in range(n): add([-it(x, j, z), -f(x, z, u), it(x, j + 1, u)])
            for z, z2 in itertools.combinations(range(n), 2): add([-it(x, j + 1, z), -it(x, j + 1, z2)])
    if NEX:
        if NEX + 1 > NO: return 'skip'
        add([-it(bot, NEX, bot)]); add([it(bot, NEX + 1, bot)])
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
    for x in low:                                             # (T) of W0-flat at rows x != bot of Z
        if x == bot: continue
        for y in hi:
            for u in range(n):
                if le[y][u]: add([-Z(x), -f(x, y, u)])                        # Ta
                if h[x] == 1 and le[u][x]: add([-Z(x), -f(x, y, u)])          # Tb at atom rows
    atoms = [q for q in low if h[q] == 1]; M2c = [m for m in low if h[m] == 2]
    def nofix():
        for q in atoms:
            for p in low: add([-Z(q), -lam[q, p], -f(bot, p, q)])
    def ydefs():                                              # inY(y) <-> OR_{x,j} (Z(x) & it(x,j,y))
        for y in hi:
            ws = []
            for x in low:
                for j in range(NO + 1):
                    w_ = v('w', x, j, y); ws.append(w_)
                    add([-w_, Z(x)]); add([-w_, it(x, j, y)]); add([w_, -Z(x), -it(x, j, y)])
            add([-v('inY', y)] + ws)
            for w_ in ws: add([-w_, v('inY', y)])
    def bnotZ(sel, y):                                        # sel -> no x in Z with F(x,y) <= x
        for x in low:
            for u in range(n):
                if le[u][x]: add([-sel, -Z(x), -f(x, y, u)])
    if MODE in ('lead', 'mutA', 'gt', 'nofix'): nofix()
    if MODE == 'lead':
        ydefs()
        for y in hi:
            ym = v('ym', y); add([ym, -v('inY', y)] + [v('inY', z) for z in hi if z != y and le[z][y]]); bnotZ(ym, y)
    if MODE == 'mutA':
        ydefs(); ss_ = []
        for y in hi:
            s_ = v('s', y); ss_.append(s_); add([-s_, v('inY', y)])
            for z in hi:
                if z != y and le[z][y]: add([-s_, -v('inY', z)])
            bnotZ(s_, y)
        add(ss_)
    if MODE == 'gt':
        for m in M2c: add([-Z(m), -lam[m, m]])
    if MODE in ('uniq', 'mutU'):
        fx = {}
        for x in low:
            if x == bot: continue
            o = v('fx', x); fx[x] = o; add([-o, Z(x)]); gs = []
            for p in low:
                g = v('g', x, p); gs.append(g); add([-g, lam[x, p]])
                if MODE == 'uniq':
                    if p == x and h[x] == 2: add([-g, Z(p)])                                   # self-landing
                    elif h[x] == 1: add([-g, f(bot, p, x)])                                    # exit-fixed atom
                    else: add([-g])
                else:                                                                          # mu(x) <= x
                    lits = ([Z(p)] if le[p][x] else []) + [f(bot, p, c) for c in range(n) if c != bot and le[c][x]]
                    add([-g] + lits)
            add([-o] + gs)
        xs = list(fx); prs = []
        for x1, x2 in itertools.combinations(xs, 2):
            pr = v('pr', x1, x2); prs.append(pr); add([-pr, fx[x1]]); add([-pr, fx[x2]])
        add(prs if prs else [])
    if not S.solve(): S.delete(); return None
    m = set(l for l in S.get_model() if l > 0)
    F = [[(next(u for u in range(n) if V[('f', x, y, u)] in m) if x in low else top) for y in range(n)] for x in range(n)]
    S.delete(); return F

def mu(w, x):
    p = w.lam(x); return p if w.F[w.bot][p] == w.bot else w.F[w.bot][p]
def replay(L, F, MODE):
    w = W(L.S, F); assert w.w0flat(), 'replay: not in W0-flat'
    d, N = w.dN()
    if NEX: assert N == NEX, f'replay: N = {N} != {NEX}'
    le = w.le; Zs = set(w.Z)
    Y = set(v_ for x in w.Z for v_ in w.desc(x)[:w.lidx(x)]); Ym = [y for y in Y if not any(z != y and le[z][y] for z in Y)]
    Z1 = [x for x in w.Z if x != w.bot]
    if MODE == 'lead': ok = w.nofix() and all(w.b(y) not in Zs for y in Ym)
    elif MODE == 'mutA': ok = w.nofix() and any(w.b(y) not in Zs for y in Ym)
    elif MODE == 'gt': ok = w.nofix() and not w.witnesses()
    elif MODE == 'uniq': ok = sum(1 for x in Z1 if mu(w, x) == x) >= 2
    elif MODE == 'mutU': ok = sum(1 for x in Z1 if le[mu(w, x)][x]) >= 2
    else: ok = w.nofix()
    br = 'a' if w.h[d] == 2 else ('g' if (le[d][w.a(d)] or d in w.desc(d)) else 'b')
    return ok, br, N, w.noexit()

def corpora(a):
    cur = []
    for t in a + ['+']:
        if t == '+':
            if cur: yield from lattices(cur)
            cur = []
        else: cur.append(t)
KEYS = [(M_, k) for M_ in MODES for k in NEXS]
C = {K: collections.Counter() for K in KEYS}; best = {}; allm = collections.defaultdict(list)
t0 = time.time(); cnt = 0
for L in corpora(args):
    if MAXN is not None and L.n > MAXN: continue
    if L.rank[L.top] < 3: continue
    cnt += 1; row = []
    for (M_, NEX) in KEYS:
        K = (M_, NEX); tg = M_ + (f'/N{NEX}' if NEX else '')
        F = solve(L, M_)
        if F == 'skip': C[K]['skip(N)'] += 1; row.append(f'{tg}:skip'); continue
        if F is None: C[K]['UNSAT'] += 1; row.append(f'{tg}:UNSAT'); continue
        ok, br, N, ne = replay(L, F, M_)
        assert ok, f'SAT/Python mismatch on {tg}'
        C[K]['SAT'] += 1; C[K]['SAT_' + br] += 1; C[K][f'SAT_N{N}'] += 1; C[K]['SAT_noexit' if ne else 'SAT_exit'] += 1
        row.append(f'{tg}:SAT({br},N{N},{"noexit" if ne else "exit"})')
        mod = dict(sets=L.S, F=F, mode=M_, N=N, world='W0-flat', tag=TAG)
        if M_ in ('lead', 'uniq', 'gt'): allm[M_].append(mod)
        if M_ not in best or L.n < best[M_][0]: best[M_] = (L.n, mod)
    print(f'  lattice #{cnt} n={L.n} h={L.height} [{time.time() - t0:.0f}s]: ' + ' '.join(row), flush=True)
print('SUMMARY', TAG, args, NEXS if NEXS != [0] else '', f'{time.time() - t0:.0f}s', f'{cnt} lattices')
for (M_, k) in KEYS: print('  ', M_, f'N={k}' if k else '', '|', SATM[M_], '|', dict(C[(M_, k)]))
for M_, (n_, Mod) in best.items():
    fn = os.path.join(os.getcwd(), f'lfp_{M_}_{TAG}_min{n_}.json'); json.dump(Mod, open(fn, 'w')); print('  smallest', M_, n_, '->', fn)
for M_, L_ in allm.items():
    fn = os.path.join(os.getcwd(), f'lfp_{M_}_{TAG}_all.json'); json.dump(L_, open(fn, 'w')); print('  all SAT models', M_, len(L_), '->', fn)
