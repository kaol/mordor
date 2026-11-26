"""Run-16 briefer, LEAD probe (ZCell).  World W0b = W0 with Tb dropped at the height-2 rows of Z (relaxation noTb2):
a(bot) = bot, ZT, n1, h(top) >= 3, Ta at every row of Z, Tb at bot (ZT) and at every atom row.  In W0b the hypothesis
NoFix (no atom of Z is mu-fixed) HAS models (run 1: 82 of 82 lattices), so the contradiction-mode lead is tested there.
  OwnZCell: some atom q of Z and some z in Z of height 2 on row q's own descent with q <= F(q, z).
  (In W0 OwnZCell is impossible: upTrap_land makes row z land at z, against land_not_le at z; see the brief.)
MODES (each solved on every lattice; quantifier: exists F in W0b):
  lead : SAT = NoFix and not OwnZCell                          (the LEAD fails)
  mutA : SAT = NoFix and no own Z-cell at z = lambda(bot)      (ANCHORED MUTANT: the cell named at the bot-landing)
  mutB : SAT = NoFix and no own Z-STALL (q <= F(q, z) = z)     (STALL-ONLY MUTANT)
  vac  : SAT = NoFix has a model in W0b                         (vacuity check of the lead's hypothesis world)
Older docstring of the encoding follows.
Run-16 briefer: which hypotheses does EXISTENCE (CertAtom) use?  Role analysis of the open target itself.

Encoding (written from the definitions, after orbit_probe.py's one-hot layout): rows F(x, .) only for low x (height <= 2),
one-hot, monotone in y (covers) and in x (covers inside the low set); rows of high x are the constant top in the replay
(they never enter Z, landings, mu or R_2 in this world).  World W0_R:
  a(bot) = bot (no y != bot with y <= F(bot, y));  ZT (Z = {F(bot, y) = bot} has no element of height >= 3);
  n1 (some height-2 element in Z);  h(top) >= 3;
  (T) at the rows x of Z other than bot, as modified by the relaxation R:
     Ta(x): no y of height >= 3 with y <= F(x, y)        (= row x lands, ta_iff_lands)
     Tb(x): no y of height >= 3 with F(x, y) <= x
     DescTb(x): lambda(x) is not <= x (descent form of Tb; requires the row to land)
Exact descents it(x, j, .) for j <= h(top) + 1; lambda(x) = first element of height <= 2 on row x's descent.
Fixed atom (exit form): q an atom of Z, lambda(q) = p and F(bot, p) = q (then p is not in Z).
  MODE nofix : SAT = in W0_R no atom of Z is mu-fixed (CertAtom FAILS in the relaxed world)
  MODE nogood: SAT = in W0_R no atom of Z is good in the own-cell form (some height-2 p on row q's descent with
               q <= F(q, p)); with R = full this is GoodAtom1 failing
Relaxations R (comma list in argv[2]; each solved separately on every lattice):
  full     all of (T) at every row of Z                       (control: CertAtom is conjectured, expect UNSAT)
  noTb2    Tb dropped at the height-2 rows
  noTb1    Tb dropped at the atom rows
  noTbD    Tb dropped at the row of d only (d = last nonzero element of the bot-descent; no effect in branch a)
  noTb     Tb dropped at every row other than bot (Ta kept everywhere)
  desc1    at the atom rows Tb replaced by DescTb
  desc12   at every row other than bot Tb replaced by DescTb
  noTa2    Ta dropped at the height-2 rows (Tb kept)
  noTa1    Ta dropped at the atom rows (Tb kept)
  desc2    at the height-2 rows Tb replaced by DescTb (DescTb2)
  descD    at the row of d only, Tb replaced by DescTb (every other row keeps full Tb)
  onlyD2   at the height-2 rows Tb kept only at the row of d (atom rows keep full Tb)
  onlyD1   at the atom rows Tb kept only at the row of d (height-2 rows keep full Tb)
  onlyD    Tb kept only at the row of d (and at bot, = ZT); Ta kept everywhere
Every SAT model is decoded and replayed in Python from the definitions (world_R and the mode), else assertion error.
  python3 certrole.py MODE R1,R2,... CORPUS [+ CORPUS ...] [maxn N]   (CORPUS = closure K M SEED CNT | tall K M SEED CNT | file PATH...)
Per-lattice progress is printed; the smallest SAT model per relaxation is written to certrole_<MODE>_<R>_min<n>.json."""
import sys, os, itertools, collections, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'separation')); sys.path.insert(0, os.path.join(HERE, 'amalg'))
from pysat.solvers import Cadical153
from tight_probe import lattices
from rstages import a_of

MODES = sys.argv[1].split(','); RELS = sys.argv[2].split(','); args = sys.argv[3:]; MODE = None
MAXN = None
if 'maxn' in args: k_ = args.index('maxn'); MAXN = int(args[k_ + 1]); args = args[:k_] + args[k_ + 2:]
SATM = {'lead': 'NoFix and not OwnZCell in W0b (LEAD fails)', 'mutA': 'NoFix and no own Z-cell at z = lambda(bot) (anchored mutant fails)',
        'mutB': 'NoFix and no own Z-stall (stall-only mutant fails)', 'vac': 'NoFix has a model in W0b',
        'nofix': 'in W0_R no atom of Z is mu-fixed (CertAtom fails)',
        'nogood': 'in W0_R no atom of Z has an own-row cell (GoodAtom1 fails, own-cell form)'}
for M_ in MODES: print(f'lead_probe {M_} | quantifier: exists F in W0_R with ... | SAT = {SATM[M_]} | relaxations {RELS} | corpus {args}', flush=True)

def rule(R, x, h):
    """(Ta, Tb, DescTb) at row x != bot of Z under relaxation R."""
    Ta, Tb, D = True, True, False
    if R == 'noTb2' and h[x] == 2: Tb = False
    if R == 'noTb1' and h[x] == 1: Tb = False
    if R == 'noTb': Tb = False
    if R == 'desc1' and h[x] == 1: Tb, D = False, True
    if R == 'desc12': Tb, D = False, True
    if R == 'noTa2' and h[x] == 2: Ta = False
    if R == 'noTa1' and h[x] == 1: Ta = False
    if R == 'desc2' and h[x] == 2: Tb, D = False, True
    return Ta, Tb, D

def solve(L, R):
    n = L.n; le = L.le; h = L.rank; bot = L.bot; top = L.top
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
    dv = lambda z: v('dv', z)                                  # d = last nonzero element of the bot-descent
    for z in range(n):
        if z == bot: add([-dv(z)]); continue
        js = [v('dvj', z, j) for j in range(NO)]
        for j in range(NO):
            t = v('dvj', z, j); add([-t, it(bot, j, z)]); add([-t, it(bot, j + 1, bot)])
            add([t, -it(bot, j, z), -it(bot, j + 1, bot)])
        add([-dv(z)] + js)
        for t in js: add([-t, dv(z)])
    for x in low:                                             # (T) at rows of Z (bot: Tb is ZT, Ta is a(bot) = bot)
        if x == bot: continue
        Ta, Tb, D = rule(R, x, h)
        for y in range(n):
            if h[y] <= 2: continue
            for u in range(n):
                if Ta and le[y][u]: add([-Z(x), -f(x, y, u)])
                if le[u][x]:
                    if R in ('noTbD', 'descD'): add([-Z(x), -f(x, y, u), dv(x)])     # waived only at the row of d
                    elif R == 'onlyD' or (R == 'onlyD2' and h[x] == 2) or (R == 'onlyD1' and h[x] == 1):
                        add([-Z(x), -f(x, y, u), -dv(x)])                              # kept only at the row of d
                    elif Tb: add([-Z(x), -f(x, y, u)])
        if R == 'descD':
            add([-dv(x)] + [lam[x, p] for p in low])                      # d's row lands, lambda(d) not <= d
            for p in low:
                if le[p][x]: add([-dv(x), -lam[x, p]])
        if D:
            add([-Z(x)] + [lam[x, p] for p in low])                       # the row lands
            for p in low:
                if le[p][x]: add([-Z(x), -lam[x, p]])                     # lambda(x) not <= x
    atoms = [q for q in low if h[q] == 1]
    if MODE in ('lead', 'mutA', 'mutB', 'vac'):
        for q in atoms:
            for p in low: add([-Z(q), -lam[q, p], -f(bot, p, q)])          # NoFix
        for q in atoms:
            for z in low:
                if h[z] != 2 or not le[q][z]: continue
                for j in range(NO + 1):
                    if MODE == 'lead':
                        for u in range(n):
                            if le[q][u]: add([-Z(q), -Z(z), -it(q, j, z), -f(q, z, u)])
                    elif MODE == 'mutA':
                        for u in range(n):
                            if le[q][u]: add([-Z(q), -Z(z), -it(q, j, z), -f(q, z, u), -lam[bot, z]])
                    elif MODE == 'mutB': add([-Z(q), -Z(z), -it(q, j, z), -f(q, z, z)])
    elif MODE == 'nofix':
        for q in atoms:
            for p in low: add([-Z(q), -lam[q, p], -f(bot, p, q)])
    else:
        for q in atoms:
            for j in range(NO + 1):
                for p in low:
                    if h[p] != 2: continue
                    for u in range(n):
                        if le[q][u]: add([-Z(q), -it(q, j, p), -f(q, p, u)])
    if not S.solve(): S.delete(); return None
    m = set(l for l in S.get_model() if l > 0)
    F = [[(next(u for u in range(n) if V[('f', x, y, u)] in m) if x in low else top) for y in range(n)] for x in range(n)]
    S.delete(); return F

def replay(L, F, R):
    n = L.n; le = L.le; h = L.rank; bot = L.bot; top = L.top
    def desc(x):
        z = top; s = []
        while z not in s: s.append(z); z = F[x][z]
        return s
    lamf = lambda x: next((z for z in desc(x) if h[z] <= 2), None)
    Zs = [z for z in range(n) if F[bot][z] == bot]
    ok = a_of(L, F, bot) == bot and all(h[z] <= 2 for z in Zs) and any(h[z] == 2 for z in Zs) and h[top] >= 3
    tb = desc(bot); dd = [t for t in tb if t != bot][-1]
    for x in Zs:
        if x == bot: continue
        Ta, Tb, D = rule(R, x, h)
        if R == 'noTbD' and x == dd: Tb = False
        if R == 'descD' and x == dd: Tb, D = False, True
        if R == 'onlyD' or (R == 'onlyD2' and h[x] == 2) or (R == 'onlyD1' and h[x] == 1): Tb = (x == dd)
        for y in range(n):
            if h[y] <= 2: continue
            if Ta and le[y][F[x][y]]: ok = False
            if Tb and le[F[x][y]][x]: ok = False
        if D and (lamf(x) is None or le[lamf(x)][x]): ok = False
    ats = [q for q in Zs if h[q] == 1]
    if MODE in ('lead', 'mutA', 'mutB', 'vac'):
        ok = ok and not any(lamf(q) is not None and F[bot][lamf(q)] == q for q in ats)
        cells = [(q, z) for q in ats for z in desc(q) if z in Zs and h[z] == 2 and le[q][F[q][z]]]
        if MODE == 'lead': ok = ok and not cells
        if MODE == 'mutA': ok = ok and not any(z == lamf(bot) for q, z in cells)
        if MODE == 'mutB': ok = ok and not any(F[q][z] == z for q, z in cells)
    elif MODE == 'nofix': ok = ok and not any(lamf(q) is not None and F[bot][lamf(q)] == q for q in ats)
    else: ok = ok and not any(h[p] == 2 and le[q][F[q][p]] for q in ats for p in desc(q))
    br = 'a' if h[dd] == 2 else 'atom'
    return ok, br

KEYS = [(M_, R) for M_ in MODES for R in RELS]
C = {K: collections.Counter() for K in KEYS}; best = {}
t0 = time.time(); cnt = 0
def corpora(a):
    cur = []
    for t in a + ['+']:
        if t == '+':
            if cur: yield from lattices(cur)
            cur = []
        else: cur.append(t)
for L in corpora(args):
    if MAXN is not None and L.n > MAXN: continue
    if L.rank[L.top] < 3: continue
    cnt += 1; row = []
    for (M_, R) in KEYS:
        MODE = M_; K = (M_, R); tag = f'{M_}/{R}'
        F = solve(L, R)
        if F is None: C[K]['UNSAT'] += 1; row.append(f'{tag}:UNSAT'); continue
        ok, br = replay(L, F, R)
        assert ok, f'SAT/Python mismatch on {tag}'
        C[K]['SAT'] += 1; C[K]['SAT_' + br] += 1; row.append(f'{tag}:SAT({br})')
        if K not in best or L.n < best[K][0]: best[K] = (L.n, dict(sets=L.S, F=F, relaxation=R, mode=M_))
    print(f'  lattice #{cnt} n={L.n} h={L.height} [{time.time() - t0:.0f}s]: ' + ' '.join(row), flush=True)
print('SUMMARY', args)
for K in KEYS: print('  ', K, dict(C[K]))
for (M_, R), (n_, Mod) in best.items():
    fn = os.path.join(os.getcwd(), f'lead_{M_}_{R}_min{n_}.json'); json.dump(Mod, open(fn, 'w')); print('  smallest', M_, R, n_, '->', fn)
