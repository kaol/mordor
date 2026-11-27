"""Brief run 25 (briefer's encoding, written from the statements; not derived from cgall_probe.py).

World W(rows): a monotone F on a finite lattice L; rows of height <= 2 are variables, rows of height >= 3 are the
constant top (admissible: no hypothesis below constrains them).  phi = F(bot, .), Z = phi^-1(bot).
Always imposed:  a(bot) = bot (no y != bot with y <= phi(y));  ZT (Z has heights <= 2);  n1 (some height-2 element in Z);
  h(top) >= 3;  colours = atoms c of Z with c = phi(w) for some w (encoded exactly);  at least K colours;
  NoFix at every colour row c that lands: not (lambda(c) outside Z and phi(lambda(c)) = c).
Row constraints, imposed only on the row classes named by flags:
  L<cls>  the row lands (its descent from top reaches height <= 2; lambda = first such element)
  G<cls>  ColourGain: some colour c <= lambda(x) with c not <= x (implies L)
  T<cls>  Tb: no lower cell F(x, y) <= x at a high column y
  D<cls>  descent Tb: the row lands and lambda(x) is not <= x (implies L)
  classes: b = row bot, c = colour rows, q = every atom row of Z, p = pair-join rows (elements of Z above >= 2
           colours), z = every row of Z
Global shape flags:
  thin     no element of Z lies above two distinct colours
  nonthin  some element of Z lies above two distinct colours
  unb      no element of Z lies above every colour (implied by thin when K >= 2)
Quantifier: per lattice, EXISTS F in the world.  SAT = the world has a model with no mu-fixed colour, i.e. the
statement "this world forces a mu-fixed colour atom" FAILS on that lattice.  Every SAT model is replayed from the
definitions (assertion) and dumped to JSON.
  python3 rowset_probe.py TAG 'FLAGS' corpus... [maxn N] [K k]      e.g.  thin 'Lc Gc thin'  closure 6 12 1 40
Several worlds can be run on the same lattices:  'FLAGS1|FLAGS2'  (the second is typically the calibrated mutant)."""
import sys, itertools, json, time, os
A = '/home/user/mordor/experiments/amalgamation'
sys.path.insert(0, A); sys.path.insert(0, A + '/../separation')
from pysat.solvers import Cadical153
from pysat.card import CardEnc
from tight_probe import lattices
from rstages import a_of

TAG = sys.argv[1]; WORLDS = [w.split() for w in sys.argv[2].split('|')]; args = sys.argv[3:]
MAXN = None; K = 2
if 'K' in args: k = args.index('K'); K = int(args[k + 1]); args = args[:k] + args[k + 2:]
print(f'rowset_probe {TAG} | per lattice: EXISTS F | SAT = world has a model with no mu-fixed colour (statement fails) '
      f'| worlds {WORLDS} | at least {K} colours | corpus {args} maxn {MAXN}', flush=True)

def solve(L, FL):
    n, le, h, bot, top = L.n, L.le, L.rank, L.bot, L.top
    NO = h[top] + 1
    low = [x for x in range(n) if h[x] <= 2]; atoms = [x for x in range(n) if h[x] == 1]
    high = [y for y in range(n) if h[y] > 2]
    S = Cadical153(); V = {}; NX = [1]
    def v(*key):
        if key not in V: V[key] = NX[0]; NX[0] += 1
        return V[key]
    add = S.add_clause
    f = lambda x, y, u: v('f', x, y, u)
    for x in low:                                   # F(x, y) is a function, monotone in y and in x (low rows)
        for y in range(n):
            ls = [f(x, y, u) for u in range(n)]; add(ls)
            for p, q in itertools.combinations(ls, 2): add([-p, -q])
            for y2 in L.covers_up[y]:
                for u in range(n): add([-f(x, y, u)] + [f(x, y2, w) for w in range(n) if le[u][w]])
            for x2 in L.covers_up[x]:
                if h[x2] <= 2:
                    for u in range(n): add([-f(x, y, u)] + [f(x2, y, w) for w in range(n) if le[u][w]])
    Z = lambda y: f(bot, y, bot)
    for y in range(n):
        if y != bot:
            for u in range(n):
                if le[y][u]: add([-f(bot, y, u)])                 # a(bot) = bot
    for y in high: add([-Z(y)])                                    # ZT
    add([Z(y) for y in low if h[y] == 2])                          # n1
    col = {c: v('col', c) for c in atoms}
    for c in atoms:
        add([-col[c], Z(c)]); add([-col[c]] + [f(bot, w, c) for w in range(n)])
        for w in range(n): add([-Z(c), -f(bot, w, c), col[c]])
    enc = CardEnc.atleast([col[c] for c in atoms], bound=K, top_id=NX[0])
    for cl in enc.clauses: add(cl)
    NX[0] = max([NX[0]] + [abs(l) for cl in enc.clauses for l in cl]) + 1     # later ids clear of card auxiliaries
    # pair-join indicator for height-2 z: Z(z) and two colours below
    pj = {}
    for z in low:
        if h[z] != 2: continue
        cs = [c for c in atoms if le[c][z]]
        pj[z] = v('pj', z)
        pairs = list(itertools.combinations(cs, 2))
        for (c1, c2) in pairs: add([-Z(z), -col[c1], -col[c2], pj[z]])
        add([-pj[z], Z(z)])
        add([-pj[z]] + [v('pp', z, c1, c2) for (c1, c2) in pairs])
        for (c1, c2) in pairs: add([-v('pp', z, c1, c2), col[c1]]); add([-v('pp', z, c1, c2), col[c2]])
    if 'thin' in FL:
        for z in low:
            if h[z] == 2:
                for c1, c2 in itertools.combinations([c for c in atoms if le[c][z]], 2): add([-Z(z), -col[c1], -col[c2]])
    if 'nonthin' in FL: add([pj[z] for z in pj])
    if 'unb' in FL:
        for z in low: add([-Z(z)] + [col[c] for c in atoms if not le[c][z]])
    # descents and landing for every low row (definitions only; constraints are conditional)
    it = lambda x, j, z: v('it', x, j, z)
    lam = {}
    for x in low:
        for z in range(n): add([it(x, 0, z)] if z == top else [-it(x, 0, z)])
        for j in range(NO):
            for z in range(n):
                for u in range(n): add([-it(x, j, z), -f(x, z, u), it(x, j + 1, u)])
            for z, z2 in itertools.combinations(range(n), 2): add([-it(x, j + 1, z), -it(x, j + 1, z2)])
        for p in low:
            ts = []
            for j in range(1, NO + 1):
                t = v('t', x, j, p); ts.append(t)
                add([-t, it(x, j, p)]); add([-t] + [it(x, j - 1, z) for z in high])
                for z in high: add([t, -it(x, j, p), -it(x, j - 1, z)])
            lam[x, p] = v('lam', x, p)
            for t in ts: add([-t, lam[x, p]])
            add([-lam[x, p]] + ts)
        lands = v('lands', x); add([-lands] + [lam[x, p] for p in low])
        for p in low: add([-lam[x, p], lands])
    def cls_guard(x, cls):            # literal list G such that "row x in class" is  AND(G)  (empty = always)
        if cls == 'b': return [] if x == bot else None
        if cls == 'c': return [col[x]] if x in col else None
        if cls == 'p': return [pj[x]] if x in pj else None
        if cls == 'q': return [Z(x)] if h[x] == 1 else None
        if cls == 'z': return [Z(x)]
    for x in low:
        if h[x] == 1:                                   # NoFix at colour rows
            for p in low: add([-col[x], -lam[x, p], Z(p), -f(bot, p, x)])
        for cls in 'bcqpz':
            g = cls_guard(x, cls)
            if g is None: continue
            ng = [-l for l in g]
            if ('L' + cls) in FL or ('G' + cls) in FL or ('D' + cls) in FL: add(ng + [v('lands', x)])
            if ('D' + cls) in FL:
                for p in low:
                    if le[p][x]: add(ng + [-lam[x, p]])
            if ('G' + cls) in FL:
                for p in low: add(ng + [-lam[x, p]] + [col[c] for c in atoms if le[c][p] and not le[c][x]])
            if ('T' + cls) in FL and x != bot:
                for y in high:
                    for u in range(n):
                        if le[u][x]: add(ng + [-f(x, y, u)])
    ok = S.solve()
    if not ok:
        S.delete(); return None
    m = set(l for l in S.get_model() if l > 0); S.delete()
    F = [[(next(u for u in range(n) if V[('f', x, y, u)] in m) if x in low else top) for y in range(n)] for x in range(n)]
    return F

def replay(L, F, FL):
    n, le, h, bot, top = L.n, L.le, L.rank, L.bot, L.top
    for x in range(n):
        for y in range(n):
            for y2 in range(n):
                if le[y][y2]: assert le[F[x][y]][F[x][y2]]
                if le[x][y2]: assert le[F[x][y]][F[y2][y]]
    phi = F[bot]; Zs = [y for y in range(n) if phi[y] == bot]
    assert a_of(L, F, bot) == bot and all(h[z] <= 2 for z in Zs) and any(h[z] == 2 for z in Zs) and h[top] >= 3
    def lamf(x):
        z = top; seen = []
        while z not in seen:
            if h[z] <= 2: return z
            seen.append(z); z = F[x][z]
        return None
    cols = sorted({phi[w] for w in range(n) if h[phi[w]] == 1 and phi[w] in Zs})
    assert len(cols) >= K
    for c in cols:
        p = lamf(c)
        if p is not None: assert not (p not in Zs and phi[p] == c), 'fixed colour'
    two = lambda z: sum(1 for c in cols if le[c][z]) >= 2
    pjs = [z for z in Zs if h[z] == 2 and two(z)]
    if 'thin' in FL: assert not pjs
    if 'nonthin' in FL: assert pjs
    if 'unb' in FL: assert not any(all(le[c][z] for c in cols) for z in Zs)
    classes = {'b': [bot], 'c': cols, 'q': [z for z in Zs if h[z] == 1], 'p': pjs, 'z': Zs}
    for cls, rows in classes.items():
        for x in rows:
            if ('L' + cls) in FL or ('G' + cls) in FL or ('D' + cls) in FL: assert lamf(x) is not None
            if ('D' + cls) in FL: assert not le[lamf(x)][x]
            if ('G' + cls) in FL: assert any(le[c][lamf(x)] and not le[c][x] for c in cols)
            if ('T' + cls) in FL and x != bot: assert all(not le[F[x][y]][x] for y in range(n) if h[y] > 2)
    return cols, pjs

tot = [dict(SAT=0, UNSAT=0) for _ in WORLDS]; dumps = [[] for _ in WORLDS]; t0 = time.time()
def corpora(args):                      # several corpora separated by '+'
    cur = []
    for a in args + ['+']:
        if a == '+':
            mx = None
            if 'maxn' in cur: k = cur.index('maxn'); mx = int(cur[k + 1]); cur = cur[:k] + cur[k + 2:]
            if cur:
                for L in lattices(cur):
                    if mx is None or L.n <= mx: yield L
            cur = []
        else: cur.append(a)
for L in corpora(args):
    if MAXN is not None and L.n > MAXN: continue
    if L.rank[L.top] < 3: continue
    if sum(1 for x in range(L.n) if L.rank[x] == 1) < K: continue
    line = []
    for wi, FL in enumerate(WORLDS):
        F = solve(L, FL)
        if F is None: tot[wi]['UNSAT'] += 1; line.append('UNSAT')
        else:
            cols, pjs = replay(L, F, FL); tot[wi]['SAT'] += 1; line.append(f'SAT(cols {cols}, pairjoins {pjs})')
            dumps[wi].append(dict(sets=L.S, F=F, colours=cols, pairjoins=pjs, world=' '.join(FL), tag=TAG))
            json.dump(dumps[wi], open(f'{TAG}_w{wi}.json', 'w'))          # incremental: survives a timeout
    print(f'  lattice n={L.n} H={L.height} atoms={sum(1 for x in range(L.n) if L.rank[x] == 1)}: ' + ' | '.join(line) + f'  [{time.time() - t0:.0f}s]', flush=True)
for wi, FL in enumerate(WORLDS):
    print('RESULT', TAG, ' '.join(FL), args, tot[wi])
    if dumps[wi]:
        fn = f'{TAG}_w{wi}.json'; json.dump(dumps[wi], open(fn, 'w')); print('  dumped', fn)
