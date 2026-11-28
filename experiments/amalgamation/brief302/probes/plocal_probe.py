"""Brief run 27, briefer's tester (exact, per lattice).  Base world W = PairSelf's world without D_p ('pairselfM'):
  rows of height <= 2 are variables (one-hot, monotone in both arguments); rows of height >= 3 are the constant top;
  a(bot) = bot; ZT; n1 (some height-2 element of Z); h(top) >= 3;
  colours = atoms c of Z with c = phi(w) for some w (exact); colours unbounded in Z; some pair-join (element of Z of
  height 2 above two colours); every colour row lands, has ColourGain (a colour <= lambda(c), != c) and Tb (no lower
  cell at a high column); every pair-join row lands; NoFix (no atom q of Z with lambda(q) outside Z, phi(lambda(q)) = q).
Modes (each is EXISTS F on the lattice; SAT = the named statement FAILS on this lattice):
  plocal   PairLocal fails: colours c0 != c1, pair-join m >= c0, c1, lambda(c0) = m, c0 <= lambda(c1), lambda(m) != m
  plocalM  MUTANT (nearest refuted relative = d2pM of §301, 'lambda(c0) = m a pair-join => lambda(m) = m'):
           as plocal with 'c0 <= lambda(c1)' dropped
  plne     the open half of PairLocal: plocal with lambda(c1) != m
  esc      EscapeLow fails: W and NO pair-join m with lambda(m) = m having a colour c <= m with lambda(c) <= m
  escM     MUTANT (refuted relative ClosedColour-in-W, 3 stored models): W and no colour c with c <= lambda(c) = m in Z
           and c <= lambda(m)
  cx       CrossExists fails: W and NO cross pair (colours a != b with a v b in Z, b <= lambda(a), a <= lambda(b))
  cp       CrossPair fails: W and a cross pair a, b with lambda(a v b) != a v b
  caseB    CaseBEmpty fails: W and every colour row exits (lambda(c) outside Z for every colour c)
  caseAall MUTANT (same family, a case-emptiness statement): W and every colour row lands in Z
  cpM      MUTANT OneCross (CrossPair with 'a <= lambda(b)' dropped): W, colours a != b, a v b in Z, b <= lambda(a),
           lambda(a v b) != a v b
Flags: E<k> exact N = k (index of d, the last nonzero element of the bot-descent); maxn N; min<K> (>= K colours).
Usage: python3 plocal_probe.py MODE1,MODE2 corpus... [maxn N] [E<k>] [min3]   (modes run on the same lattices)
Every SAT model is replayed from the definitions (assertion) and dumped to plocal_<modes>_<corpus>.json."""
import sys, itertools, json
from pysat.solvers import Cadical153
from pysat.card import CardEnc
from tight_probe import lattices
from rstages import a_of
MODES = sys.argv[1].split(','); rest = sys.argv[2:]
FL = [a for a in rest if (a.startswith('min') and a[3:].isdigit()) or (a.startswith('E') and a[1:].isdigit())]; args = [a for a in rest if a not in FL]
EXN = next((int(a[1:]) for a in FL if a.startswith('E')), None); MINK = next((int(a[3:]) for a in FL if a.startswith('min')), 0); MIN3 = MINK > 0
MAXN = None
if 'maxn' in args: k = args.index('maxn'); MAXN = int(args[k + 1]); args = args[:k] + args[k + 2:]
MEAN = {'plocal': 'PairLocal fails (lambda(c0)=m pj >= c0, c0 <= lambda(c1) for another colour c1 <= m, lambda(m) != m)',
        'plocalM': 'MUTANT d2pM (lambda(c0)=m pj >= c0, lambda(m) != m; no condition on c1)',
        'plne': 'PairLocal fails with lambda(c1) != m (open half)',
        'esc': 'EscapeLow fails (no self-landing pj m with a colour c <= m, lambda(c) <= m)',
        'escM': 'MUTANT ClosedColour-in-W fails (no colour c <= lambda(c) = m in Z with c <= lambda(m))',
        'cx': 'CrossExists fails (no colours a != b with a v b in Z, b <= lambda(a), a <= lambda(b))',
        'cp': 'CrossPair fails (cross pair a, b with lambda(a v b) != a v b)',
        'caseB': 'CaseBEmpty fails (W and every colour row exits)',
        'caseAall': 'MUTANT case-emptiness relative fails (W and every colour row lands in Z)',
        'cpM': 'MUTANT OneCross fails (a v b in Z, b <= lambda(a), lambda(a v b) != a v b)'}
print(f'plocal_probe | per lattice: EXISTS F in W = PairSelf world without D_p | quantifier: exists F | modes ' +
      ' ; '.join(f'{md}: SAT = {MEAN[md]}' for md in MODES) + f' | corpus {args} maxn {MAXN} exactN {EXN} min colours {MINK}', flush=True)

def solve(L, MODE):
    n, le, h, bot, top = L.n, L.le, L.rank, L.bot, L.top
    NO = h[top] + 1; low = [x for x in range(n) if h[x] <= 2]; atoms = [x for x in range(n) if h[x] == 1]
    S = Cadical153(); V = {}
    def v(*k):
        if k not in V: V[k] = len(V) + 1
        return V[k]
    add = S.add_clause; f = lambda x, y, u: v('f', x, y, u); Z = lambda y: f(bot, y, bot)
    for x in low:                                                   # one-hot, monotone in y and in x (low rows)
        for y in range(n):
            ls = [f(x, y, u) for u in range(n)]; add(ls)
            for p, q in itertools.combinations(ls, 2): add([-p, -q])
        for y in range(n):
            for y2 in L.covers_up[y]:
                for u in range(n): add([-f(x, y, u)] + [f(x, y2, w) for w in range(n) if le[u][w]])
        for x2 in L.covers_up[x]:
            if h[x2] > 2: continue
            for y in range(n):
                for u in range(n): add([-f(x, y, u)] + [f(x2, y, w) for w in range(n) if le[u][w]])
    for y in range(n):                                              # a(bot) = bot: phi(y) < y or y = bot ... (no y <= phi(y))
        if y != bot:
            for u in range(n):
                if le[y][u]: add([-f(bot, y, u)])
        if h[y] > 2: add([-Z(y)])                                   # ZT
    add([Z(y) for y in range(n) if h[y] == 2])                      # n1
    col = {}
    for c in atoms:
        col[c] = v('col', c); add([-col[c], Z(c)]); add([-col[c]] + [f(bot, w, c) for w in range(n)])
        for w in range(n): add([-Z(c), -f(bot, w, c), col[c]])
    for z in low: add([-Z(z)] + [col[c] for c in atoms if not le[c][z]])   # unbounded
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
                t = v('t', x, j, p); ts.append(t); add([-t, it(x, j, p)]); add([-t] + [it(x, j - 1, z) for z in range(n) if h[z] > 2])
                for z in range(n):
                    if h[z] > 2: add([t, -it(x, j, p), -it(x, j - 1, z)])
            lam[x, p] = v('lam', x, p)
            for t in ts: add([-t, lam[x, p]])
            add([-lam[x, p]] + ts)
        if h[x] == 1:
            for p in low: add([-Z(x), -lam[x, p], Z(p), -f(bot, p, x)])              # NoFix
            for p in low: add([-col[x], -lam[x, p]] + [col[c] for c in atoms if le[c][p] and c != x])   # ColourGain at colour rows
            add([-col[x]] + [lam[x, p] for p in low])                                 # colour rows land
            for y in range(n):                                                        # Tb at colour rows
                if h[y] > 2:
                    for u in range(n):
                        if le[u][x]: add([-col[x], -f(x, y, u)])
        if h[x] == 2:                                                                 # pj(x) <-> Z(x) & two colours below
            pj = v('pj', x); prs = [(c, c2) for c, c2 in itertools.combinations(atoms, 2) if le[c][x] and le[c2][x]]
            add([-pj, Z(x)]); ts = []
            for (c, c2) in prs:
                t = v('pjw', x, c, c2); ts.append(t); add([-t, col[c]]); add([-t, col[c2]]); add([-Z(x), -col[c], -col[c2], pj])
            add([-pj] + ts)
            add([-pj] + [lam[x, p] for p in low])                                     # pair-join rows land
    add([v('pj', x) for x in low if h[x] == 2])                                       # non-thin
    if EXN is not None:                                                               # exact N: bot-descent t_N != bot, t_{N+1} = bot
        if EXN + 1 > NO: return None
        add([-it(bot, EXN, bot)]); add([it(bot, EXN + 1, bot)])
    pjs2 = [m_ for m_ in low if h[m_] == 2]
    if MODE in ('plocal', 'plocalM', 'plne'):
        sels = []
        for c0 in atoms:
            for c1 in atoms:
                if c1 == c0: continue
                for m_ in pjs2:
                    if not (le[c0][m_] and le[c1][m_]): continue
                    t = v('sel', c0, c1, m_); sels.append(t)
                    add([-t, col[c0]]); add([-t, col[c1]]); add([-t, v('pj', m_)]); add([-t, lam[c0, m_]]); add([-t, -lam[m_, m_]])
                    if MODE in ('plocal', 'plne'): add([-t] + [lam[c1, p] for p in low if le[c0][p]])
                    if MODE == 'plne': add([-t, -lam[c1, m_]])
        if not sels: S.delete(); return 'UNSAT'
        add(sels)
    if MODE in ('esc', 'escM'):
        for m_ in pjs2:
            for c in atoms:
                if not le[c][m_]: continue
                if MODE == 'esc':          # forbid: pj m self-lands, colour c <= m with lambda(c) <= m
                    for p in low:
                        if le[p][m_]: add([-v('pj', m_), -lam[m_, m_], -col[c], -lam[c, p]])
                else:                      # forbid: colour c, lambda(c) = m in Z, c <= lambda(m)
                    for p in low:
                        if le[c][p]: add([-col[c], -lam[c, m_], -Z(m_), -lam[m_, p]])
    if MODE in ('cx', 'cp', 'cpM'):
        sels = []
        for a_ in atoms:
            for b_ in atoms:
                if a_ == b_ or (MODE == 'cx' and b_ < a_): continue
                m_ = L.join[a_][b_] if hasattr(L, 'join') else min((z for z in range(n) if le[a_][z] and le[b_][z]), key=lambda z: h[z])
                if h[m_] != 2: continue
                if MODE == 'cx':
                    for p in low:
                        if not le[b_][p]: continue
                        for p2 in low:
                            if le[a_][p2]: add([-col[a_], -col[b_], -Z(m_), -lam[a_, p], -lam[b_, p2]])
                else:
                    t = v('csel', a_, b_); sels.append(t)
                    add([-t, col[a_]]); add([-t, col[b_]]); add([-t, Z(m_)]); add([-t, -lam[m_, m_]])
                    add([-t] + [lam[a_, p] for p in low if le[b_][p]])
                    if MODE == 'cp': add([-t] + [lam[b_, p] for p in low if le[a_][p]])
        if MODE != 'cx':
            if not sels: S.delete(); return 'UNSAT'
            add(sels)
    if MODE in ('caseB', 'caseAall'):
        for x in atoms:
            for p in low: add([-col[x], -lam[x, p], -Z(p)] if MODE == 'caseB' else [-col[x], -lam[x, p], Z(p)])
    if MIN3 and len(atoms) < MINK: S.delete(); return 'UNSAT'        # fewer atoms than colours required (run-5 crash fix)
    if MIN3:
        for cl in CardEnc.atleast([col[c] for c in atoms], bound=MINK, top_id=len(V)).clauses: add(cl)
    if not S.solve(): S.delete(); return 'UNSAT'
    mm = set(l for l in S.get_model() if l > 0); S.delete()
    F = [[(next(u for u in range(n) if V[('f', x, y, u)] in mm) if x in low else top) for y in range(n)] for x in range(n)]
    return F

def replay(L, F, MODE):
    n, le, h, bot, top = L.n, L.le, L.rank, L.bot, L.top
    phi = F[bot]; Zs = [y for y in range(n) if phi[y] == bot]
    def desc(x):
        z = top; s = []
        while z not in s: s.append(z); z = F[x][z]
        return s
    def lamf(x): return next((z for z in desc(x) if h[z] <= 2), None)
    cols = sorted({phi[w] for w in range(n) if h[phi[w]] == 1 and phi[w] in Zs})
    PJ = [z for z in Zs if h[z] == 2 and sum(1 for c in cols if le[c][z]) >= 2]
    hi = [y for y in range(n) if h[y] > 2]
    ok = a_of(L, F, bot) == bot and all(h[z] <= 2 for z in Zs) and any(h[z] == 2 for z in Zs) and h[top] >= 3
    ok = ok and not any(all(le[c][z] for c in cols) for z in Zs) and len(PJ) > 0
    ok = ok and all(lamf(x) is not None for x in cols + PJ)
    ok = ok and all(any(le[g][lamf(c)] and g != c for g in cols) for c in cols)
    ok = ok and all(not le[F[c][y]][c] for c in cols for y in hi)
    ok = ok and not any(h[q] == 1 and lamf(q) not in Zs and phi[lamf(q)] == q for q in Zs if lamf(q) is not None)
    if MODE in ('plocal', 'plocalM', 'plne'):
        ok = ok and any(lamf(c0) == m and lamf(m) != m and (MODE == 'plocalM' or le[c0][lamf(c1)]) and (MODE != 'plne' or lamf(c1) != m)
                        for c0 in cols for c1 in cols if c1 != c0 for m in PJ if le[c0][m] and le[c1][m])
    if MODE == 'esc':
        ok = ok and not any(lamf(m) == m and any(le[c][m] and le[lamf(c)][m] for c in cols) for m in PJ)
    if MODE == 'escM':
        ok = ok and not any(le[c][lamf(c)] and lamf(c) in Zs and le[c][lamf(lamf(c))] for c in cols)
    J = lambda a_, b_: min((z for z in range(n) if le[a_][z] and le[b_][z]), key=lambda z: h[z])
    cross = lambda a_, b_: a_ != b_ and J(a_, b_) in Zs and h[J(a_, b_)] == 2 and le[b_][lamf(a_)] and le[a_][lamf(b_)]
    if MODE == 'cx': ok = ok and not any(cross(a_, b_) for a_ in cols for b_ in cols)
    if MODE == 'cp': ok = ok and any(cross(a_, b_) and lamf(J(a_, b_)) != J(a_, b_) for a_ in cols for b_ in cols)
    if MODE == 'cpM': ok = ok and any(a_ != b_ and J(a_, b_) in Zs and h[J(a_, b_)] == 2 and le[b_][lamf(a_)] and lamf(J(a_, b_)) != J(a_, b_) for a_ in cols for b_ in cols)
    if MODE == 'caseB': ok = ok and all(lamf(c) not in Zs for c in cols)
    if MODE == 'caseAall': ok = ok and all(lamf(c) in Zs for c in cols)
    d = [t for t in desc(bot) if t != bot]; N = desc(bot).index(d[-1]) if d else None
    if EXN is not None: ok = ok and N == EXN
    if MIN3: ok = ok and len(cols) >= MINK
    return ok, dict(cols=cols, PJ=PJ, N=N, branch=('a' if d and h[d[-1]] == 2 else 'atom'))

tot = {md: {'SAT': 0, 'UNSAT': 0} for md in MODES}; dump = []; k = 0
for L in lattices(args):
    if MAXN is not None and L.n > MAXN: continue
    if L.rank[L.top] < 3: continue
    k += 1; line = []
    for md in MODES:
        r = solve(L, md)
        if r is None: line.append(f'{md}: n/a'); continue
        if r == 'UNSAT': tot[md]['UNSAT'] += 1; line.append(f'{md}: UNSAT'); continue
        ok, info = replay(L, r, md); assert ok, f'SAT/replay mismatch {md}'
        tot[md]['SAT'] += 1; dump.append(dict(mode=md, sets=L.S, F=r, **info))
        line.append(f'{md}: SAT (colours {info["cols"]}, pjs {info["PJ"]}, N {info["N"]}, d {info["branch"]})')
    print(f'  lattice {k} n={L.n} h={L.height}: ' + ' | '.join(line), flush=True)
print('TOTAL', MODES, args, 'exactN', EXN, tot, flush=True)
json.dump(dump, open(f'plocal_{"-".join(MODES)}_{"_".join(args)}{"_E%d" % EXN if EXN is not None else ""}.json', 'w'))
