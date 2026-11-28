"""Brief run 28, briefer's tester (exact, per lattice).  Base world W = PairSelf's world without D_p (as brief302
plocal_probe.py, from which the base encoding is copied):
  rows of height <= 2 are variables (one-hot, monotone in both arguments); rows of height >= 3 are the constant top;
  a(bot) = bot; ZT; n1; h(top) >= 3; colours = atoms c of Z with c = phi(w) for some w (exact); colours unbounded in Z;
  some pair-join; colour rows land, have ColourGain and Tb; pair-join rows land; NoFix.
Notation: C(m) = colours below m; C'(m) = atoms below m that are phi(X) for some HIGH X (exact, variable cp(c)).
Modes (each is EXISTS F on the lattice; SAT = the named statement FAILS on this lattice; every conclusion is
'lambda(m) <= m', the negation of D_p at m, so SAT means D_p holds at m):
  plu    PairLocalU fails: colour c0, pair-join m >= c0 with lambda(c0) = m, EVERY colour c <= m has c0 <= lambda(c),
         and lambda(m) not <= m
  pls    PairLocalS fails: as plu with 'every c in C'(m)' in place of 'every colour c <= m' (stronger statement)
  ns     NSL fails: colour c0 with lambda(c0) = m pair-join >= c0, a colour t in C'(m), t != c0, with c0 <= lambda(t)
         and t not <= lambda(t), and lambda(m) not <= m
  nsC    as ns with t any colour <= m (t in C(m))
  pl     MUTANT = PairLocal (refuted, bank s302_pairlocal_h5): colours c0 != c1 <= m, lambda(c0) = m pair-join,
         c0 <= lambda(c1), lambda(m) not <= m
  kself  THEOREM CHECK (kSelf_absurd's W form): pair-join m, a colour c0 <= m with lambda(c0) = m, every c in C'(m)
         has lambda(c) = m, and lambda(m) != m.  Expected UNSAT everywhere (an encoding check, not evidence)
Flags: k<d> (k3, k4, k5, ...): the instance pair-join m has >= d colours below it (room |C(m)|); kp3: >= 3 atoms of C'(m)
       which are colours; maxn N; E<k> exact N.
Usage: python3 plu_probe.py MODE1,MODE2 corpus... [flags]   (corpus as tight_probe.lattices, plus 'planted H M SEED CNT k')
Every SAT model is replayed from the definitions (assertion) and dumped to plu_<modes>_<corpus>_<flags>.json."""
import sys, itertools, json
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation'); sys.path.insert(0, '/home/user/mordor/experiments/separation')
from pysat.solvers import Cadical153
from rstages import a_of
from my_lat import lattices
MODES = sys.argv[1].split(','); rest = sys.argv[2:]
FLAGS = {a for a in rest if (a.startswith('k') and a[1:].isdigit()) or a == 'kp3' or (a.startswith('E') and a[1:].isdigit())}; args = [a for a in rest if a not in FLAGS]
EXN = next((int(a[1:]) for a in FLAGS if a.startswith('E')), None)
KC = max([int(a[1:]) for a in FLAGS if a.startswith('k') and a[1:].isdigit()] or [0]); KP = 3 if 'kp3' in FLAGS else 0
MAXN = None
if 'maxn' in args: k = args.index('maxn'); MAXN = int(args[k + 1]); args = args[:k] + args[k + 2:]
MEAN = {'plu': 'PairLocalU fails (lambda(c0)=m pj >= c0, c0 <= lambda(c) for EVERY colour c <= m, lambda(m) not <= m)',
        'pls': "PairLocalS fails (lambda(c0)=m pj >= c0, c0 <= lambda(c) for every c in C'(m), lambda(m) not <= m)",
        'ns': "NSL fails (lambda(c0)=m pj >= c0, t in C'(m)\\{c0}, c0 <= lambda(t), t not <= lambda(t), lambda(m) not <= m)",
        'nsC': 'NSL-C fails (as ns, t any colour <= m)',
        'pl': 'MUTANT PairLocal fails (lambda(c0)=m pj >= c0, c0 <= lambda(c1) for ONE other colour c1 <= m, lambda(m) not <= m)',
        'helly': 'Helly2 fails (the colour sets K(c) of all colour rows pairwise intersect, and no colour lies in every K(c))',
        'tri': 'Triangle exists (three colour rows whose landing colour sets pairwise intersect with no common colour) -- room check for Helly2',
        'hellyM': 'MUTANT (refuted relative UnivCol-in-W, 81 stored W-models): no colour lies in every K(c)',
        'kself': "kSelf CHECK fails (lambda(c0)=m pj, lambda(c)=m for every c in C'(m), lambda(m) != m) -- theorem, expect UNSAT"}
print(f'plu_probe | per lattice: EXISTS F in W (PairSelf world without D_p) | ' + ' ; '.join(f'{md}: SAT = {MEAN[md]}' for md in MODES)
      + f' | corpus {args} maxn {MAXN} exactN {EXN} |C(m)|>={KC} |C\'(m)|>={KP}', flush=True)

def solve(L, MODE):
    n, le, h, bot, top = L.n, L.le, L.rank, L.bot, L.top
    NO = h[top] + 1; low = [x for x in range(n) if h[x] <= 2]; atoms = [x for x in range(n) if h[x] == 1]
    hi = [y for y in range(n) if h[y] > 2]
    S = Cadical153(); V = {}
    def v(*k):
        if k not in V: V[k] = len(V) + 1
        return V[k]
    add = S.add_clause; f = lambda x, y, u: v('f', x, y, u); Z = lambda y: f(bot, y, bot)
    for x in low:
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
    for y in range(n):
        if y != bot:
            for u in range(n):
                if le[y][u]: add([-f(bot, y, u)])
        if h[y] > 2: add([-Z(y)])
    add([Z(y) for y in range(n) if h[y] == 2])
    col = {}; cp = {}
    for c in atoms:
        col[c] = v('col', c); add([-col[c], Z(c)]); add([-col[c]] + [f(bot, w, c) for w in range(n)])
        for w in range(n): add([-Z(c), -f(bot, w, c), col[c]])
        cp[c] = v('cp', c); add([-cp[c]] + [f(bot, X, c) for X in hi])        # cp(c) <-> c = phi(X) for a high X
        for X in hi: add([-f(bot, X, c), cp[c]])
    for z in low: add([-Z(z)] + [col[c] for c in atoms if not le[c][z]])
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
            for p in low: add([-Z(x), -lam[x, p], Z(p), -f(bot, p, x)])
            for p in low: add([-col[x], -lam[x, p]] + [col[c] for c in atoms if le[c][p] and c != x])
            add([-col[x]] + [lam[x, p] for p in low])
            for y in hi:
                for u in range(n):
                    if le[u][x]: add([-col[x], -f(x, y, u)])
        if h[x] == 2:
            pj = v('pj', x); prs = [(c, c2) for c, c2 in itertools.combinations(atoms, 2) if le[c][x] and le[c2][x]]
            add([-pj, Z(x)]); ts = []
            for (c, c2) in prs:
                t = v('pjw', x, c, c2); ts.append(t); add([-t, col[c]]); add([-t, col[c2]]); add([-Z(x), -col[c], -col[c2], pj])
            add([-pj] + ts)
            add([-pj] + [lam[x, p] for p in low])
    add([v('pj', x) for x in low if h[x] == 2])
    if EXN is not None:
        if EXN + 1 > NO: return None
        add([-it(bot, EXN, bot)]); add([it(bot, EXN + 1, bot)])
    def room(sel, m_):       # sel -> m has >= KC colours below it and >= KP C'-colours below it
        for K_, pred in ((KC, lambda c: [col[c]]), (KP, lambda c: [col[c], cp[c]])):
            if K_ == 0: continue
            ab = [c for c in atoms if le[c][m_]]
            if len(ab) < K_: add([-sel]); continue
            tr = []
            for T in itertools.combinations(ab, K_):
                g = v('room', m_, K_, T); tr.append(g)
                for c in T:
                    for lit in pred(c): add([-g, lit])
            add([-sel] + tr)
    if MODE in ('helly', 'hellyM', 'tri'):
        kin = {}
        for c in atoms:
            for g in atoms:
                kv = v('kin', c, g); kin[c, g] = kv; ups = [lam[c, p] for p in low if le[g][p]]
                add([-kv] + ups)
                for u_ in ups: add([-u_, kv])
        if MODE == 'helly':
            for c, c2 in itertools.combinations(atoms, 2):
                ws = []
                for g in atoms:
                    w_ = v('hw', c, c2, g); ws.append(w_); add([-w_, col[g]]); add([-w_, kin[c, g]]); add([-w_, kin[c2, g]])
                add([-col[c], -col[c2]] + ws)
        if MODE == 'tri':
            sels = []
            for T in itertools.combinations(atoms, 3):
                t3 = v('tri', T); sels.append(t3)
                for c in T: add([-t3, col[c]])
                for c, c2 in itertools.combinations(T, 2):
                    ws = []
                    for g in atoms:
                        w_ = v('tw', T, c, c2, g); ws.append(w_); add([-w_, col[g]]); add([-w_, kin[c, g]]); add([-w_, kin[c2, g]])
                    add([-t3] + ws)
                for g in atoms: add([-t3, -col[g]] + [-kin[c, g] for c in T])
            if not sels: S.delete(); return 'UNSAT'
            add(sels)
        for g in (atoms if MODE != 'tri' else []):
            nus = []
            for c in atoms:
                nu = v('nu', g, c); nus.append(nu); add([-nu, col[c]]); add([-nu, -kin[c, g]])
            add([-col[g]] + nus)
        if not S.solve(): S.delete(); return 'UNSAT'
        mm = set(l for l in S.get_model() if l > 0); S.delete()
        return [[(next(u for u in range(n) if V[('f', x, y, u)] in mm) if x in low else top) for y in range(n)] for x in range(n)]
    pjs2 = [m_ for m_ in low if h[m_] == 2]
    notle = lambda m_: [lam[m_, p] for p in low if not le[p][m_]]       # lambda(m) not <= m
    sels = []
    for m_ in pjs2:
        for c0 in atoms:
            if not le[c0][m_]: continue
            others = [c for c in atoms if le[c][m_] and c != c0]
            up0 = lambda c: [lam[c, p] for p in low if le[c0][p]]          # c0 <= lambda(c)
            if MODE in ('plu', 'pls', 'kself'):
                t = v('sel', MODE, c0, m_); sels.append(t)
                add([-t, col[c0]]); add([-t, v('pj', m_)]); add([-t, lam[c0, m_]])
                if MODE == 'kself': add([-t, -lam[m_, m_]])
                else: add([-t] + notle(m_))
                for c in others:
                    if MODE == 'plu': add([-t, -col[c]] + up0(c))
                    if MODE == 'pls': add([-t, -col[c], -cp[c]] + up0(c))
                    if MODE == 'kself': add([-t, -col[c], -cp[c], lam[c, m_]])
                room(t, m_)
            else:
                for c1 in others:
                    t = v('sel', MODE, c0, c1, m_); sels.append(t)
                    add([-t, col[c0]]); add([-t, col[c1]]); add([-t, v('pj', m_)]); add([-t, lam[c0, m_]]); add([-t] + notle(m_))
                    if MODE == 'pl': add([-t] + up0(c1))
                    else:   # ns, nsC: c0 <= lambda(c1), c1 not <= lambda(c1)
                        add([-t] + [lam[c1, p] for p in low if le[c0][p] and not le[c1][p]])
                        if MODE == 'ns': add([-t, cp[c1]])
                    room(t, m_)
    if not sels: S.delete(); return 'UNSAT'
    add(sels)
    if not S.solve(): S.delete(); return 'UNSAT'
    mm = set(l for l in S.get_model() if l > 0); S.delete()
    return [[(next(u for u in range(n) if V[('f', x, y, u)] in mm) if x in low else top) for y in range(n)] for x in range(n)]

def replay(L, F, MODE):
    n, le, h, bot, top = L.n, L.le, L.rank, L.bot, L.top
    phi = F[bot]; Zs = [y for y in range(n) if phi[y] == bot]; hi = [y for y in range(n) if h[y] > 2]
    def desc(x):
        z = top; s = []
        while z not in s: s.append(z); z = F[x][z]
        return s
    def lamf(x): return next((z for z in desc(x) if h[z] <= 2), None)
    cols = sorted({phi[w] for w in range(n) if h[phi[w]] == 1 and phi[w] in Zs})
    Cpr = lambda m: [c for c in cols if le[c][m] and any(phi[X] == c for X in hi)]
    PJ = [z for z in Zs if h[z] == 2 and sum(1 for c in cols if le[c][z]) >= 2]
    mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for x2 in range(n) if le[x][x2] for y in range(n) for y2 in range(n) if le[y][y2])
    ok = mono and a_of(L, F, bot) == bot and all(h[z] <= 2 for z in Zs) and any(h[z] == 2 for z in Zs) and h[top] >= 3
    ok = ok and not any(all(le[c][z] for c in cols) for z in Zs) and len(PJ) > 0
    ok = ok and all(lamf(x) is not None for x in cols + PJ)
    ok = ok and all(any(le[g][lamf(c)] and g != c for g in cols) for c in cols)
    ok = ok and all(not le[F[c][y]][c] for c in cols for y in hi)
    ok = ok and not any(h[q] == 1 and lamf(q) not in Zs and phi[lamf(q)] == q for q in Zs if lamf(q) is not None)
    inst = []
    if MODE == 'tri':
        Kd = {c: set(c2 for c2 in cols if le[c2][lamf(c)]) for c in cols}
        tris = [T for T in itertools.combinations(cols, 3) if all(Kd[a_] & Kd[b_] for a_, b_ in itertools.combinations(T, 2)) and not (Kd[T[0]] & Kd[T[1]] & Kd[T[2]])]
        ok = ok and len(tris) > 0
        d = [t for t in desc(bot) if t != bot]; N = desc(bot).index(d[-1]) if d else None
        return ok, dict(cols=cols, PJ=PJ, N=N, branch=('a' if d and h[d[-1]] == 2 else 'atom'), inst=[('tri', tris[:1], {c: sorted(Kd[c]) for c in tris[0]} if tris else None)], Cm=0, Cpm=0)
    if MODE in ('helly', 'hellyM'):
        Ks = [set(c2 for c2 in cols if le[c2][lamf(c)]) for c in cols]
        pw = all(a_ & b_ for a_, b_ in itertools.combinations(Ks, 2))
        ok = ok and not set.intersection(*Ks) and (MODE == 'hellyM' or pw)
        d = [t for t in desc(bot) if t != bot]; N = desc(bot).index(d[-1]) if d else None
        if EXN is not None: ok = ok and N == EXN
        return ok, dict(cols=cols, PJ=PJ, N=N, branch=('a' if d and h[d[-1]] == 2 else 'atom'), inst=[('K', [sorted(k_) for k_ in Ks], 'pairwise', pw)], Cm=0, Cpm=0)
    for m in PJ:
        Cm = [c for c in cols if le[c][m]]
        if len(Cm) < KC or len([c for c in Cpr(m)]) < KP: continue
        for c0 in Cm:
            if lamf(c0) != m: continue
            oth = [c for c in Cm if c != c0]
            if MODE == 'kself': hyp = lamf(m) != m and all(lamf(c) == m for c in Cpr(m) if c != c0)
            else:
                dp = not le[lamf(m)][m]
                if MODE == 'plu': hyp = dp and all(le[c0][lamf(c)] for c in oth)
                if MODE == 'pls': hyp = dp and all(le[c0][lamf(c)] for c in Cpr(m) if c != c0)
                if MODE == 'pl': hyp = dp and any(le[c0][lamf(c)] for c in oth)
                if MODE in ('ns', 'nsC'): hyp = dp and any(le[c0][lamf(t)] and not le[t][lamf(t)] for t in (Cpr(m) if MODE == 'ns' else Cm) if t != c0)
            if hyp: inst.append((c0, m, len(Cm), len(Cpr(m))))
    ok = ok and len(inst) > 0
    d = [t for t in desc(bot) if t != bot]; N = desc(bot).index(d[-1]) if d else None
    if EXN is not None: ok = ok and N == EXN
    return ok, dict(cols=cols, PJ=PJ, N=N, branch=('a' if d and h[d[-1]] == 2 else 'atom'), inst=inst,
                    Cm=max(i[2] for i in inst) if inst else 0, Cpm=max(i[3] for i in inst) if inst else 0)

tot = {md: {'SAT': 0, 'UNSAT': 0} for md in MODES}; dump = []; k = 0; maxC = {md: 0 for md in MODES}
for L in lattices(args):
    if MAXN is not None and L.n > MAXN: continue
    if L.rank[L.top] < 3: continue
    k += 1; line = []
    roomL = max((sum(1 for a in range(L.n) if L.rank[a] == 1 and L.le[a][z]) for z in range(L.n) if L.rank[z] == 2), default=0)
    for md in MODES:
        r = solve(L, md)
        if r is None: line.append(f'{md}: n/a'); continue
        if r == 'UNSAT': tot[md]['UNSAT'] += 1; line.append(f'{md}: UNSAT'); continue
        ok, info = replay(L, r, md); assert ok, f'SAT/replay mismatch {md}'
        tot[md]['SAT'] += 1; maxC[md] = max(maxC[md], info['Cm']); dump.append(dict(mode=md, sets=L.S, F=r, **info))
        line.append(f'{md}: SAT (|A| {len(info["cols"])}, inst (c0,m,|C(m)|,|C\'(m)|) {info["inst"][:2]}, N {info["N"]}, d {info["branch"]})')
    print(f'  lattice {k} n={L.n} h={L.height} atoms-under-a-height-2-element {roomL}: ' + ' | '.join(line), flush=True)
print('TOTAL', MODES, args, sorted(FLAGS), tot, 'max |C(m)| at SAT instances', maxC, flush=True)
tag = "_".join(a.replace('/', '').replace('.json', '')[-24:] for a in args)
json.dump(dump, open(f'plu_{"-".join(MODES)}_{tag}_{"_".join(sorted(FLAGS))}.json', 'w'))
