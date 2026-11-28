"""Brief run 27, lead probe: BreakDichotomy (BD), exact per lattice.
World W = PairSelf's world without D_p (as in plocal_probe.py): rows of height <= 2 variables, higher rows the constant
top; a(bot) = bot; ZT; n1; h(top) >= 3; colours exact; unbounded; some pair-join; colour rows land, ColourGain, Tb;
pair-join rows land; NoFix.
A *break* of the colourStair staircase of colour rows x, y (value row bot) at column l+1: with v = desc(x), w = desc(y),
kappa(j) = first k with v_j /\\ w_k low, B_l = v_l /\\ w_(kappa(l)-1) (high), e_l = phi(B_l), corner A = v_(l+1) /\\
w_(kappa(l+1)), B = v_(l+1) /\\ w_(kappa(l+1)-1) (high), e = phi(B), v_(l+1) high (so l+1 < i(x)):
  some colour of K(y) = C(lambda(y)) lies below e_l, and no colour of K(y) lies below e.   (Any such l, not only the first.)
Modes (EXISTS F, colour rows x != y, index l; SAT = the statement FAILS on this lattice):
  bd     BD fails: a break at A with lambda(A) not <= A and no colour u <= A with lambda(u) = A
  bdM1   MUTANT BreakCornerSelf (brief300 D1 test form; refuted by 11 stored models): a break with lambda(A) not <= A
  bdM2   MUTANT 'break => lambda(u) = A for a colour u <= A' (refuted by the Case B models of run 3): a break with no
         colour u <= A with lambda(u) = A
  bdB    (NOT RUN by the briefer; owed) BD-B fails: W, every colour row exits (Case B), and a break at A with
         lambda(A) not <= A.  Mutant: bdM1 (same without Case B; SAT on stored lattices).
Usage: python3 bd_probe.py MODE1,MODE2 corpus... [maxn N]    Every SAT model is replayed (assertion) and dumped."""
import sys, itertools, json
from pysat.solvers import Cadical153
from tight_probe import lattices
from rstages import a_of
MODES = sys.argv[1].split(','); args = sys.argv[2:]
MAXN = None
if 'maxn' in args: k = args.index('maxn'); MAXN = int(args[k + 1]); args = args[:k] + args[k + 2:]
MEAN = {'bd': 'BD fails (break at A, lambda(A) not <= A, no colour u <= A with lambda(u) = A)',
        'bdM1': 'MUTANT BreakCornerSelf fails (break at A with lambda(A) not <= A)',
        'bdM2': 'MUTANT fails (break at A with no colour u <= A, lambda(u) = A)',
        'bdB': 'BD-B fails (Case B: every colour row exits; break at A with lambda(A) not <= A)'}
print('bd_probe | per lattice: EXISTS F in W (PairSelf world without D_p), colour rows x != y, column l | ' +
      ' ; '.join(f'{md}: SAT = {MEAN[md]}' for md in MODES) + f' | corpus {args} maxn {MAXN}', flush=True)

def solve(L, MODE):
    n, le, h, bot, top = L.n, L.le, L.rank, L.bot, L.top; meet = L.meet
    NO = h[top] + 1; low = [x for x in range(n) if h[x] <= 2]; atoms = [x for x in range(n) if h[x] == 1]
    high = [z for z in range(n) if h[z] > 2]
    S = Cadical153(); V = {}
    def v(*k):
        if k not in V: V[k] = len(V) + 1
        return V[k]
    add = S.add_clause; f = lambda x, y, u: v('f', x, y, u); Z = lambda y: f(bot, y, bot)
    def onehot(name, dom):
        ls = [v(name, z) for z in dom]; add(ls)
        for p, q in itertools.combinations(ls, 2): add([-p, -q])
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
    col = {}
    for c in atoms:
        col[c] = v('col', c); add([-col[c], Z(c)]); add([-col[c]] + [f(bot, w, c) for w in range(n)])
        for w in range(n): add([-Z(c), -f(bot, w, c), col[c]])
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
                t = v('t', x, j, p); ts.append(t); add([-t, it(x, j, p)]); add([-t] + [it(x, j - 1, z) for z in high])
                for z in high: add([t, -it(x, j, p), -it(x, j - 1, z)])
            lam[x, p] = v('lam', x, p)
            for t in ts: add([-t, lam[x, p]])
            add([-lam[x, p]] + ts)
        if h[x] == 1:
            for p in low: add([-Z(x), -lam[x, p], Z(p), -f(bot, p, x)])
            for p in low: add([-col[x], -lam[x, p]] + [col[c] for c in atoms if le[c][p] and c != x])
            add([-col[x]] + [lam[x, p] for p in low])
            for y in high:
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
    # ---- the break: choices x, y (colour atoms), l, k1 = kappa(l), k2 = kappa(l+1), elements P = v_l, P2 = v_(l+1),
    # Q1 = w_(k1-1), Q1b = w_k1, Q2 = w_(k2-1), Q2b = w_k2
    if len(atoms) < 2: return 'UNSAT'
    onehot('sx', atoms); onehot('sy', atoms)
    for c in atoms: add([-v('sx', c), col[c]]); add([-v('sy', c), col[c]]); add([-v('sx', c), -v('sy', c)])
    L_ = list(range(NO)); K_ = list(range(1, NO + 1))
    onehot('sl', L_); onehot('sk1', K_); onehot('sk2', K_)
    for nm in ('P', 'P2', 'Q1', 'Q1b', 'Q2', 'Q2b'): onehot(nm, range(n))
    for x in atoms:
        for l in L_:
            for z in range(n):
                add([-v('sx', x), -v('sl', l), -v('P', z), it(x, l, z)])
                add([-v('sx', x), -v('sl', l), -v('P2', z), it(x, l + 1, z)])
    for y in atoms:
        for k in K_:
            for z in range(n):
                add([-v('sy', y), -v('sk1', k), -v('Q1', z), it(y, k - 1, z)]); add([-v('sy', y), -v('sk1', k), -v('Q1b', z), it(y, k, z)])
                add([-v('sy', y), -v('sk2', k), -v('Q2', z), it(y, k - 1, z)]); add([-v('sy', y), -v('sk2', k), -v('Q2b', z), it(y, k, z)])
    for z in low: add([-v('P2', z)])                                   # v_(l+1) high: column l+1 is a step of the walk
    for z1 in range(n):
        for z2 in range(n):
            mz = meet[z1][z2]
            if h[mz] <= 2: add([-v('P', z1), -v('Q1', z2)]); add([-v('P2', z1), -v('Q2', z2)])   # B_l, B high
            else: add([-v('P', z1), -v('Q1b', z2)]); add([-v('P2', z1), -v('Q2b', z2)])          # corners low
    # e_l = phi(B_l), e = phi(B), A = corner, lambda(y)
    onehot('E1', range(n)); onehot('E2', range(n)); onehot('A', range(n)); onehot('LY', low)
    for z1 in range(n):
        for z2 in range(n):
            mz = meet[z1][z2]
            for u in range(n):
                add([-v('P', z1), -v('Q1', z2), -f(bot, mz, u), v('E1', u)])
                add([-v('P2', z1), -v('Q2', z2), -f(bot, mz, u), v('E2', u)])
            add([-v('P2', z1), -v('Q2b', z2), v('A', mz)])
    for y in atoms:
        for p in low: add([-v('sy', y), -lam[y, p], v('LY', p)])
    # carried at l: some colour c <= e_l and c <= lambda(y); not carried at l+1
    cs = []
    for c in atoms:
        t = v('car', c); cs.append(t); add([-t, col[c]])
        add([-t] + [v('E1', u) for u in range(n) if le[c][u]]); add([-t] + [v('LY', p) for p in low if le[c][p]])
        for u in range(n):
            if not le[c][u]: continue
            for p in low:
                if le[c][p]: add([-col[c], -v('E2', u), -v('LY', p)])
    add(cs)
    # the conclusion of BD, negated per mode
    for z in low:
        if MODE in ('bd', 'bdM1', 'bdB'):
            for p in low:
                if le[p][z]: add([-v('A', z), -lam[z, p]])                     # lambda(A) not <= A
        if MODE in ('bd', 'bdM2'):
            for u in atoms:
                if le[u][z]: add([-v('A', z), -col[u], -lam[u, z]])          # no colour u <= A lands at A
    for z in high: add([-v('A', z)])
    if MODE == 'bdB':                                                     # Case B: every colour row exits
        for c in atoms:
            for p in low: add([-col[c], -lam[c, p], -Z(p)])
    if not S.solve(): S.delete(); return 'UNSAT'
    mm = set(l for l in S.get_model() if l > 0)
    F = [[(next(u for u in range(n) if V[('f', x, y, u)] in mm) if x in low else top) for y in range(n)] for x in range(n)]
    pick = lambda nm, dom: next(z for z in dom if V[(nm, z)] in mm)
    choice = dict(x=pick('sx', atoms), y=pick('sy', atoms), l=pick('sl', L_), A=pick('A', range(n)))
    S.delete(); return F, choice

def replay(L, F, ch, MODE):
    n, le, h, bot, top = L.n, L.le, L.rank, L.bot, L.top; meet = L.meet
    phi = F[bot]; Zs = [y for y in range(n) if phi[y] == bot]
    def desc(x):
        z = top; s = []
        while z not in s: s.append(z); z = F[x][z]
        return s
    def u_(x, j):
        z = top
        for _ in range(j): z = F[x][z]
        return z
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
    x, y, l = ch['x'], ch['y'], ch['l']
    ok = ok and x in cols and y in cols and x != y
    kap = lambda j: next(k for k in range(1, 4 * n) if h[meet[u_(x, j)][u_(y, k)]] <= 2)
    K = [c for c in cols if le[c][lamf(y)]]
    ok = ok and h[u_(x, l + 1)] > 2
    k1, k2 = kap(l), kap(l + 1)
    e1 = phi[meet[u_(x, l)][u_(y, k1 - 1)]]; e2 = phi[meet[u_(x, l + 1)][u_(y, k2 - 1)]]; A = meet[u_(x, l + 1)][u_(y, k2)]
    ok = ok and A == ch['A'] and any(le[c][e1] for c in K) and not any(le[c][e2] for c in K)
    if MODE in ('bd', 'bdM1', 'bdB'): ok = ok and not le[lamf(A)][A]
    if MODE == 'bdB': ok = ok and all(lamf(c) not in Zs for c in cols)
    if MODE in ('bd', 'bdM2'): ok = ok and not any(lamf(u) == A for u in cols if le[u][A])
    d = [t for t in desc(bot) if t != bot]; N = desc(bot).index(d[-1]) if d else None
    return ok, dict(cols=cols, PJ=PJ, N=N, x=x, y=y, l=l, A=A, AinZ=A in Zs, lamA=lamf(A))

tot = {md: {'SAT': 0, 'UNSAT': 0} for md in MODES}; dump = []; k = 0
for L in lattices(args):
    if MAXN is not None and L.n > MAXN: continue
    if L.rank[L.top] < 3: continue
    k += 1; line = []
    for md in MODES:
        r = solve(L, md)
        if r == 'UNSAT': tot[md]['UNSAT'] += 1; line.append(f'{md}: UNSAT'); continue
        F, ch = r; ok, info = replay(L, F, ch, md); assert ok, f'SAT/replay mismatch {md} {info}'
        tot[md]['SAT'] += 1; dump.append(dict(mode=md, sets=L.S, F=F, **info))
        line.append(f'{md}: SAT (colours {info["cols"]}, x {info["x"]} y {info["y"]} l {info["l"]} A {info["A"]} inZ {info["AinZ"]} lam(A) {info["lamA"]}, N {info["N"]})')
    print(f'  lattice {k} n={L.n} h={L.height}: ' + ' | '.join(line), flush=True)
print('TOTAL', MODES, args, tot, flush=True)
json.dump(dump, open(f'bd_{"-".join(MODES)}_{"_".join(args)}.json', 'w'))
