"""Brief run 18, lead probe "StairTb": CertAtom in the world Stair, where Tb at an atom row q is imposed ONLY at the
staircase-boundary columns of the pairs (q, x), x in Z, q <= x:
      w = u ^ v  with  u in desc(q), v in desc(x), h(w) >= 3  and  h(u ^ succ_x(v)) <= 2      (succ_x(v) = F(x, v)).
These are exactly the columns G(l, kappa(l) - 1) the CornerColour proof uses (one per index l of row q's descent).
Rest of the world as W0^2: a(bot) = bot, ZT, n1, h(top) >= 3, every row of Z lands (Ta), lambda(m) not <= m on M2.
Theorem (paper, brief §4): in branch b/g with N = 1 CertAtom holds in Stair.  Elsewhere: conjecture.

QUANTIFIER: for each lattice, EXISTS F in Stair with NO mu-fixed atom (lambda(q) = p not in Z and F(bot, p) = q).
SAT = StairTb fails on this lattice (the model is saved and re-checked in Python from the definitions).
UNSAT = every Stair model on this lattice has a mu-fixed atom.
  python3 stair_probe.py nofix [maxn N] [E1] CORPUS [+ CORPUS ...]      (E1: exact N = 1)"""
import sys, os, json, itertools, collections, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation'); sys.path.insert(0, '/home/user/mordor/experiments/separation')
sys.path.insert(0, HERE); sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291')
from pysat.solvers import Cadical153
from tight_probe import lattices
from world import W

MODE = sys.argv[1]; assert MODE == 'nofix'
rest = sys.argv[2:]; MAXN = None
NEX = next((int(a[1:]) for a in rest if a in ('E1', 'E2', 'E3', 'E4', 'E5', 'E6')), 0); E1 = NEX == 1   # exact N
rest = [a for a in rest if a not in ('E1', 'E2', 'E3', 'E4', 'E5', 'E6')]
if rest[:1] == ['maxn']: MAXN = int(rest[1]); rest = rest[2:]
corpora = [[]]
for a in rest:
    if a == '+': corpora.append([])
    else: corpora[-1].append(a)
print(__doc__.split('\n\n')[1])
print(f'stair_probe {MODE} exactN={NEX or None} maxn={MAXN} corpora={corpora}', flush=True)


def stair_world(w):
    """Stair world from the definitions (see the docstring)."""
    if not w.base(): return False
    for x in w.Z:
        if w.lam(x) is None: return False
        if x != w.bot and w.h[x] == 2 and w.le[w.lam(x)][x]: return False
    for q in w.atoms:
        for x in w.Z:
            if not w.le[q][x]: continue
            for u in w.desc(q):
                for v in w.desc(x):
                    g = w.L.meet[u][v]
                    if w.h[g] >= 3 and w.h[w.L.meet[u][w.F[x][v]]] <= 2 and w.le[w.F[q][g]][q]: return False
    return True

def encode(L):
    n, le, h, bot, top = L.n, L.le, L.rank, L.bot, L.top
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
    for y in range(n):                                   # a(bot) = bot
        if y == bot: continue
        for u in range(n):
            if le[y][u]: add([-f(bot, y, u)])
    for y in range(n):
        if h[y] > 2: add([-Z(y)])                        # ZT
    add([Z(y) for y in range(n) if h[y] == 2])           # n1
    hi = [y for y in range(n) if h[y] > 2]
    for x in low:                                        # Ta at rows of Z
        if x == bot: continue
        for y in hi:
            for u in range(n):
                if le[y][u]: add([-Z(x), -f(x, y, u)])
    it = lambda x, j, z: v('it', x, j, z)
    for x in low:
        for z in range(n): add([it(x, 0, z)] if z == top else [-it(x, 0, z)])
        for j in range(NO):
            for z in range(n):
                for u in range(n): add([-it(x, j, z), -f(x, z, u), it(x, j + 1, u)])
            for z, z2 in itertools.combinations(range(n), 2): add([-it(x, j + 1, z), -it(x, j + 1, z2)])
    lam = {}
    for x in low:                                        # lam(x, p): p is the first element of height <= 2 on desc(x)
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
    for x in low:                                        # every row of Z lands within NO steps (implied by Ta; explicit)
        if x != bot: add([-Z(x)] + [lam[x, p] for p in low])
    for m in low:                                        # lambda(m) not <= m on M2
        if h[m] == 2:
            for p in low:
                if le[p][m]: add([-Z(m), -lam[m, p]])
    D = lambda x, w: v('D', x, w)
    for x in low:
        for j in range(NO + 1):
            for w in range(n): add([-it(x, j, w), D(x, w)])
    for q in low:                                        # Tb at atom rows only at staircase-boundary columns
        if h[q] != 1: continue
        for x in low:
            if not le[q][x]: continue
            for u1 in range(n):
                for u2 in range(n):
                    w = L.meet[u1][u2]
                    if h[w] <= 2: continue
                    for u3 in range(n):
                        if not le[u3][u2] or h[L.meet[u1][u3]] > 2: continue
                        for u in range(n):
                            if le[u][q]: add([-Z(q), -Z(x), -D(q, u1), -D(x, u2), -f(x, u2, u3), -f(q, w, u)])
    if NEX:                                              # exact N: t_N != bot = t_(N+1)
        if NEX + 1 > NO: return None, None, None
        add([-it(bot, NEX, bot)]); add([it(bot, NEX + 1, bot)])
    for q in low:                                        # NoFix
        if h[q] != 1: continue
        for p in low: add([-Z(q), -lam[q, p], Z(p), -f(bot, p, q)])
    return S, V, low

C = collections.Counter(); best = None; DUMPL = []; DUMPF = os.environ.get('DUMP'); t0 = time.time()
for args in corpora:
    for L in lattices(args):
        n, h = L.n, L.rank
        if h[L.top] < 3 or (MAXN is not None and n > MAXN): continue
        t1 = time.time(); S, V, low = encode(L)
        if S is None: continue
        if S.solve():
            m = set(l for l in S.get_model() if l > 0)
            F = [[(next(u for u in range(n) if V[('f', x, y, u)] in m) if x in low else L.top) for y in range(n)] for x in range(n)]
            w = W(L.S, F); ok = stair_world(w); nf = w.nofix(); d, N = w.dN()
            assert ok and nf and (not NEX or N == NEX), f'SAT/Python mismatch ok={ok} nofix={nf} N={N}'
            d, N = w.dN(); br = 'a' if h[d] == 2 else 'atom'
            print(f'  {" ".join(args)} lattice n={n} h={L.height}: SAT  (Stair NoFix model; branch {br}, N {N}, W0 {w.w0flat() and w.w0()})  {time.time() - t1:.0f}s', flush=True)
            C['SAT'] += 1; C[f'SAT h{L.height} {br} N{N}'] += 1
            DUMPL.append(dict(sets=L.S, F=F, corpus=args, mode=MODE))
            if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
        else:
            print(f'  {" ".join(args)} lattice n={n} h={L.height}: UNSAT  {time.time() - t1:.0f}s', flush=True); C['UNSAT'] += 1
        S.delete()
print(MODE, dict(C), 'smallest SAT', best[0] if best else None, f'total {time.time() - t0:.0f}s', flush=True)
if DUMPL: json.dump(DUMPL, open(DUMPF or f'stair_{MODE}_models.json', 'w'))
if best: json.dump(best[1], open(f'stair_{MODE}_min{best[0]}.json', 'w'))
