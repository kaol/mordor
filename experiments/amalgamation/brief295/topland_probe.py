"""Brief run 20, P2 probe "TopLand_S".  World W0 + n1 through (T) (same scheme as stair_probe.py / orbit_probe.py:
one-hot rows F(x, .) for low x, monotone; a(bot) = bot; ZT; n1; h(top) >= 3; Ta and Tb at every row of Z).
calA = atoms q of Z with q = F(bot, w) for some w;  S = {bot} u calA u {z in Z of height 2 above two atoms of calA};
g_S(y) = join_{z in S} F(z, y)  (a virtual row; TopRow, brief §5: if the g_S-iteration from top gets low, CertAtom).
TopLand_S fails  <=>  some high Y has Y <= g_S(Y)  (then gfp g_S is high and the iteration from top never gets low).
QUANTIFIER: for each lattice, EXISTS F in W0 (with the branch / exact-N flags) such that TopLand_S FAILS.
SAT = TopLand_S fails on this lattice (model replayed from the definitions and saved).  UNSAT = TopLand_S holds there.
Flags: Ba (branch a: h(d) = 2) | Bb (branch atom: d an atom) ; E2..E6 exact N ; Nge2 (N >= 2) ; maxn K.
MUTANT flag T1: S replaced by Z ^ down(t1), t1 = F(bot, top) (TopLand_t1: refuted on stored W0 models, branch a
included: 4 of 9 stored branch-a N >= 2 models; topland_census.py).
  python3 topland_probe.py [Ba|Bb] [E2..E6|Nge2] [maxn K] CORPUS"""
import sys, os, json, itertools, collections, time, functools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation'); sys.path.insert(0, '/home/user/mordor/experiments/separation')
sys.path.insert(0, HERE); sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291')
from pysat.solvers import Cadical153
from tight_probe import lattices
from world import W
from closure_census import first_low

rest = sys.argv[1:]
T1 = 'T1' in rest; rest = [a for a in rest if a != 'T1']
BR = 'a' if 'Ba' in rest else ('atom' if 'Bb' in rest else None)
NEX = next((int(a[1:]) for a in rest if a in ('E2', 'E3', 'E4', 'E5', 'E6')), 0); NGE2 = 'Nge2' in rest
rest = [a for a in rest if a not in ('Ba', 'Bb', 'E2', 'E3', 'E4', 'E5', 'E6', 'Nge2')]
MAXN = None
if rest[:1] == ['maxn']: MAXN = int(rest[1]); rest = rest[2:]
print(__doc__.split('\n  python3')[0])
print(f'topland_probe {"MUTANT T1 (S = Z ^ down t1)" if T1 else "candidate S"} branch={BR} exactN={NEX or None} Nge2={NGE2} maxn={MAXN} corpus={rest}', flush=True)

def S_of(w):
    phi = w.F[w.bot]; L = w.L
    calA = sorted({phi[y] for y in range(w.n) if phi[y] != w.bot and w.h[phi[y]] == 1 and phi[phi[y]] == w.bot})
    return calA, {w.bot} | set(calA) | {z for z in w.Z if w.h[z] == 2 and sum(1 for q in calA if w.le[q][z]) >= 2}

def encode(L):
    n, le, h, bot, top = L.n, L.le, L.rank, L.bot, L.top
    low = [x for x in range(n) if h[x] <= 2]; NO = h[top] + 1; hi = [y for y in range(n) if h[y] > 2]
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
    for x in low:                                        # (T) at rows of Z: Ta and Tb
        if x == bot: continue
        for y in hi:
            for u in range(n):
                if le[y][u] or le[u][x]: add([-Z(x), -f(x, y, u)])
    it = lambda j, z: v('it', j, z)                      # the bot-descent only
    for z in range(n): add([it(0, z)] if z == top else [-it(0, z)])
    for j in range(NO):
        for z in range(n):
            for u in range(n): add([-it(j, z), -f(bot, z, u), it(j + 1, u)])
        for z, z2 in itertools.combinations(range(n), 2): add([-it(j + 1, z), -it(j + 1, z2)])
    # N and branch: d = t_N is the last nonzero element; t_(N+1) = bot
    Ns = [NEX] if NEX else list(range(2 if NGE2 else 1, NO))
    nsel = []
    for N in Ns:
        if N + 1 > NO: continue
        t = v('N', N); nsel.append(t)
        add([-t, -it(N, bot)]); add([-t, it(N + 1, bot)])
        if BR: add([-t] + [it(N, z) for z in range(n) if h[z] == (2 if BR == 'a' else 1)])
    if not nsel: return None, None, None
    add(nsel)
    # calA, S
    A = lambda q: v('A', q); s = lambda z: v('s', z)
    atoms = [q for q in low if h[q] == 1]
    for q in atoms:
        add([-A(q), Z(q)]); add([-A(q)] + [f(bot, w_, q) for w_ in range(n)])
    for z in low:
        if T1:                                            # mutant: S = Z ^ down(t1)
            add([-s(z), Z(z)]); add([-s(z)] + [f(bot, top, t) for t in range(n) if le[z][t]]); continue
        if z == bot: add([s(z)]); continue
        if h[z] == 1: add([-s(z), A(z)]); continue
        ps = [(q1, q2) for q1, q2 in itertools.combinations(atoms, 2) if le[q1][z] and le[q2][z]]
        add([-s(z), Z(z)]); add([-s(z)] + [v('pr', q1, q2) for q1, q2 in ps])
        for q1, q2 in ps: add([-v('pr', q1, q2), A(q1)]); add([-v('pr', q1, q2), A(q2)])
    # TopLand_S fails: some high Y with Y <= join_{z in S} F(z, Y)
    st = lambda Y: v('stuck', Y); add([st(Y) for Y in hi])
    for Y in hi:
        for e in range(n):
            if le[Y][e]: continue                         # every upper bound e of the values must be >= Y
            add([-st(Y)] + [v('a', z, Y, u) for z in low for u in range(n) if not le[u][e]])
        for z in low:
            for u in range(n):
                add([-v('a', z, Y, u), s(z)]); add([-v('a', z, Y, u), f(z, Y, u)])
    return S, V, low

C = collections.Counter(); best = None; DUMPL = []; DUMPF = os.environ.get('DUMP'); t0 = time.time()
for L in lattices(rest):
    n, h = L.n, L.rank
    if h[L.top] < 3 or (MAXN is not None and n > MAXN): continue
    t1 = time.time(); S, V, low = encode(L)
    if S is None: continue
    if S.solve():
        m = set(l for l in S.get_model() if l > 0)
        F = [[(next(u for u in range(n) if V[('f', x, y, u)] in m) if x in low else L.top) for y in range(n)] for x in range(n)]
        w = W(L.S, F); d, N = w.dN(); br = 'a' if h[d] == 2 else 'atom'
        calA, Sset = S_of(w)
        if T1: Sset = {z for z in w.Z if w.le[z][w.F[w.bot][w.top]]}
        fails = first_low(w, sorted(Sset)) is None
        ok = w.base() and w.w0flat() and w.w0() and fails and (not BR or br == BR) and (not NEX or N == NEX) and (not NGE2 or N >= 2)
        assert ok, f'SAT/Python mismatch base={w.base()} w0={w.w0flat() and w.w0()} fails={fails} br={br} N={N}'
        fx = [q for q in w.atoms if w.fixed(q)]
        print(f'  lattice n={n} h={L.height}: SAT  (W0 model, TopLand_S fails; branch {br}, N {N}, |calA| {len(calA)}, fixed atoms {fx})  {time.time() - t1:.0f}s', flush=True)
        C['SAT'] += 1; C[f'SAT {br} N{N}'] += 1
        DUMPL.append(dict(sets=L.S, F=F, corpus=rest, refutes='TopLand_S', branch=br, N=N))
        if best is None or n < best[0]: best = (n, DUMPL[-1])
    else:
        print(f'  lattice n={n} h={L.height}: UNSAT  {time.time() - t1:.0f}s', flush=True); C['UNSAT'] += 1
    S.delete()
print('topland', dict(C), 'smallest SAT', best[0] if best else None, f'total {time.time() - t0:.0f}s', flush=True)
if DUMPL: json.dump(DUMPL, open(DUMPF or 'topland_models.json', 'w'))
if best: json.dump(best[1], open(f'topland_min{best[0]}.json', 'w'))
