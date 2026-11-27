"""Run-17 briefer probe: WHICH instances of Tb at the atom rows does existence (CertAtom) use?  Exact SAT, one-hot rows
(encoding written from the definitions; layout as lfp_probe.py).  high = height >= 3.
Common world (all modes): a(bot) = bot; ZT; n1; h(top) >= 3; Ta at every row of Z; at every height-2 row m of Z only the
descent form lambda(m) not <= m (DescTb2; equivalent to full Tb there for CertAtom by the normalization theorem, brief §2).
Tb at an atom row q of Z is imposed only at the high columns listed per mode:
  w0d  : every high column                                   (control = CertAtom in W0^desc ~ W0; expect UNSAT)
  two  : columns u_i(q) /\\ u_j(x), u_i(q) on row q's descent, u_j(x) on row x's descent, x in Z with q <= x
         (one descent element of q and one of a row of Z above q; x = q gives q's own descent)      (CANDIDATE TwoRowTb)
  desc1: columns on row q's own descent only (= Tb in descent form lambda(q) not <= q; the refuted relative desc1 of
         brief289 run 1, banked there as run1/certrole_nofix_desc1_min10.json)                 (CALIBRATED MUTANT)
MODES: SAT = the mode's world has a model with NoFix (no atom of Z is mu-fixed), i.e. CertAtom FAILS there.
Every SAT model is decoded and replayed in Python from the definitions (world.py + the mode's Tb list), else abort.
  python3 meet_probe.py MODES TAG CORPUS [+ CORPUS ...] [maxn K]"""
import sys, os, itertools, collections, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from pysat.solvers import Cadical153
from tight_probe import lattices
from world import W

MODES = sys.argv[1].split(','); TAG = sys.argv[2]; args = sys.argv[3:]; MAXN = None
if 'maxn' in args: k_ = args.index('maxn'); MAXN = int(args[k_ + 1]); args = args[:k_] + args[k_ + 2:]
NEX = next((int(a[1:]) for a in args if a[0] == 'E' and a[1:].isdigit()), 0)       # exact N: t_N != bot = t_(N+1)
args = [a for a in args if not (a[0] == 'E' and a[1:].isdigit())]
SATM = {'w0d': 'NoFix in W0^desc (CertAtom FAILS; control)', 'two': 'NoFix with Tb at atoms only at two-row meet columns (TwoRowTb FAILS)',
        'desc1': 'NoFix with Tb at atoms only on their own descent (mutant desc1 FAILS)'}
for M_ in MODES: print(f'meet_probe {M_} | quantifier: exists F in the mode world{" with exact N = " + str(NEX) if NEX else ""} | SAT = {SATM[M_]} | corpus {args}', flush=True)

def solve(L, MODE):
    n = L.n; le = L.le; h = L.rank; bot = L.bot; top = L.top; meet = L.meet
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
    for y in range(n):
        if y != bot:
            for u in range(n):
                if le[y][u]: add([-f(bot, y, u)])
    for y in hi: add([-Z(y)])
    add([Z(y) for y in range(n) if h[y] == 2])
    it = lambda x, j, z: v('it', x, j, z)
    for x in low:
        for z in range(n): add([it(x, 0, z)] if z == top else [-it(x, 0, z)])
        for j in range(NO):
            for z in range(n):
                for u in range(n): add([-it(x, j, z), -f(x, z, u), it(x, j + 1, u)])
            for z, z2 in itertools.combinations(range(n), 2): add([-it(x, j + 1, z), -it(x, j + 1, z2)])
    if NEX:
        if NEX + 1 > NO: S.delete(); return 'skip'
        add([-it(bot, NEX, bot)]); add([it(bot, NEX + 1, bot)])
    on = lambda x, z: v('on', x, z)
    for x in low:
        for j in range(NO + 1):
            for z in range(n): add([-it(x, j, z), on(x, z)])
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
    for x in low:
        if x == bot: continue
        for y in hi:
            for u in range(n):
                if le[y][u]: add([-Z(x), -f(x, y, u)])                                  # Ta at every row of Z
        if h[x] == 2:                                                                    # DescTb2
            for p in low:
                if le[p][x]: add([-Z(x), -lam[x, p]])
        if h[x] == 1:
            q = x; us = [u for u in range(n) if le[u][q]]
            if MODE == 'w0d':
                for y in hi:
                    for u in us: add([-Z(q), -f(q, y, u)])
            elif MODE == 'desc1':
                for y in hi:
                    for u in us: add([-Z(q), -on(q, y), -f(q, y, u)])
            elif MODE == 'two':
                for x2 in low:
                    if not le[q][x2]: continue
                    done = set()
                    for z1 in range(n):
                        for z2 in range(n):
                            y = meet[z1][z2]
                            if h[y] < 3 or (z1, z2) in done: continue
                            for u in us: add([-Z(q), -Z(x2), -on(q, z1), -on(x2, z2), -f(q, y, u)])
    for q in [q for q in low if h[q] == 1]:                                              # NoFix
        for p in low: add([-Z(q), -lam[q, p], -f(bot, p, q)])
    if not S.solve(): S.delete(); return None
    m = set(l for l in S.get_model() if l > 0)
    F = [[(next(u for u in range(n) if V[('f', x, y, u)] in m) if x in low else top) for y in range(n)] for x in range(n)]
    S.delete(); return F

def replay(L, F, MODE):
    w = W(L.S, F); le = w.le; h = w.h; meet = L.meet
    ok = w.base() and all(w.Ta(x) for x in w.Z if x != w.bot) and all(not le[w.lam(m)][m] for m in w.M2) and w.nofix()
    for q in w.atoms:
        dq = set(w.desc(q))
        if MODE == 'w0d': cols = set(w.hi)
        elif MODE == 'desc1': cols = set(y for y in dq if h[y] >= 3)
        else: cols = set(meet[z1][z2] for x2 in w.Z if le[q][x2] for z1 in dq for z2 in w.desc(x2) if h[meet[z1][z2]] >= 3)
        ok = ok and all(not le[F[q][y]][q] for y in cols)
    d, N = w.dN()
    if NEX: ok = ok and N == NEX
    br = 'a' if h[d] == 2 else ('g' if (le[d][w.a(d)] or d in w.desc(d)) else 'b')
    tbfull = all(w.Tb(q) for q in w.atoms)
    return ok, br, N, w.noexit(), tbfull

def corpora(a):
    cur = []
    for t in a + ['+']:
        if t == '+':
            if cur: yield from lattices(cur)
            cur = []
        else: cur.append(t)
C = {M_: collections.Counter() for M_ in MODES}; best = {}; allm = collections.defaultdict(list); t0 = time.time(); cnt = 0
for L in corpora(args):
    if MAXN is not None and L.n > MAXN: continue
    if L.rank[L.top] < 3: continue
    cnt += 1; row = []
    for M_ in MODES:
        F = solve(L, M_)
        if F == 'skip': C[M_]['skip(N)'] += 1; row.append(f'{M_}:skip'); continue
        if F is None: C[M_]['UNSAT'] += 1; row.append(f'{M_}:UNSAT'); continue
        ok, br, N, ne, tbf = replay(L, F, M_)
        assert ok, f'SAT/Python mismatch on {M_}'
        if tbf and M_ != 'w0d':
            fn = os.path.join(os.getcwd(), f'ALERT_fullTb_{M_}_{TAG}_n{L.n}.json'); json.dump(dict(sets=L.S, F=F), open(fn, 'w'))
            print('  ALERT: model with full Tb at atom rows (a W0^desc counterexample to CertAtom) ->', fn, flush=True)
        C[M_]['SAT'] += 1; C[M_]['SAT_' + br] += 1; C[M_][f'SAT_N{N}'] += 1
        row.append(f'{M_}:SAT({br},N{N},{"noexit" if ne else "exit"})')
        mod = dict(sets=L.S, F=F, mode=M_, N=N, world=M_ + '-world (see meet_probe.py docstring)', tag=TAG, refutes={'two': 'TwoRowTb', 'desc1': 'CertAtom under desc1', 'w0d': 'CertAtom (W0^desc)'}[M_])
        allm[M_].append(mod)
        if M_ not in best or L.n < best[M_][0]: best[M_] = (L.n, mod)
    print(f'  lattice #{cnt} n={L.n} h={L.height} [{time.time() - t0:.0f}s]: ' + ' '.join(row), flush=True)
print('SUMMARY', TAG, args, f'{time.time() - t0:.0f}s', f'{cnt} lattices')
for M_ in MODES: print('  ', M_, '|', SATM[M_], '|', dict(C[M_]))
for M_, (n_, Mod) in best.items():
    fn = os.path.join(os.getcwd(), f'meet_{M_}_{TAG}_min{n_}.json'); json.dump(Mod, open(fn, 'w')); print('  smallest', M_, n_, '->', fn)
for M_, L_ in allm.items():
    if M_ in ('two', 'w0d'):
        fn = os.path.join(os.getcwd(), f'meet_{M_}_{TAG}_all.json'); json.dump(L_, open(fn, 'w')); print('  all SAT models', M_, len(L_), '->', fn)
