"""Brief run 18, audit probe "Repair": is every model of the world W0^2 repairable, i.e. does its descent-maximal form
F# (brief291 A3: same descents, F#(x,y) = meet over x' in Z, x' >= x of F(x', sigma_{x'}(y))) lie in W0?
TwoRowTb (CertAtom in W0^2) says more than CertAtom only on IRREPARABLE models (F in W0^2, F# not in W0).

QUANTIFIER: for each lattice of the corpus, EXISTS F in W0^2 and EXISTS an atom q of Z and a high column w with
            meet_{x' in Z, x' >= q} succ_{x'}(sigma_{x'}(w)) <= q          (that meet is F#(q, w)).
SAT  = an irreparable W0^2 model exists on this lattice (Repair fails there; the lattice gives TwoRowTb room).
UNSAT = every W0^2 model on this lattice is repaired by F# (TwoRowTb has no content beyond CertAtom there).
Mode 'irrepnf' adds NoFix (no mu-fixed atom): SAT would refute TwoRowTb itself.

World W0^2 (frontier §2): a(bot) = bot, ZT, n1, h(top) >= 3, Ta at every row of Z (= every row lands), lambda(m) not <= m
for m in M2, Tb at an atom row q only at high columns u ^ v with u in desc(q), v in desc(x), x in Z, q <= x.
Encoding written from these definitions (one-hot rows of height <= 2, as in orbit_probe.py); every SAT model is decoded,
completed (rows of height >= 3 constant top) and re-checked in Python from the definitions (corners.w0sq, dmaxviol.sharp,
world.W); an assertion aborts on any mismatch.  Every SAT model is saved.
  python3 irrep_probe.py MODE [maxn N] CORPUS [+ CORPUS ...]      (MODE = irrep | irrepnf; DUMP=file.json)"""
import sys, os, json, itertools, collections, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation'); sys.path.insert(0, '/home/user/mordor/experiments/separation')
sys.path.insert(0, HERE); sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291')
from pysat.solvers import Cadical153
from tight_probe import lattices
from corners import w0sq
from dmaxviol import sharp
from world import W

MODE = sys.argv[1]; assert MODE in ('irrep', 'irrepnf')
rest = sys.argv[2:]; MAXN = None
D1 = 'D1' in rest; FAST = 'fast' in rest; rest = [a for a in rest if a not in ('D1', 'fast')]   # fast: TbFibre restriction (phi(w) = q, e over covers of q) -- same SAT set (brief §2 A2)   # CONTROL world Desc1: Tb at q only on desc(q) (refuted relative)
if rest[:1] == ['maxn']: MAXN = int(rest[1]); rest = rest[2:]
corpora = [[]]
for a in rest:
    if a == '+': corpora.append([])
    else: corpora[-1].append(a)
print(__doc__.split('\n\n')[1])
print(f'irrep_probe {MODE}{" CONTROL-WORLD Desc1" if D1 else ""}{" fast" if FAST else ""} maxn={MAXN} corpora={corpora}', flush=True)

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
    for q in low:                                        # Tb at atom rows only at two-row meet columns
        if h[q] != 1: continue
        for x in low:
            if not le[q][x] or (D1 and x != q): continue
            for u1 in range(n):
                for u2 in ([top] if D1 else range(n)):
                    w = L.meet[u1][u2]
                    if h[w] <= 2: continue
                    for u in range(n):
                        if le[u][q]: add([-Z(q), -Z(x), -D(q, u1), -D(x, u2), -f(q, w, u)])
    if MODE == 'irrepnf':                                # NoFix: no atom q with lambda(q) = p not in Z and F(bot, p) = q
        for q in low:
            if h[q] != 1: continue
            for p in low: add([-Z(q), -lam[q, p], Z(p), -f(bot, p, q)])
    # irreparable: some atom q, high w with meet_{x' >= q in Z} s_{x'}(w) <= q
    ge = {}
    for w in hi:
        for x in low:
            for j in range(NO + 1):
                o = v('ge', w, x, j); ge[w, x, j] = o
                ls = [it(x, j, z) for z in range(n) if le[w][z]]
                for l in ls: add([-l, o])
                add([-o] + ls)
    sel = []
    for q in low:
        if h[q] != 1: continue
        E = [e for e in range(n) if not le[e][q] and all(le[t][q] for t in L.covers_dn[e])]   # minimal elements off down(q)
        if FAST: E = [e for e in L.covers_up[q]]          # with phi(w) = q every succ value is >= q: only covers of q matter
        rows = [x for x in low if le[q][x] and x != bot]
        for w in hi:
            s = v('sel', q, w); sel.append(s); add([-s, Z(q)])
            if FAST: add([-s, f(bot, w, q)])                 # TbFibre: an F#-violation at (q, w) has phi(w) = q
            for e in E:
                ys = []
                for x in rows:
                    y_ = v('Y', q, w, e, x); ys.append(y_); add([-y_, Z(x)])
                    js = []
                    for j in range(NO):
                        t = v('Yj', w, x, j, e); js.append(t)
                        add([-t, ge[w, x, j]]); add([-t, -ge[w, x, j + 1]])
                        add([-t] + [it(x, j + 1, z) for z in range(n) if not le[e][z]])
                    add([-y_] + js)
                add([-s] + ys)
    add(sel)
    return S, V, low

C = collections.Counter(); best = None; DUMPL = []; DUMPF = os.environ.get('DUMP'); t0 = time.time()
for args in corpora:
    for L in lattices(args):
        n, h = L.n, L.rank
        if h[L.top] < 3 or (MAXN is not None and n > MAXN): continue
        t1 = time.time(); S, V, low = encode(L)
        if S.solve():
            m = set(l for l in S.get_model() if l > 0)
            F = [[(next(u for u in range(n) if V[('f', x, y, u)] in m) if x in low else L.top) for y in range(n)] for x in range(n)]
            w = W(L.S, F); ok = w0sq(w) if not D1 else (w.base() and all(w.lam(x) is not None for x in w.Z))
            G, _ = sharp(w); vv = W(L.S, G); rep = vv.mono and vv.w0flat() and vv.w0()
            nf = w.nofix()
            assert ok and not rep and (MODE == 'irrep' or nf), f'SAT/Python mismatch ok={ok} rep={rep} nofix={nf}'
            d, N = w.dN(); br = 'a' if h[d] == 2 else 'atom'
            print(f'  {" ".join(args)} lattice n={n} h={L.height}: SAT  (irreparable W0^2 model; branch {br}, N {N}, NoFix {nf}, '
                  f'W0 {w.w0flat() and w.w0()})  {time.time() - t1:.0f}s', flush=True)
            C['SAT'] += 1; C[f'SAT h{L.height} {br} N{N}'] += 1
            DUMPL.append(dict(sets=L.S, F=F, corpus=args, mode=MODE))
            if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
        else:
            print(f'  {" ".join(args)} lattice n={n} h={L.height}: UNSAT  {time.time() - t1:.0f}s', flush=True); C['UNSAT'] += 1
        S.delete()
print(MODE, dict(C), 'smallest SAT', best[0] if best else None, f'total {time.time() - t0:.0f}s', flush=True)
if DUMPL: json.dump(DUMPL, open(DUMPF or f'irrep_{MODE}_models.json', 'w'))
if best: json.dump(best[1], open(f'irrep_{MODE}_min{best[0]}.json', 'w'))
