"""§34.3z²⁹⁹: ColourGain at every row of Z, any number of colours (refined P3 of brief run 20), worker's encoding.
World: rows x of height <= 2 are variables (one-hot, monotone in both arguments); higher rows are the constant top.
  a(bot) = bot; ZT; n1; h(top) >= 3; every row of Z lands (lambda(x) = first element of height <= 2 of the descent);
  colour atoms: atoms c of Z with c = phi(w) for some w (encoded exactly);
  unbounded: no element of Z lies above every colour atom;
  NoFix: no atom q of Z with lambda(q) outside Z and phi(lambda(q)) = q;
  ColourGain at row x: some colour atom c with c <= lambda(x) and c not <= x.
  No Tb at any row other than bot.
Modes (SAT = counterexample):
  all     ColourGain at every row of Z                    -> CGall fails
  colrows ColourGain at the colour rows only (mutant: the refuted R3-any relative)
  python3 cgall_probe.py MODE corpus... [maxn N] [min3]   (min3: at least three colour atoms)"""
import sys, itertools, json
sys.path.insert(0, '../separation'); sys.path.insert(0, '.')
from pysat.solvers import Cadical153
from pysat.card import CardEnc
from tight_probe import lattices
from rstages import a_of
MODE = sys.argv[1]; FL = {a for a in sys.argv[2:] if a in ('min3', 'TbA', 'TbM')}; args = [a for a in sys.argv[2:] if a not in FL]; MIN3 = 'min3' in FL
MAXN = None
if 'maxn' in args: k = args.index('maxn'); MAXN = int(args[k + 1]); args = args[:k] + args[k + 2:]
MEAN = {'all': 'colour atoms unbounded in Z, ColourGain at every row of Z, no mu-fixed atom (CGall fails)',
        'colrows': 'colour atoms unbounded in Z, ColourGain at the colour rows only, no mu-fixed atom (mutant)',
        'col2': 'colour atoms unbounded in Z, ColourGain at the colour rows and the height-2 rows of Z, no mu-fixed atom',
        'h2': 'colour atoms unbounded in Z, ColourGain at the height-2 rows of Z only, no mu-fixed atom',
        'colbot': 'colour atoms unbounded in Z, ColourGain at the colour rows and row bot, no mu-fixed atom'}[MODE]
print(f'cgall_probe {MODE} | per lattice: exists F | SAT = {MEAN}{" | at least 3 colours" if MIN3 else ""}{" | + Tb at atom rows" if "TbA" in FL else ""}{" | + Tb at height-2 rows" if "TbM" in FL else ""} | corpus {args} maxn {MAXN}', flush=True)
tot = {'SAT': 0, 'UNSAT': 0}; dump = []
for L in lattices(args):
    if MAXN is not None and L.n > MAXN: continue
    n, le, h, bot, top = L.n, L.le, L.rank, L.bot, L.top
    if h[top] < 3: continue
    NO = h[top] + 1; low = [x for x in range(n) if h[x] <= 2]; atoms = [x for x in range(n) if h[x] == 1]
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
    col = {}
    for c in atoms:                                       # col(c) <-> Z(c) and exists w with phi(w) = c
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
        add([-Z(x)] + [lam[x, p] for p in low])                              # rows of Z land
        if h[x] == 1:                                                        # NoFix
            for p in low: add([-Z(x), -lam[x, p], Z(p), -f(bot, p, x)])
        for p in low:                                                        # ColourGain
            cands = [col[c] for c in atoms if le[c][p] and not le[c][x]]
            if MODE == 'all': add([-Z(x), -lam[x, p]] + cands)
            elif h[x] == 1 and MODE != 'h2': add([-col[x], -lam[x, p]] + cands)
            if MODE in ('col2', 'h2') and h[x] == 2: add([-Z(x), -lam[x, p]] + cands)
            if MODE == 'colbot' and x == bot: add([-lam[x, p]] + cands)
    for x in low:                                         # optional Tb: no lower cell at a high column
        if x == bot or not ((h[x] == 1 and 'TbA' in FL) or (h[x] == 2 and 'TbM' in FL)): continue
        for y in range(n):
            if h[y] > 2:
                for u in range(n):
                    if le[u][x]: add([-Z(x), -f(x, y, u)])
    if MIN3:                                              # at least three colours (auxiliaries above every used id)
        for cl in CardEnc.atleast([col[c] for c in atoms], bound=3, top_id=len(V)).clauses: add(cl)
    if S.solve():
        m = set(l for l in S.get_model() if l > 0)
        F = [[(next(u for u in range(n) if V[('f', x, y, u)] in m) if x in low else top) for y in range(n)] for x in range(n)]
        phi = F[bot]; Zs = [y for y in range(n) if phi[y] == bot]
        def desc(x):
            z = top; s = []
            while z not in s: s.append(z); z = F[x][z]
            return s
        def lamf(x): return next((z for z in desc(x) if h[z] <= 2), None)
        cols = sorted({phi[w] for w in range(n) if h[phi[w]] == 1 and phi[w] in Zs})
        ok = a_of(L, F, bot) == bot and all(h[z] <= 2 for z in Zs) and any(h[z] == 2 for z in Zs)
        ok = ok and all(lamf(x) is not None for x in Zs) and not any(all(le[c][z] for c in cols) for z in Zs)
        ok = ok and not any(h[q] == 1 and lamf(q) not in Zs and phi[lamf(q)] == q for q in Zs)
        rows = Zs if MODE == 'all' else ([] if MODE == 'h2' else cols) + ([z for z in Zs if h[z] == 2] if MODE in ('col2', 'h2') else []) + ([bot] if MODE == 'colbot' else [])
        ok = ok and all(any(le[c][lamf(x)] and not le[c][x] for c in cols) for x in rows)
        ok = ok and (not MIN3 or len(cols) >= 3)
        hi_ = [y for y in range(n) if h[y] > 2]
        ok = ok and all(not le[F[x][y]][x] for x in Zs if x != bot and ((h[x] == 1 and 'TbA' in FL) or (h[x] == 2 and 'TbM' in FL)) for y in hi_)
        assert ok, 'SAT/replay mismatch'
        tot['SAT'] += 1; dump.append(dict(sets=L.S, F=F, colours=cols))
        print(f'  lattice n={n} h={L.height}: SAT (colours {cols})', flush=True)
    else:
        tot['UNSAT'] += 1; print(f'  lattice n={n} h={L.height}: UNSAT', flush=True)
    S.delete()
print(MODE, args, tot)
if dump: json.dump(dump, open(f'cgall_{MODE}_{"_".join(args)}_{"_".join(sorted(FL))}.json', 'w'))
