"""§34.3z²⁹⁷ (worker's independent encoding of brief run 20's lead): two colour atoms, three rows.
World (written from the statement, not from the briefer's open_probe.py): rows bot, a, b of a monotone F (every other
row is the constant top, which is admissible since no hypothesis constrains it); phi = F(bot, .).
  a(bot) = bot; ZT (Z := phi^-1(bot) has heights <= 2); n1 (some height-2 element of Z); h(top) >= 3;
  colours: the atoms c of Z with c = phi(w) for some w are exactly a and b; no element of Z lies above both;
  rows a and b land (their descents from top reach an element of height <= 2; lambda = the first such element);
  NoFix: no c in {a, b} has lambda(c) outside Z with phi(lambda(c)) = c.
Modes (SAT = counterexample to the statement named):
  r3      ColourGain at both colour rows (b <= lambda(a), a <= lambda(b))   -> TwoColourCG fails
  cgone   ColourGain at row b only                                          -> calibrated mutant (CGone)
  shadow  ColourGain at row b only, and not a <= phi(r_a) (r_a = last high element of row a's descent)
                                                                            -> ShadowLemma fails
Per lattice the ordered (cgone, shadow) or unordered (r3) colour pairs are tried; SAT models are replayed from the
definitions (assertion) and dumped.
  python3 r3_probe.py MODE corpus... [maxn N]"""
import sys, itertools, json
sys.path.insert(0, '../separation'); sys.path.insert(0, '.')
from pysat.solvers import Cadical153
from tight_probe import lattices
from rstages import a_of
MODE = sys.argv[1]; args = [x for x in sys.argv[2:] if x not in ('noNFa', 'noNFb', 'noCG')]; NONFA = 'noNFa' in sys.argv[2:]
NONFB = 'noNFb' in sys.argv[2:]; NOCG = 'noCG' in sys.argv[2:]
MAXN = None
if 'maxn' in args: k = args.index('maxn'); MAXN = int(args[k + 1]); args = args[:k] + args[k + 2:]
MEAN = {'r3': 'two unbounded colours a, b, ColourGain at both colour rows, no mu-fixed colour (TwoColourCG fails)',
        'cgone': 'two unbounded colours, ColourGain at row b only, no mu-fixed colour (mutant CGone)',
        'shadow': 'two unbounded colours, ColourGain at row b only, no mu-fixed colour, a not <= phi(r_a) (ShadowLemma fails)',
        'break': 'two unbounded colours, ColourGain at row b only, no mu-fixed colour, and the (a, b) staircase has a corner J = a v b outside Z with phi(J) = b whose boundary point above has phi = b (NoBreak fails)'}[MODE] + (' [NoFix at a DROPPED]' if NONFA else '') + (' [NoFix at b DROPPED]' if NONFB else '') + (' [ColourGain DROPPED]' if NOCG else '')
print(f'r3_probe {MODE} | per lattice: exists F and colour pair | SAT = {MEAN} | corpus {args} maxn {MAXN}', flush=True)
tot = {'SAT': 0, 'UNSAT': 0}; dump = []
for L in lattices(args):
    if MAXN is not None and L.n > MAXN: continue
    n, le, h, bot, top = L.n, L.le, L.rank, L.bot, L.top
    if h[top] < 3: continue
    NO = h[top] + 1
    atoms = [x for x in range(n) if h[x] == 1]
    pairs = list(itertools.permutations(atoms, 2)) if MODE != 'r3' else list(itertools.combinations(atoms, 2))
    found = None
    for (A, B) in pairs:
        S = Cadical153(); V = {}
        def v(*k):
            if k not in V: V[k] = len(V) + 1
            return V[k]
        add = S.add_clause; rows = [bot, A, B]
        f = lambda x, y, u: v('f', x, y, u)
        for x in rows:
            for y in range(n):
                ls = [f(x, y, u) for u in range(n)]; add(ls)
                for p, q in itertools.combinations(ls, 2): add([-p, -q])
            for y in range(n):
                for y2 in L.covers_up[y]:
                    for u in range(n): add([-f(x, y, u)] + [f(x, y2, w) for w in range(n) if le[u][w]])
        for x in (A, B):                                   # monotone in the row: F(bot, .) <= F(x, .)
            for y in range(n):
                for u in range(n): add([-f(bot, y, u)] + [f(x, y, w) for w in range(n) if le[u][w]])
        Z = lambda y: f(bot, y, bot)
        for y in range(n):                                 # a(bot) = bot
            if y != bot:
                for u in range(n):
                    if le[y][u]: add([-f(bot, y, u)])
            if h[y] > 2: add([-Z(y)])                      # ZT
        add([Z(y) for y in range(n) if h[y] == 2])         # n1
        add([Z(A)]); add([Z(B)])                           # colours
        add([f(bot, w, A) for w in range(n)]); add([f(bot, w, B) for w in range(n)])
        for c in atoms:
            if c in (A, B): continue
            for w in range(n): add([-f(bot, w, c), -Z(c)])
        for z in range(n):                                 # unbounded: no element of Z above both
            if le[A][z] and le[B][z]: add([-Z(z)])
        it = lambda x, j, z: v('it', x, j, z)
        for x in (A, B):
            for z in range(n): add([it(x, 0, z)] if z == top else [-it(x, 0, z)])
            for j in range(NO):
                for z in range(n):
                    for u in range(n): add([-it(x, j, z), -f(x, z, u), it(x, j + 1, u)])
                for z, z2 in itertools.combinations(range(n), 2): add([-it(x, j + 1, z), -it(x, j + 1, z2)])
            lam = {}
            for p in range(n):
                if h[p] > 2: continue
                ts = []
                for j in range(1, NO + 1):
                    t = v('t', x, j, p); ts.append(t)
                    hi = [it(x, j - 1, z) for z in range(n) if h[z] > 2]
                    add([-t, it(x, j, p)]); add([-t] + hi)
                    for z in range(n):
                        if h[z] > 2: add([t, -it(x, j, p), -it(x, j - 1, z)])
                lam[p] = v('lam', x, p)
                for t in ts: add([-t, lam[p]])
                add([-lam[p]] + ts)
            add([lam[p] for p in lam])                      # the row lands
            other = B if x == A else A
            cg = ((MODE == 'r3') or (x == B)) and not NOCG
            for p in lam:
                if cg and not le[other][p]: add([-lam[p]])  # ColourGain at this colour row
                if not (NONFA and x == A) and not (NONFB and x == B): add([-lam[p], Z(p), -f(bot, p, x)])        # NoFix at this colour
            if MODE == 'shadow' and x == A:                # not a <= phi(r_a)
                for j in range(1, NO + 1):
                    for p in lam:
                        for z in range(n):
                            if h[z] <= 2: continue
                            for u in range(n):
                                if le[A][u]: add([-v('t', x, j, p), -it(x, j - 1, z), -f(bot, z, u)])
        if MODE == 'break':
            Jn = L.join[A][B]
            if h[Jn] != 2: S.delete(); continue
            add([-Z(Jn)]); add([f(bot, Jn, B)])
            sel = []
            trip = [(x, y, y2) for x in range(n) if le[Jn][x] for y in range(n) if le[Jn][y] and L.meet[x][y] == Jn
                    for y2 in range(n) if le[y][y2] and y2 != y and h[L.meet[x][y2]] > 2]
            for j in range(NO + 1):
                for k in range(1, NO + 1):
                    for (x, y, y2) in trip:
                        t = v('brk', j, k, x, y, y2); sel.append(t)
                        for lit in (it(A, j, x), it(B, k, y), it(B, k - 1, y2), f(bot, L.meet[x][y2], B)): add([-t, lit])
            if not sel: S.delete(); continue
            add(sel)
        if S.solve():
            m = set(l for l in S.get_model() if l > 0)
            F = [[(next(u for u in range(n) if V[('f', x, y, u)] in m) if x in rows else top) for y in range(n)] for x in range(n)]
            phi = F[bot]; Zs = [y for y in range(n) if phi[y] == bot]
            def desc(x):
                z = top; s = []
                while z not in s: s.append(z); z = F[x][z]
                return s
            def lamf(x): return next((z for z in desc(x) if h[z] <= 2), None)
            cols = sorted({phi[w] for w in range(n) if h[phi[w]] == 1 and phi[w] in Zs})
            ok = (a_of(L, F, bot) == bot and all(h[z] <= 2 for z in Zs) and any(h[z] == 2 for z in Zs) and cols == sorted([A, B])
                  and not any(le[A][z] and le[B][z] for z in Zs) and lamf(A) is not None and lamf(B) is not None
                  and all(x == bot or all(le[F[bot][y]][F[x][y]] for y in range(n)) for x in rows))
            ok = ok and not any(lamf(c) not in Zs and phi[lamf(c)] == c for c in [c_ for c_ in (A, B) if not (NONFA and c_ == A) and not (NONFB and c_ == B)])
            ok = ok and (NOCG or (le[A][lamf(B)] and (MODE != 'r3' or le[B][lamf(A)])))
            if MODE == 'break':
                da, db = desc(A), desc(B); Jn = L.join[A][B]
                ok = ok and Jn not in Zs and phi[Jn] == B and any(L.meet[x][db[k]] == Jn and h[L.meet[x][db[k - 1]]] > 2 and phi[L.meet[x][db[k - 1]]] == B
                                                                  for x in da for k in range(1, len(db)))
            if MODE == 'shadow':
                d = desc(A); i = d.index(lamf(A)); ok = ok and not le[A][phi[d[i - 1]]]
            assert ok, 'SAT/replay mismatch'
            found = (A, B, F); S.delete(); break
        S.delete()
    if found:
        tot['SAT'] += 1; dump.append(dict(sets=L.S, F=found[2], colours=[found[0], found[1]]))
        print(f'  lattice n={n} h={L.height}: SAT (colours {found[0]}, {found[1]})', flush=True)
    else:
        tot['UNSAT'] += 1; print(f'  lattice n={n} h={L.height}: UNSAT ({len(pairs)} pairs)', flush=True)
print(MODE, args, tot)
if dump: json.dump(dump, open(f'r3_{MODE}_{"_".join(args)}.json', 'w'))
