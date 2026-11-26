"""amr_run15 briefer -- exact probes (pysat Cadical153) of the run-15 candidates, one solver per lattice.

WORLD (W0 + n1, h(top) >= 3), the run-13 ctlA lean encoding (w0lean.py, copied here) with one change: the lower half Tb of
(T) at the atom rows and at the height-2 rows of Z is guarded by selector literals, so one solver serves five worlds:
  full   : (T) at every row of Z                                              = W0 + n1     (assumptions gF, gFA)
  desc2  : at height-2 rows m, Tb only along row m's own descent (F(m,t) not<= m for HIGH t on m's descent, i.e.
           lambda(m) not<= m); Tb in full at atom rows                                      (gD, gFA)
  noTb2  : Tb dropped at height-2 rows (section 283's Ta2 + land)                           (gFA)
  desc12 : Tb only along own descent at atom rows AND at height-2 rows                      (gD, gDA)
  noTb1  : Tb dropped at atom rows (section 283's Ta1 + land), full at height-2 rows         (gF)
  Ta (upper half) and Tb at row bot are kept in every world; Ta at row x <=> h(a(x)) <= 2 <=> row x lands.
  NOV (relaxed worlds): SAT iff the relaxed world has a model in which the dropped half is really violated (some row of
  Z of the relaxed height has a lower cell at a high column), i.e. the relaxation is not vacuous.
Rows exist only for low elements (h <= 2); F one-hot, monotone in x and y; Z(y) = [F(bot, y) = bot]; a(bot) = bot; n1.
Descents it(x, j, .) exact from top; lambda = first element of height <= 2; exit = lambda not in Z; c = F(bot, lambda).
mu-fixed atom q: q in Z, lambda(q) of height 2 with F(bot, lambda(q)) = q.  good(q): q on its own descent or q <= a(q)
(a(q) = descent element at index h(top)).  Branches (from d = last nonzero element of the bot-descent): a = h(d) = 2,
b = d a bad atom, g = d a good atom.  Optional Nmin=K: assume t_K != bot on the bot-descent (N >= K).

QUANTIFIER: per lattice, per branch, over ALL F of the world: a column prints SAT iff SOME F of that branch makes the
named statement FAIL (vac: SAT iff the branch has a model).  Every SAT model is decoded, completed (rows of non-low
elements = top) and REPLAYED in Python from the definitions (rstages.stages for the world; Rep for the statement) before
it is counted; a mismatch aborts.  Statements (each 'fails' = SAT):
  main mode, world full:
  TopExit        off g: some m in M2 exits with c(m) <= m                                     (the open target)
  M:MaxIdx2      off g: some m in M2 of maximal landing index among M2 does so     (refuted relative of TopExit, s282)
  OneFix         exactly one atom of Z is mu-fixed                                             (LEAD)
  AtMost1Fix     at most one atom of Z is mu-fixed                                             (LEAD, uniqueness half)
  M:OneGood      at most one atom of Z is good                                    (refuted relative of OneFix, s282)
  FixMax         off g: every mu-fixed atom lies below some m in M2                (audit: TopExit <=> CertAtom off g)
  M:GoodNonMax   off g: every good atom lies below some m in M2                    (refuted relative of FixMax, s282)
  GoodToFix      every good atom is mu-fixed or exits to a mu-fixed atom         (audit: GoodAtom1 <=> CertAtom)
  M:GoodFix      every good atom is mu-fixed                                       (refuted relative of GoodToFix, s282)
  bside mode: TopExit (off g) in worlds full / desc2 (candidate DescTb2) / noTb2 (refuted relative, section 283).
  Options: Nmin=K (assume N >= K); maxn=X (skip lattices with |L| > X; reported); budget=C (conflict budget per solve,
  default 0 = unlimited; an exhausted budget prints 'undec' = undecided, which is silent, never UNSAT).
  Per lattice the tester prints one progress line per solve (name, result, seconds) and a summary line.
  B=1 (main mode): also run the bside block (TopExit in worlds full, desc2, noTb2, desc12, noTb1, with NOV columns).
  python3 probe15.py (main | bside | selfcheck) (tall K M SEED CNT | closure K M SEED CNT | file PATH...) [Nmin=K] [maxn=X] [budget=C]"""
import sys, collections, itertools, json, time, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, '/home/user/mordor/experiments/separation'); sys.path.insert(0, '/home/user/mordor/experiments/amalgamation')
sys.path.insert(0, HERE)
from pysat.solvers import Cadical153
from tight_probe import lattices
from rstages import stages, a_of
from w0lean import Rep

def width(L):
    n = L.n; lt = [[L.le[i][j] and i != j for j in range(n)] for i in range(n)]; match = [-1] * n
    def aug(u, seen):
        for v in range(n):
            if lt[u][v] and not seen[v]:
                seen[v] = True
                if match[v] < 0 or aug(match[v], seen): match[v] = u; return True
        return False
    return n - sum(aug(u, [False] * n) for u in range(n))

class W:
    def __init__(s, L, nmin=0):
        s.L = L; n = L.n; le = L.le; h = L.rank; s.n = n; bot = L.bot; top = L.top
        s.V = {}; S = s.S = Cadical153(); s.R = R = [x for x in range(n) if h[x] <= 2]
        s.atoms = [x for x in R if h[x] == 1]; s.h2 = [x for x in R if h[x] == 2]; s.NO = NO = h[top]
        f = s.f; add = S.add_clause
        for x in R:
            for y in range(n):
                ls = [f(x, y, v) for v in range(n)]; add(ls)
                for a_, b_ in itertools.combinations(ls, 2): add([-a_, -b_])
        for x in R:
            for y in range(n):
                for y2 in L.covers_up[y]:
                    for v in range(n): add([-f(x, y, v)] + [f(x, y2, w) for w in range(n) if le[v][w]])
                for x2 in L.covers_up[x]:
                    if x2 not in R: continue
                    for v in range(n): add([-f(x, y, v)] + [f(x2, y, w) for w in range(n) if le[v][w]])
        Z = s.Z = lambda y: f(bot, y, bot)
        for y in range(n):                                   # a(bot) = bot
            if y == bot: continue
            for v in range(n):
                if le[y][v]: add([-f(bot, y, v)])
        s.gF = s.v('gF'); s.gD = s.v('gD'); s.gFA = s.v('gFA'); s.gDA = s.v('gDA')                   # world selectors (lower half at height-2 rows)
        for x in R:                                          # (T) at every row of Z
            for y in range(n):
                if h[y] <= 2: continue
                for v in range(n):
                    if le[y][v]: add([-Z(x), -f(x, y, v)])                       # Ta (upper half): all rows
                    elif le[v][x]:
                        if h[x] == 2: add([-s.gF, -Z(x), -f(x, y, v)])           # Tb at height-2 rows: selector gF
                        elif h[x] == 1: add([-s.gFA, -Z(x), -f(x, y, v)])        # Tb at atom rows: selector gFA
                        else: add([-Z(x), -f(x, y, v)])                          # Tb at row bot: always
        add([Z(y) for y in s.h2])                            # n1
        it = s.it = lambda x, j, z: s.v('it', x, j, z)
        for x in R:
            for z in range(n): add([it(x, 0, z)] if z == top else [-it(x, 0, z)])
            for j in range(NO):
                for z in range(n):
                    for w in range(n): add([-it(x, j, z), -f(x, z, w), it(x, j + 1, w)])
                for w, w2 in itertools.combinations(range(n), 2): add([-it(x, j + 1, w), -it(x, j + 1, w2)])
        for x in s.h2 + s.atoms:                             # descent form of Tb: F(x, t) not<= x for HIGH t on row x's descent
            g = s.gD if h[x] == 2 else s.gDA
            for j in range(NO):
                for z in range(n):
                    if h[z] <= 2: continue
                    for v in range(n):
                        if le[v][x]: add([-g, -Z(x), -it(x, j, z), -f(x, z, v)])
        s.nov = {}                                           # novelty: some row of Z of height k has a high lower cell
        for k in (1, 2):
            s.nov[k] = s.OR(('nov', k), [s.AND(('novx', x, y, v), [Z(x), f(x, y, v)]) for x in (s.atoms if k == 1 else s.h2)
                                         for y in range(n) if h[y] > 2 for v in range(n) if le[v][x]])
        s.lowat = {}; s.li = {}; s.land = {}
        for x in R:
            for j in range(NO + 1): s.lowat[x, j] = s.OR(('lowat', x, j), [it(x, j, z) for z in R])
            for j in range(NO + 1):
                s.li[x, j] = s.AND(('li', x, j), [s.lowat[x, j]] + [-s.lowat[x, j2] for j2 in range(j)])
            for p in R: s.land[x, p] = s.OR(('land', x, p), [s.AND(('lj', x, j, p), [s.li[x, j], it(x, j, p)]) for j in range(NO + 1)])
        for x in R: add([-Z(x)] + [s.land[x, p] for p in R])  # every row of Z lands (implied by Ta in all three worlds)
        s.ext = {}; s.inl = {}; s.C = {}
        for x in R:
            for c in s.atoms: s.ext[x, c] = s.OR(('ext', x, c), [s.AND(('extp', x, p, c), [s.land[x, p], f(bot, p, c)]) for p in s.h2])
            s.inl[x] = s.OR(('inl', x), [s.AND(('inlp', x, p), [s.land[x, p], Z(p)]) for p in R])
            s.C[x] = s.AND(('C', x), [Z(x), s.OR(('Cx', x), [s.ext[x, c] for c in s.atoms if le[c][x]])]) if x != bot else None
        s.D = {z: s.OR(('D', z), [s.AND(('Dj', z, j), [it(bot, j, z), it(bot, j + 1, bot)]) for j in range(NO)]) for z in R if z != bot}
        s.good = {q: s.OR(('good', q), [it(q, j, q) for j in range(NO + 1)] + [it(q, NO, v) for v in range(n) if le[q][v]]) for q in s.atoms}
        s.hd2 = s.OR(('hd2',), [s.D[z] for z in s.h2])
        s.dgood = s.OR(('dgood',), [s.AND(('dg', q), [s.D[q], s.good[q]]) for q in s.atoms])
        s.brl = {'a': [s.hd2], 'b': [-s.hd2, -s.dgood], 'g': [-s.hd2, s.dgood]}
        s.nmin = []
        if nmin:
            if nmin > NO: s.nmin = None
            else: s.nmin = [s.OR(('nmin',), [it(bot, nmin, z) for z in range(n) if z != bot])]
    def v(s, *k):
        if k not in s.V: s.V[k] = len(s.V) + 1
        return s.V[k]
    def f(s, x, y, w): return s.v('f', x, y, w)
    def OR(s, key, ls):
        o = s.v(*key)
        for l in ls: s.S.add_clause([o, -l])
        s.S.add_clause([-o] + list(ls)); return o
    def AND(s, key, ls):
        o = s.v(*key)
        for l in ls: s.S.add_clause([-o, l])
        s.S.add_clause([o] + [-l for l in ls]); return o
    def decode(s):
        M = set(l for l in s.S.get_model() if l > 0); n = s.n; L = s.L
        F = [[L.top] * n for _ in range(n)]
        for x in s.R:
            for y in range(n): F[x][y] = next(w for w in range(n) if s.f(x, y, w) in M)
        return F
    def fix_lits(s, F):                                    # selfcheck: pin F completely (no search freedom)
        return [s.f(x, y, F[x][y]) for x in s.R for y in range(s.n)]

def queries(s):
    L = s.L; le = L.le; bot = L.bot; add = s.S.add_clause; NO = s.NO; Q = {}
    fixq = {q: s.AND(('fixq', q), [s.Z(q), s.ext[q, q]]) for q in s.atoms}
    gq = {q: s.AND(('gq', q), [s.Z(q), s.good[q]]) for q in s.atoms}
    bm2 = {q: s.OR(('bm2', q), [s.Z(m) for m in s.h2 if le[q][m]]) for q in s.atoms}
    def act(name): a = s.v('act', name); Q[name] = a; return a
    a = act('TopExit')
    for m in s.h2: add([-a, -s.C[m]])
    lj2 = {j: s.OR(('lj2', j), [s.AND(('zli2', m, j), [s.Z(m), s.li[m, j]]) for m in s.h2]) for j in range(NO + 1)}
    I = {j: s.AND(('I2', j), [lj2[j]] + [-lj2[j2] for j2 in range(j + 1, NO + 1)]) for j in lj2}
    a = act('M:MaxIdx2')
    for m in s.h2:
        X = s.AND(('X2', m), [s.Z(m), s.OR(('X2o', m), [s.AND(('X2j', m, j), [I[j], s.li[m, j]]) for j in I])])
        add([-a, -X, -s.C[m]])
    two = lambda tag, P: [s.AND((tag, q1, q2), [P[q1], P[q2]]) for q1, q2 in itertools.combinations(s.atoms, 2)]
    nofix = s.AND(('nofix',), [-fixq[q] for q in s.atoms])
    a = act('OneFix'); add([-a, nofix] + two('fx2', fixq))
    a = act('AtMost1Fix'); add([-a] + two('fx2b', fixq))
    a = act('M:OneGood'); add([-a] + two('gq2', gq))
    a = act('FixMax'); add([-a] + [s.AND(('fm', q), [fixq[q], -bm2[q]]) for q in s.atoms])
    a = act('M:GoodNonMax'); add([-a] + [s.AND(('gnm', q), [gq[q], -bm2[q]]) for q in s.atoms])
    exfix = {q: s.OR(('exfix', q), [s.AND(('exf', q, c), [s.ext[q, c], fixq[c]]) for c in s.atoms]) for q in s.atoms}
    a = act('GoodToFix'); add([-a] + [s.AND(('g2f', q), [gq[q], -fixq[q], -exfix[q]]) for q in s.atoms])
    a = act('M:GoodFix'); add([-a] + [s.AND(('gf', q), [gq[q], -fixq[q]]) for q in s.atoms])
    return Q

OFFG = {'TopExit', 'M:MaxIdx2', 'FixMax', 'M:GoodNonMax'}
def worlds(w):   # (name, selector assumptions, novelty literal that must be satisfiable for the relaxation to be new)
    return [('full', [w.gF, w.gFA], None), ('desc2', [w.gD, w.gFA], w.nov[2]), ('noTb2', [w.gFA], w.nov[2]),
            ('desc12', [w.gD, w.gDA], w.nov[1]), ('noTb1', [w.gF], w.nov[1])]

def check(r, name):
    """Python replay from the definitions: True iff the decoded model really makes `name` FAIL."""
    le = r.L.le; h = r.L.rank
    top2 = [m for m in r.Zs if h[m] == 2]
    fx = [q for q in r.atoms if r.fixed(q)]; gd = [q for q in r.atoms if r.good(q)]
    bm2 = lambda q: any(le[q][m] for m in top2)
    if name == 'TopExit': return not any(r.cert(m) for m in top2)
    if name == 'M:MaxIdx2':
        I = {m: r.li(m) for m in top2}; t = max(I.values()); return not any(r.cert(m) for m in top2 if I[m] == t)
    if name == 'OneFix': return len(fx) != 1
    if name == 'AtMost1Fix': return len(fx) >= 2
    if name == 'M:OneGood': return len(gd) >= 2
    if name == 'FixMax': return any(not bm2(q) for q in fx)
    if name == 'M:GoodNonMax': return any(not bm2(q) for q in gd)
    if name == 'GoodToFix': return any(not r.fixed(q) and not (r.exits(q) and r.fixed(r.c(q))) for q in gd)
    if name == 'M:GoodFix': return any(not r.fixed(q) for q in gd)
    raise ValueError(name)

def brof(rep): return {'exit-a': 'a', 'in-a': 'a', 'exit-b': 'b', 'in-b': 'b', 'g': 'g'}[rep.br]

def coords(L, F):
    rep = Rep(L, F); tb = rep.desc(L.bot); N = tb.index(rep.d)
    return rep, f'N={N} |A|={len(rep.atoms)} |M2|={sum(1 for m in rep.Zs if L.rank[m] == 2)} fix={sum(1 for q in rep.atoms if rep.fixed(q))}'

def replay_world(L, F, world):
    """Python check of a world from the definitions: a(bot) = bot, Z heights <= 2, n1, Ta at every row of Z, Tb at row bot,
    and Tb at atom rows / height-2 rows of Z in full or descent form (or not at all) as the world says."""
    n = L.n; le = L.le; h = L.rank; bot = L.bot
    Zs = [x for x in range(n) if F[bot][x] == bot]
    if a_of(L, F, bot) != bot or any(h[z] > 2 for z in Zs) or not any(h[z] == 2 for z in Zs): return False
    form = {'full': ('full', 'full'), 'desc2': ('full', 'desc'), 'noTb2': ('full', 'none'), 'desc12': ('desc', 'desc'),
            'noTb1': ('none', 'full')}[world]
    for x in Zs:
        ds = []; v = L.top
        while v not in ds: ds.append(v); v = F[x][v]
        fm = 'full' if h[x] == 0 else form[h[x] - 1]
        for y in range(n):
            if h[y] <= 2: continue
            if le[y][F[x][y]]: return False                                   # Ta
            if le[F[x][y]][x] and (fm == 'full' or (fm == 'desc' and y in ds)): return False
    return True

def novel(L, F, k):   # some row of Z of height k has a lower cell at a high column (the relaxation is really used)
    return any(F[L.bot][x] == L.bot and L.rank[x] == k and L.le[F[x][y]][x] for x in range(L.n) for y in range(L.n) if L.rank[y] > 2)

def bside_block(w, b, SOLVE, T, best, L, idx):
    """TopExit (off g) in each world; for a relaxed world also NOV = the relaxation has a model that uses it."""
    cells = []
    for world, sel, nov in worlds(w):
        base = sel + w.brl[b] + w.nmin
        a = w.v('actTE', b)
        for m in w.h2: w.S.add_clause([-a, -w.C[m]])
        names = [('TopExit', [a])] + ([('NOV', [nov])] if nov is not None else [])
        for qn, extra in names:
            rv = SOLVE(w, base + extra, f'{b} {world} {qn}')
            key = (b, world, qn)
            if rv is None: cells.append(f'{world}:{qn}=undec'); T[key + ('undec',)][f'h{L.height}'] += 1; continue
            if not rv: cells.append(f'{world}:{qn}=uns'); T[key + ('uns',)][f'h{L.height}'] += 1; continue
            F = w.decode(); assert replay_world(L, F, world), ('world replay', world); rr = RepRel(L, F); assert rr.br == b
            if qn == 'TopExit': assert not any(rr.cert(m) for m in rr.Zs if L.rank[m] == 2), ('replay', world, b)
            else: assert novel(L, F, 1 if world in ('desc12', 'noTb1') else 2), ('novelty replay', world)
            T[key][f'h{L.height}'] += 1; cells.append(f'{world}:{qn}=SAT')
            if qn == 'TopExit' and (key not in best or L.n < best[key][0]): best[key] = (L.n, idx, dict(sets=L.S, F=F))
    return f'{b}:B[' + ' '.join(cells) + ']'

class RepRel:   # statement replay for relaxed worlds (no R-stage check; branch by own-cell goodness of d)
    def __init__(r, L, F):
        r.L = L; r.F = F; h = L.rank; bot = L.bot
        r.Z = [x for x in range(L.n) if F[bot][x] == bot]; r.Zs = [x for x in r.Z if x != bot]
        bd = r.desc(bot); r.d = [v for v in bd if v != bot][-1]
        r.br = 'a' if h[r.d] == 2 else ('g' if r.good(r.d) else 'b')
    def desc(r, x):
        v = r.L.top; s = []
        while v not in s: s.append(v); v = r.F[x][v]
        return s
    def lam(r, x): return next(v for v in r.desc(x) if r.L.rank[v] <= 2)
    def good(r, q): ds = r.desc(q); return q in ds or r.L.le[q][ds[-1]]
    def cert(r, x): p = r.lam(x); c = r.F[r.L.bot][p]; return c != r.L.bot and r.L.le[c][x]

if __name__ == '__main__':
    mode = sys.argv[1]; args = [a for a in sys.argv[2:] if '=' not in a]
    opt = dict(a.split('=') for a in sys.argv[2:] if '=' in a); nmin = int(opt.get('Nmin', 0))
    MAXN = int(opt.get('maxn', 10 ** 9)); BUD = int(opt.get('budget', 0))
    def SOLVE(w, assm, label):
        t = time.time()
        if BUD: w.S.conf_budget(BUD); res = w.S.solve_limited(assumptions=assm)
        else: res = w.S.solve(assumptions=assm)
        print(f'    {label}: {"SAT" if res else ("UNSAT" if res is False else "undec")} {time.time() - t:.0f}s', flush=True)
        return res
    if mode == 'selfcheck':                                  # encoding vs Python on stored models, F pinned: no search
        sys.path.insert(0, HERE); import bankx, bank
        idx = json.load(open(os.path.join(bank.BANK, 'index.json'))); bad = 0; cnt = 0
        for e in idx:
            for mf in bank.models(e):
                m = bank.M(mf['sets'], mf['F'])
                if not m.w0: continue
                L = m.L; F = mf['F']; w = W(L); Q = queries(w); pin = w.fix_lits(F) + [w.gF, w.gFA]
                rep = Rep(L, F); b = brof(rep); cnt += 1
                assert w.S.solve(assumptions=pin + w.brl[b]), ('pinned model rejected by the world encoding', e['file'])
                for name, a in Q.items():
                    if b == 'g' and name in OFFG: continue
                    enc = w.S.solve(assumptions=pin + w.brl[b] + [a]); py = check(rep, name)
                    if enc != py: bad += 1; print('MISMATCH', e['file'], name, enc, py)
                w.S.delete()
        print(f'selfcheck: {cnt} banked W0 models, every query compared with its Python replay (F pinned, no search): {bad} mismatches'); sys.exit()
    print(f'probe15 {mode} | corpus {args} {opt} | per lattice (height >= 3) and branch a/b/g, over ALL F: vac = SAT iff the branch'
          f' has a model; every other column = SAT iff SOME F makes the named statement FAIL (docstring); SAT models replayed', flush=True)
    T = collections.defaultdict(collections.Counter); best = {}; t0 = time.time(); tag = '_'.join(a.split('/')[-1] for a in args)
    for idx, L in enumerate(lattices(args)):
        if L.height < 3: continue
        if L.n > MAXN: print(f'lattice {idx} n={L.n}: skipped (maxn={MAXN})', flush=True); continue
        print(f'lattice {idx} n={L.n} h={L.height}: start', flush=True)
        t1 = time.time(); w = W(L, nmin)
        if w.nmin is None: print(f'lattice {idx}: Nmin > h(top), skipped'); continue
        row = []
        if mode == 'main':
            Q = queries(w)
            for b in 'abg':
                base = [w.gF, w.gFA] + w.brl[b] + w.nmin
                rv = SOLVE(w, base, f'{b} vac')
                if rv is None: row.append(f'{b}:vac=undec'); continue
                if not rv: row.append(f'{b}:-'); continue
                rep, cc = coords(L, w.decode()); assert rep.world and brof(rep) == b, ('vac replay', b)
                T[(b, 'vac')][f'h{L.height}'] += 1; cells = [f'vac({cc})']
                for name, a in Q.items():
                    if b == 'g' and name in OFFG: continue
                    rv = SOLVE(w, base + [a], f'{b} {name}')
                    if rv is None: cells.append(f'{name}=undec'); T[(b, name + ':undec')][f'h{L.height}'] += 1; continue
                    if rv:
                        rep, cc = coords(L, w.decode()); assert rep.world and brof(rep) == b and check(rep, name), ('replay', b, name)
                        T[(b, name)][f'h{L.height}'] += 1; cells.append(f'{name}=SAT({cc})')
                        if (b, name) not in best or L.n < best[b, name][0]: best[b, name] = (L.n, idx, dict(sets=L.S, F=rep.F))
                    else: cells.append(f'{name}=uns'); T[(b, name + ':uns')][f'h{L.height}'] += 1
                row.append(f'{b}:[' + ' '.join(cells) + ']')
            if opt.get('B') == '1':
                for b in 'ab': row.append(bside_block(w, b, SOLVE, T, best, L, idx))
        elif mode == 'bside':
            for b in 'ab': row.append(bside_block(w, b, SOLVE, T, best, L, idx))
        print(f'lattice {idx} n={L.n} h={L.height} width={width(L)} {time.time() - t1:.0f}s | ' + ' '.join(row), flush=True)
        w.S.delete()
    print(f'== totals: lattices per (branch, column), SAT unless marked :uns ({time.time() - t0:.0f}s)')
    for k, c in sorted(T.items()): print(f'  {k} {dict(c)}')
    for k, (nn, idx, mdl) in sorted(best.items()):
        print(f'  smallest SAT {k}: |L| = {nn} (lattice {idx})')
        json.dump(mdl, open(os.path.join(HERE, f'm15_{mode}_{tag}_{"_".join(k).replace(":", "")}_min{nn}.json'), 'w'))
