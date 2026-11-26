"""ctlA (run-13 control briefer A) -- lean exact encoding of the level-1 world W0 + n1, independent of muorbit_sat.py.

World (equivalent to W0 + n1 when h(top) >= 3; see brief, section 'Frontier'):
  rows only for low elements x (h(x) <= 2); F(x, .) one-hot, monotone in x (covers inside the low set) and in y;
  Z(y) := [F(bot, y) = bot];  (A) a(bot) = bot: no y > bot with y <= F(bot, y);
  (T) for every x in Z and every y with h(y) >= 3: F(x, y) not<= x and y not<= F(x, y)  (this includes Z <= low);
  n1: some element of height 2 is in Z.   Rows of non-low elements are irrelevant (set to top in the replay).
Descents it(x, j, .) are exact one-hot iterates from top; lambda(x) = first element of height <= 2 on row x's descent;
li(x, j) = 'lambda(x) is reached at index j'. Exit: lambda(x) not in Z, c(x) = F(bot, lambda(x)) (an atom).
mu(x) = lambda(x) if lambda(x) in Z else c(x).  d = last nonzero element of the bot-descent.  Cert(x): x in Z*, x exits, c(x) <= x.
Branches (assumption literals): exit-a / in-a (h(d) = 2, d exits / steps in), exit-b / in-b (d a bad atom), g (d a good atom).
Every query is 'SAT = the named statement FAILS on this lattice and branch'. Every SAT model is replayed in Python from the
definitions (stages of R computed by rstages.stages on the completed F) before it is counted.
Modes and queries (each prints its quantifier):
  lead     MaxIdx   (SAT = no row of Z* of MAXIMAL landing index exits with c(x) <= x)
           MaxRow   (SAT = no maximal element of Z exits with c(x) <= x)
           M:MinIdx (mutant; SAT = no row of Z* of MINIMAL landing index exits with c(x) <= x)
           M:MaxAll (mutant; SAT = some row of Z* of maximal landing index exits with c(x) not<= x)
           M:RowAll (mutant; SAT = some maximal element of Z exits with c(x) not<= x)
  orbitdom OrbitDom (SAT = d in-steps to e in Z and e in-steps (L2 fails), or the first exiting point z of the chain from d
                     exits to q and no row x2 in Z* with q <= x2 exits to q)
           M:ExitDom (mutant, anchor dropped; SAT = some x in Z* exits to q and no row x2 in Z* with q <= x2 exits to q)
  p2       DLGood   (SAT = every atom q in Z with DL(bot, q) is bad)
           AtomOrb  (SAT = some atom of Z has a mu-orbit that never meets a fixed point of mu)
           M:BelowD (mutant; SAT = every atom below d is bad)
           M:ZOrb   (mutant = MuLoop; SAT = some x in Z* has a mu-orbit that never meets a fixed point)
  python3 w0lean.py MODE (sweep N MAX | closure K M SEED CNT) [only=i,j,...] [skip=h]   (run from experiments/amalgamation)"""
import sys, collections, itertools, json, time
sys.path.insert(0, '/home/user/mordor/experiments/separation'); sys.path.insert(0, '/home/user/mordor/experiments/amalgamation')
from pysat.solvers import Cadical153
from tight_probe import lattices
from rstages import stages, a_of

BR = ['exit-a', 'in-a', 'exit-b', 'in-b', 'g']

class W:
    def __init__(s, L):
        s.L = L; n = L.n; le = L.le; h = L.rank; s.n = n; bot = L.bot; top = L.top
        s.V = {}; S = s.S = Cadical153(); s.R = R = [x for x in range(n) if h[x] <= 2]
        s.low = R; s.atoms = [x for x in R if h[x] == 1]; s.h2 = [x for x in R if h[x] == 2]; s.NO = NO = h[top]
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
        for y in range(n):                                   # (A)
            if y == bot: continue
            for v in range(n):
                if le[y][v]: add([-f(bot, y, v)])
        for x in R:                                          # (T) at every row of Z (includes Z <= low via x = bot)
            for y in range(n):
                if h[y] <= 2: continue
                for v in range(n):
                    if le[v][x] or le[y][v]: add([-Z(x), -f(x, y, v)])
        add([Z(y) for y in s.h2])                            # n1
        it = s.it = lambda x, j, z: s.v('it', x, j, z)
        for x in R:
            for z in range(n): add([it(x, 0, z)] if z == top else [-it(x, 0, z)])
            for j in range(NO):
                for z in range(n):
                    for w in range(n): add([-it(x, j, z), -f(x, z, w), it(x, j + 1, w)])
                for w, w2 in itertools.combinations(range(n), 2): add([-it(x, j + 1, w), -it(x, j + 1, w2)])
        s.lowat = {}; s.li = {}; s.land = {}
        for x in R:
            for j in range(NO + 1): s.lowat[x, j] = s.OR(('lowat', x, j), [it(x, j, z) for z in R])
            for j in range(NO + 1):
                s.li[x, j] = s.AND(('li', x, j), [s.lowat[x, j]] + [-s.lowat[x, j2] for j2 in range(j)])
            for p in R: s.land[x, p] = s.OR(('land', x, p), [s.AND(('lj', x, j, p), [s.li[x, j], it(x, j, p)]) for j in range(NO + 1)])
        s.ext = {}; s.inl = {}; s.C = {}; s.mu = {}
        for x in R:
            for c in s.atoms: s.ext[x, c] = s.OR(('ext', x, c), [s.AND(('extp', x, p, c), [s.land[x, p], f(bot, p, c)]) for p in s.h2])
            s.inl[x] = s.OR(('inl', x), [s.AND(('inlp', x, p), [s.land[x, p], Z(p)]) for p in R])
            s.C[x] = s.AND(('C', x), [Z(x), s.OR(('Cx', x), [s.ext[x, c] for c in s.atoms if le[c][x]])]) if x != bot else None
            for y in R:
                ls = []
                if y != bot: ls.append(s.AND(('muin', x, y), [s.land[x, y], Z(y)]))
                if y in s.atoms: ls.append(s.ext[x, y])
                s.mu[x, y] = s.OR(('mu', x, y), ls)
        s.D = {z: s.OR(('D', z), [s.AND(('Dj', z, j), [it(bot, j, z), it(bot, j + 1, bot)]) for j in range(NO)]) for z in R if z != bot}
        s.good = {}
        for q in s.atoms:
            s.good[q] = s.OR(('good', q), [it(q, j, q) for j in range(NO + 1)] + [it(q, NO, v) for v in range(n) if le[q][v]])
        s.hd2 = s.OR(('hd2',), [s.D[z] for z in s.h2])
        s.dIn = s.OR(('dIn',), [s.AND(('dInz', z), [s.D[z], s.inl[z]]) for z in s.D])
        s.dgood = s.OR(('dgood',), [s.AND(('dg', q), [s.D[q], s.good[q]]) for q in s.atoms])
        s.brl = {'exit-a': [s.hd2, -s.dIn], 'in-a': [s.hd2, s.dIn], 'exit-b': [-s.hd2, -s.dgood, -s.dIn],
                 'in-b': [-s.hd2, -s.dgood, s.dIn], 'g': [-s.hd2, s.dgood]}
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

# ---------------- Python replay from the definitions ----------------
class Rep:
    def __init__(r, L, F):
        r.L = L; r.F = F; n = L.n; le = L.le; h = L.rank; bot = L.bot; top = L.top
        assert all(le[F[x][y]][F[x2][y2]] for x in range(n) for y in range(n) for x2 in range(n) for y2 in range(n)
                   if le[x][x2] and le[y][y2]), 'not monotone'
        st = stages(L, F); inR = lambda z, i: st[z] is not None and st[z] <= i
        r.world = (a_of(L, F, bot) == bot and all(h[z] <= 2 for z in range(n) if inR(z, 2)) and not inR(top, 2)
                   and any(h[z] > 1 for z in range(n) if inR(z, 1)))
        r.Z = [x for x in range(n) if F[bot][x] == bot]; r.Zs = [x for x in r.Z if x != bot]
        r.world = r.world and sorted(r.Z) == sorted(z for z in range(n) if inR(z, 1))
        if not r.world: return
        bd = r.desc(bot); r.d = [v for v in bd if v != bot][-1]
        r.atoms = [q for q in r.Z if h[q] == 1]
        hd2 = h[r.d] == 2; dIn = F[bot][r.lam(r.d)] == bot; dgood = h[r.d] == 1 and r.good(r.d)
        r.br = ('in-a' if dIn else 'exit-a') if hd2 else ('g' if dgood else ('in-b' if dIn else 'exit-b'))
    def desc(r, x):
        v = r.L.top; s = []
        while v not in s: s.append(v); v = r.F[x][v]
        return s
    def lam(r, x): return next(v for v in r.desc(x) if r.L.rank[v] <= 2)
    def li(r, x): return next(j for j, v in enumerate(r.desc(x)) if r.L.rank[v] <= 2)
    def exits(r, x): return r.F[r.L.bot][r.lam(x)] != r.L.bot
    def c(r, x): return r.F[r.L.bot][r.lam(x)]
    def cert(r, x): return x != r.L.bot and r.exits(x) and r.L.le[r.c(x)][x]
    def mu(r, x): return r.c(x) if r.exits(x) else r.lam(x)
    def fixed(r, x): return r.mu(x) == x
    def good(r, q): ds = r.desc(q); return q in ds or r.L.le[q][ds[-1]]
    def orbit_hits_fixed(r, x):
        seen = []
        while x not in seen:
            if r.fixed(x): return True
            seen.append(x); x = r.mu(x)
        return False
    def dl(r, q): L = r.L; return all(L.le[y][q] for y in range(L.n) if L.le[y][r.F[L.bot][L.join[q][y]]])

def queries(W_, mode):
    s = W_; L = s.L; le = L.le; bot = L.bot; R = s.R; add = s.S.add_clause; NO = s.NO; Q = {}
    if mode == 'lead':
        lj = {j: s.OR(('lj', j), [s.AND(('zli', x, j), [s.Z(x), s.li[x, j]]) for x in R if x != bot]) for j in range(NO + 1)}
        Imax = {j: s.AND(('Imax', j), [lj[j]] + [-lj[j2] for j2 in range(j + 1, NO + 1)]) for j in lj}
        Imin = {j: s.AND(('Imin', j), [lj[j]] + [-lj[j2] for j2 in range(j)]) for j in lj}
        Xmax = {x: s.AND(('Xmax', x), [s.Z(x), s.OR(('Xmax1', x), [s.AND(('Xm', x, j), [Imax[j], s.li[x, j]]) for j in lj])]) for x in R if x != bot}
        Xmin = {x: s.AND(('Xmin', x), [s.Z(x), s.OR(('Xmin1', x), [s.AND(('Xn', x, j), [Imin[j], s.li[x, j]]) for j in lj])]) for x in R if x != bot}
        maxZ = {x: s.AND(('maxZ', x), [s.Z(x)] + [-s.Z(y) for y in R if y != x and le[x][y]]) for x in R if x != bot}
        for name, X in (('MaxIdx', Xmax), ('MaxRow', maxZ), ('M:MinIdx', Xmin)):
            a = s.v('act', name); Q[name] = a
            for x in X: add([-a, -X[x], -s.C[x]])
        for name, X in (('M:MaxAll', Xmax), ('M:RowAll', maxZ)):
            a = s.v('act', name); Q[name] = a; sel = []
            for x in X:
                for c in s.atoms:
                    if le[c][x]: continue
                    o = s.v('sel', name, x, c); sel.append(o); add([-o, X[x]]); add([-o, s.ext[x, c]])
            add([-a] + sel)
    elif mode == 'lead2':
        lj = {j: s.OR(('lj', j), [s.AND(('zli', x, j), [s.Z(x), s.li[x, j]]) for x in R if x != bot]) for j in range(NO + 1)}
        Imax = {j: s.AND(('Imax', j), [lj[j]] + [-lj[j2] for j2 in range(j + 1, NO + 1)]) for j in lj}
        Xmax = {x: s.AND(('Xmax', x), [s.Z(x), s.OR(('Xmax1', x), [s.AND(('Xm', x, j), [Imax[j], s.li[x, j]]) for j in lj])]) for x in R if x != bot}
        maxZ = {x: s.AND(('maxZ', x), [s.Z(x)] + [-s.Z(y) for y in R if y != x and le[x][y]]) for x in R if x != bot}
        top2 = {x: s.Z(x) for x in s.h2}
        nonmax = {x: s.AND(('nonmax', x), [s.Z(x), -maxZ[x]]) for x in R if x != bot}
        for name, X in (('MaxRow', maxZ), ('MaxRow2', top2), ('M:MaxIdx', Xmax), ('M:NonMax', nonmax)):
            a = s.v('act', name); Q[name] = a
            for x in X: add([-a, -X[x], -s.C[x]])
        a = s.v('act', 'M:RowAll'); Q['M:RowAll'] = a; sel = []
        for x in maxZ:
            for c in s.atoms:
                if le[c][x]: continue
                o = s.v('sel', 'RowAll', x, c); sel.append(o); add([-o, maxZ[x]]); add([-o, s.ext[x, c]])
        add([-a] + sel)
    elif mode == 'final':
        fixq = {q: s.AND(('fixq', q), [s.Z(q), s.ext[q, q]]) for q in s.atoms}
        isex = {q: s.OR(('isex', q), [s.AND(('isexx', x, q), [s.Z(x), s.ext[x, q]]) for x in R if x != bot]) for q in s.atoms}
        tc = {}
        for m in s.h2:
            ls = []
            for p in s.h2:
                q = L.meet[m][p]
                if p == m or L.rank[q] != 1: continue
                cell = s.OR(('cell', q, p), [s.f(q, p, w) for w in range(L.n) if le[q][w]])
                ls.append(s.AND(('tcp', m, p), [s.land[m, p], cell]))
            tc[m] = s.AND(('tc', m), [s.Z(m), s.OR(('tc1', m), ls)])
        a = s.v('act', 'TopCell'); Q['TopCell'] = a
        for m in s.h2: add([-a, -tc[m]])
        a = s.v('act', 'TopCert'); Q['TopCert'] = a
        for m in s.h2: add([-a, -s.C[m]])
        a = s.v('act', 'UpFix'); Q['UpFix'] = a; sel = []
        for name, base in (('UpFix', fixq), ('M:UpExit', isex)):
            if name == 'M:UpExit': a = s.v('act', name); Q[name] = a; sel = []
            for q in s.atoms:
                for m in R:
                    if m == bot or m == q or not le[q][m]: continue
                    o = s.v('up', name, q, m); sel.append(o)
                    for lit in (base[q], s.Z(m), -s.ext[m, q]): add([-o, lit])
            add([-a] + sel)
        a = s.v('act', 'M:TopCellD'); Q['M:TopCellD'] = a
        for m in s.h2:
            for z in s.D:
                if le[z][m]: add([-a, -s.D[z], -tc[m]])
        a = s.v('act', 'M:TopCellAll'); Q['M:TopCellAll'] = a; sel = []
        for m in s.h2:
            o = s.v('tca', m); sel.append(o); add([-o, s.Z(m)]); add([-o, -tc[m]])
        add([-a] + sel)
    elif mode == 'orbitdom':
        exto = {(x2, q): s.AND(('exto', x2, q), [s.Z(x2), s.ext[x2, q]]) for x2 in R if x2 != bot for q in s.atoms if le[q][x2]}
        zf = {z: s.OR(('zf', z), [s.D[z]] + [s.AND(('zfin', dd, z), [s.D[dd], s.land[dd, z], s.Z(z)]) for dd in s.D]) for z in R if z != bot}
        for name in ('OrbitDom', 'M:ExitDom'):
            a = s.v('act', name); Q[name] = a; sel = []
            if name == 'OrbitDom':
                for dd in s.D:
                    for e in R:
                        if e == bot: continue
                        o = s.v('l2f', dd, e); sel.append(o)
                        for lit in (s.D[dd], s.land[dd, e], s.Z(e), s.inl[e]): add([-o, lit])
            for z in R:
                if z == bot: continue
                for q in s.atoms:
                    o = s.v('sz', name, z, q); sel.append(o)
                    add([-o, zf[z] if name == 'OrbitDom' else s.Z(z)]); add([-o, s.Z(z)]); add([-o, s.ext[z, q]])
                    for x2 in R:
                        if (x2, q) in exto: add([-o, -exto[x2, q]])
            add([-a] + sel)
    elif mode == 'p2':
        dl = {}
        for q in s.atoms:
            o = s.v('dl', q); viol = []
            for y in range(L.n):
                if le[y][q]: continue
                for w in range(L.n):
                    if le[y][w]: viol.append(s.f(bot, L.join[q][y], w))
            for t in viol: add([-o, -t])
            add([o] + viol); dl[q] = o
        a = s.v('act', 'DLGood'); Q['DLGood'] = a
        for q in s.atoms: add([-a, -s.Z(q), -dl[q], -s.good[q]])
        a = s.v('act', 'M:BelowD'); Q['M:BelowD'] = a
        for q in s.atoms:
            for z in s.D:
                if le[q][z]: add([-a, -s.D[z], -s.good[q]])
        for name in ('AtomOrb', 'M:ZOrb'):
            a = s.v('act', name); Q[name] = a; O = lambda x: s.v('O', name, x)
            add([-a, -O(bot)])
            for x in R:
                if x == bot: continue
                add([-a, -O(x), s.Z(x)]); add([-a, -O(x), -s.mu[x, x]])
                for y in R:
                    if y != bot: add([-a, -O(x), -s.mu[x, y], O(y)])
                    else: add([-a, -O(x), -s.mu[x, y]])
            add([-a] + [O(x) for x in (s.atoms if name == 'AtomOrb' else [x for x in R if x != bot])])
        maxZ = {x: s.AND(('maxZ', x), [s.Z(x)] + [-s.Z(y) for y in R if y != x and le[x][y]]) for x in R if x != bot}
        fixq = {q: s.AND(('fixq', q), [s.Z(q), s.ext[q, q]]) for q in s.atoms}
        a = s.v('act', 'FixUp'); Q['FixUp'] = a; sel = []
        for q in s.atoms:
            o = s.v('fu', q); sel.append(o); add([-o, fixq[q]])
            for m in maxZ:
                if le[q][m]: add([-o, -maxZ[m], -s.ext[m, q]])
        add([-a] + sel)
        a = s.v('act', 'M:FixUpAll'); Q['M:FixUpAll'] = a; sel = []
        for q in s.atoms:
            for m in maxZ:
                if not le[q][m]: continue
                o = s.v('fua', q, m); sel.append(o)
                for lit in (fixq[q], maxZ[m], -s.ext[m, q]): add([-o, lit])
        add([-a] + sel)
    return Q

def check(rep, mode, name):
    """Replay: True iff the model really makes statement `name` fail (SAT meaning)."""
    r = rep; le = r.L.le
    if mode == 'lead':
        I = {x: r.li(x) for x in r.Zs}; imax = max(I.values()); imin = min(I.values())
        maxZ = [x for x in r.Zs if not any(y != x and le[x][y] for y in r.Z)]
        if name == 'MaxIdx': return not any(r.cert(x) for x in r.Zs if I[x] == imax)
        if name == 'MaxRow': return not any(r.cert(x) for x in maxZ)
        if name == 'M:MinIdx': return not any(r.cert(x) for x in r.Zs if I[x] == imin)
        if name == 'M:MaxAll': return any(r.exits(x) and not le[r.c(x)][x] for x in r.Zs if I[x] == imax)
        if name == 'M:RowAll': return any(r.exits(x) and not le[r.c(x)][x] for x in maxZ)
    if mode == 'lead2':
        I = {x: r.li(x) for x in r.Zs}; imax = max(I.values())
        maxZ = [x for x in r.Zs if not any(y != x and le[x][y] for y in r.Z)]
        if name == 'MaxRow': return not any(r.cert(x) for x in maxZ)
        if name == 'MaxRow2': return not any(r.cert(x) for x in r.Zs if r.L.rank[x] == 2)
        if name == 'M:MaxIdx': return not any(r.cert(x) for x in r.Zs if I[x] == imax)
        if name == 'M:NonMax': return not any(r.cert(x) for x in r.Zs if x not in maxZ)
        if name == 'M:RowAll': return any(r.exits(x) and not le[r.c(x)][x] for x in maxZ)
    if mode == 'final':
        fx = [q for q in r.atoms if r.exits(q) and r.c(q) == q]
        exq = {r.c(x) for x in r.Zs if r.exits(x)}
        up = lambda q: [m for m in r.Zs if m != q and le[q][m]]
        exto = lambda m, q: r.exits(m) and r.c(m) == q
        top2 = [m for m in r.Zs if r.L.rank[m] == 2]
        def tcell(m):
            p = r.lam(m); q = r.L.meet[m][p]
            return r.L.rank[p] == 2 and p != m and r.L.rank[q] == 1 and le[q][r.F[q][p]]
        if name == 'TopCell': return not any(tcell(m) for m in top2)
        if name == 'TopCert': return not any(r.cert(m) for m in top2)
        if name == 'UpFix': return any(not exto(m, q) for q in fx for m in up(q))
        if name == 'M:UpExit': return any(not exto(m, q) for q in exq for m in up(q))
        if name == 'M:TopCellD': return not any(tcell(m) for m in top2 if le[r.d][m])
        if name == 'M:TopCellAll': return any(not tcell(m) for m in top2)
    if mode == 'orbitdom':
        ex = {x: r.c(x) for x in r.Zs if r.exits(x)}
        nodom = lambda q: not any(ex.get(x2) == q and le[q][x2] for x2 in ex)
        if name == 'M:ExitDom': return any(nodom(q) for q in ex.values())
        d = r.d
        if d in ex: return nodom(ex[d])
        e = r.lam(d)
        if e not in ex: return True                         # L2 fails (e in Z* and e steps in)
        return nodom(ex[e])
    if mode == 'p2':
        if name == 'DLGood': return not any(r.dl(q) and r.good(q) for q in r.atoms)
        if name == 'M:BelowD': return not any(r.good(q) for q in r.atoms if le[q][r.d])
        if name == 'AtomOrb': return any(not r.orbit_hits_fixed(q) for q in r.atoms)
        if name == 'M:ZOrb': return any(not r.orbit_hits_fixed(x) for x in r.Zs)
        maxZ = [x for x in r.Zs if not any(y != x and le[x][y] for y in r.Z)]
        fx = [q for q in r.atoms if r.exits(q) and r.c(q) == q]
        exto = lambda m, q: r.exits(m) and r.c(m) == q
        if name == 'FixUp': return any(not any(exto(m, q) for m in maxZ if le[q][m]) for q in fx)
        if name == 'M:FixUpAll': return any(not exto(m, q) for q in fx for m in maxZ if le[q][m])
    raise ValueError(name)

if __name__ == '__main__':
    mode = sys.argv[1]; args = [a for a in sys.argv[2:] if '=' not in a]
    opt = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
    only = set(int(i) for i in opt['only'].split(',')) if 'only' in opt else None
    print(f'w0lean {mode} | corpus {args} | per lattice of height >= 3 and per branch: vac (SAT = the branch of W0+n1 has a model);'
          f' every other column: SAT = the named statement FAILS there (see docstring)', flush=True)
    T = collections.defaultdict(collections.Counter); best = {}; t0 = time.time()
    for idx, L in enumerate(lattices(args)):
        if L.height < 3 or (only is not None and idx not in only): continue
        t1 = time.time(); w = W(L); Q = queries(w, mode); row = []
        for b in BR:
            hv = w.S.solve(assumptions=w.brl[b])
            if not hv: row.append(f'{b}:-'); continue
            rep = Rep(L, w.decode()); assert rep.world and rep.br == b, ('vac replay', b, rep.world, rep.br)
            T[(b, 'vac')][f'h{L.height}'] += 1; cells = []
            for name, a in Q.items():
                if w.S.solve(assumptions=w.brl[b] + [a]):
                    rep = Rep(L, w.decode()); assert rep.world and rep.br == b and check(rep, mode, name), ('replay', b, name)
                    T[(b, name)][f'h{L.height}'] += 1; cells.append(f'{name}=SAT')
                    if (b, name) not in best or L.n < best[b, name][0]: best[b, name] = (L.n, idx, dict(sets=L.S, F=rep.F))
                else: cells.append(f'{name}=uns')
            row.append(f'{b}:[' + ' '.join(cells) + ']')
        print(f'lattice {idx} n={L.n} h={L.height} {time.time() - t1:.0f}s | ' + ' '.join(row), flush=True)
        w.S.delete()
    print(f'== totals (lattices with a SAT, by height), {time.time() - t0:.0f}s')
    for (b, name), c in sorted(T.items()): print(f'  {b:7s} {name:10s} {dict(c)}')
    for (b, name), (nn, idx, mdl) in sorted(best.items()):
        if name == 'vac': continue
        print(f'  smallest SAT {b} {name}: |L| = {nn} (lattice {idx})')
        json.dump(mdl, open(f'/tmp/claude-0/-home-user/3b6fdd2c-c95c-5c07-b47c-6ae28c687a4c/scratchpad/amr_run13/ctlA/m_{mode}_{name.replace(":", "")}_{b}_min{nn}.json', 'w'))
