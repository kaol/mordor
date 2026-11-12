"""Partial models for the end cases of relay descent (log §34.3z¹⁴⁶).

Lean `RelayDescent.relay_descends`: every relay column u descends to one whose meet update w = u ⊓ F(a, u) is
terminal (w ∈ D) or a private seed. Can either end case occur when witness-freeness holds on all columns y ≤ u
(the only columns the relay lemmas use)? SAT over a fixed finite lattice: F (one-hot, monotone), D (down-set of
height ≤ 2), one-hot choices of s, a, b, u; s an atom below the distinct D-maximal a, b with a ⊓ b = s; a isolated
with centre s; relay at u; the chosen end case; witness-freeness for all x ∈ D and all y ∉ D with y ≤ u.
Option 'nearcell': also require the near-cell of BottomMaxCell.near_cell_of_atomic_over at the private seed p
(some x ∈ {p, a}, y ∉ D, p < y, y ≤ p ⊔ F(x, y), y ≰ F(x, y)) together with witness-freeness at that column y.
Option 'global': witness-freeness at every column (then UNSAT by the finite Cut Lemma: a control).
Option 'named:u,w,v,t': witness-freeness only at the named columns (t = u ⊔ v); 'botdown': in addition
F(⊥, y) ≠ ⊥ for every y ∉ D below u ⊔ v (the bottom row's lower half only); 'pj=all|D|s': also the joins p ⊔ q ≤ u ⊔ v of atoms (all atoms /
points of D / one of them the centre s); 'sv': also every column of [s, F(a, u)].
Option 'forest': D is a star forest. Option 'orbit=K': u is the K-th value of the F(⊥, ·)-orbit of ⊤, every orbit value
up to u lies outside D and carries witness-freeness. Option 'rows=K': witness-freeness along the first K values of
the ⊤-orbits of F(s, ·), F(a, ·), F(b, ·).
Options 'updown' / 'join': witness-freeness at columns ≤ u or ≤ v = F(a, u) / at columns ≤ u ⊔ v.
Options 'interval' / 'two': witness-freeness only at columns in [w, u] / at the two columns w, u.
Every model is decoded and checked in Python.
  python3 relay_probe.py (terminal | seed) [nearcell] [global] (sweep P NMAX | closure K M SEED COUNT)
"""
import sys, itertools, random, collections
from pysat.solvers import Cadical153
sys.path.insert(0, '../separation'); sys.path.insert(0, '../amalgamation')
import separator_stages as ss

class Enc:
    def __init__(self, L):
        self.L = L; self.n = L.n; self.vars = {}; self.nv = 0; self.S = Cadical153()
    def v(self, *k):
        if k not in self.vars: self.nv += 1; self.vars[k] = self.nv
        return self.vars[k]
    def cl(self, c): self.S.add_clause(c)
    def onehot(self, name):
        lits = [self.v(name, e) for e in range(self.n)]; self.cl(lits)
        for p, q in itertools.combinations(lits, 2): self.cl([-p, -q])
        return lambda e: self.v(name, e)
    def iff_or(self, o, lits):
        for l in lits: self.cl([o, -l])
        self.cl([-o] + list(lits))
    def iff_and(self, o, lits):
        for l in lits: self.cl([-o, l])
        self.cl([o] + [-l for l in lits])

SV = False         # 'sv': with named columns, also every column in the interval [s, F(a, u)]
PJ = None          # 'pj=all|D|s': with named columns, also the joins p ⊔ q ≤ u ⊔ v of atoms (all / points of D / with s)
BOTDOWN = False    # 'botdown': with named columns, also F(⊥, y) ≠ ⊥ for every y ∉ D below u ⊔ v
ROWS = 0           # 'rows=K': witness-freeness along the first K values of the ⊤-orbits of F(s, ·), F(a, ·), F(b, ·)
ORBIT = 0          # 'orbit=K': u is the K-th value of the F(⊥, ·)-orbit of ⊤ (all earlier values ∉ D, witness-free)
FOREST = False     # 'forest': D is a star forest (no block contains two points shared with other blocks)
COLS = 'down'      # columns carrying witness-freeness: 'down' (y ≤ u), 'interval' ([w, u]), 'two' ({w, u}),
                   # 'updown' (y ≤ u or y ≤ v = F(a, u)), 'join' (y ≤ u ⊔ v)

def build(L, case, nearcell, glob):
    E = Enc(L); n = L.n; le = L.le; meet = L.meet; join = L.join; bot, top = L.bot, L.top; rk = L.rank
    f = lambda x, y, v: E.v('f', x, y, v); d = lambda e: E.v('d', e)
    for x in range(n):
        for y in range(n):
            lits = [f(x, y, v) for v in range(n)]; E.cl(lits)
            for p, q in itertools.combinations(lits, 2): E.cl([-p, -q])
    for x in range(n):
        for x2 in L.covers_up[x]:
            for y in range(n):
                for v in range(n): E.cl([-f(x, y, v)] + [f(x2, y, w) for w in range(n) if le[v][w]])
    for y in range(n):
        for y2 in L.covers_up[y]:
            for x in range(n):
                for v in range(n): E.cl([-f(x, y, v)] + [f(x, y2, w) for w in range(n) if le[v][w]])
    E.cl([d(bot)]); E.cl([-d(top)])
    for e in range(n):
        for c in L.covers_up[e]: E.cl([-d(c), d(e)])
        if rk[e] > 2: E.cl([-d(e)])                                     # D has height ≤ 2
    if FOREST:                                                          # D is a star forest
        blk = lambda e: E.v('blk', e)
        for e in range(n): E.iff_and(blk(e), [d(e)] + [-d(g) for g in range(n) if g != e and le[e][g]])
        atoms = [e for e in range(n) if rk[e] == 1]
        for m in range(n):
            for p, q in itertools.combinations([t for t in atoms if le[t][m]], 2):
                for n1 in range(n):
                    if n1 == m or not le[p][n1]: continue
                    for n2 in range(n):
                        if n2 == m or not le[q][n2]: continue
                        E.cl([-blk(m), -blk(n1), -blk(n2)])
    S_, A, B, U = E.onehot('s'), E.onehot('a'), E.onehot('b'), E.onehot('u')
    if ORBIT:                                   # u = k-th value of the F(⊥, ·)-orbit of ⊤, all values up to u ∉ D
        C = [E.onehot(('c', j)) for j in range(ORBIT + 1)]
        E.cl([C[0](top)])
        for j in range(ORBIT):
            for c in range(n):
                for e in range(n): E.cl([-C[j](c), -f(bot, c, e), C[j + 1](e)])
        for j in range(ORBIT + 1):
            for c in range(n):
                E.cl([-C[j](c), -d(c)])
                for x in range(n): E.S.add_clause([-C[j](c), -d(x), -E.v('fle', x, c, x)]); E.S.add_clause([-C[j](c), -d(x), -E.v('yle', x, c)])
        for e in range(n): E.cl([-U(e), C[ORBIT](e)]); E.cl([U(e), -C[ORBIT](e)])
    if ROWS:                                    # witness-freeness along the ⊤-orbits of the rows s, a, b (ROWS steps)
        for nmr, R in (('s', S_), ('a', A), ('b', B)):
            Cr = [E.onehot(('r', nmr, j)) for j in range(ROWS + 1)]
            E.cl([Cr[0](top)])
            for j in range(ROWS):
                for r in range(n):
                    for c in range(n):
                        for e in range(n): E.cl([-R(r), -Cr[j](c), -f(r, c, e), Cr[j + 1](e)])
            for j in range(ROWS + 1):
                for c in range(n):
                    for x in range(n):
                        E.S.add_clause([-Cr[j](c), -d(x), d(c), -E.v('fle', x, c, x)])
                        E.S.add_clause([-Cr[j](c), -d(x), d(c), -E.v('yle', x, c)])
    for e in range(n):
        if rk[e] != 1: E.cl([-S_(e)])
        E.cl([-S_(e), d(e)])
        for blk in (A, B):
            E.cl([-blk(e), d(e)])
            for g in range(n):
                if g != e and le[e][g]: E.cl([-blk(e), -d(g)])            # maximal in D
    for x in range(n):
        for y in range(n):
            if x == y: E.cl([-A(x), -B(y)])
            for s in range(n):
                if meet[x][y] != s: E.cl([-A(x), -B(y), -S_(s)])           # a ⊓ b = s (so s ≤ a, b)
    for a in range(n):                                                  # isolation of a with centre s
        for s in range(n):
            for x in range(n):
                if not le[x][a] and not le[meet[x][a]][s]: E.cl([-A(a), -S_(s), -d(x)])
    fle = lambda x, y, t: E.v('fle', x, y, t)
    for x in range(n):
        for y in range(n):
            for t in range(n): E.iff_or(fle(x, y, t), [f(x, y, v) for v in range(n) if le[v][t]])
    yle = lambda x, y: E.v('yle', x, y)
    for x in range(n):
        for y in range(n): E.iff_or(yle(x, y), [f(x, y, v) for v in range(n) if le[y][v]])
    def nw(x, y, cond):            # cond: list of literals whose conjunction requires no cell at (x, y)
        E.cl(cond + [-d(x), d(y), -fle(x, y, x)]); E.cl(cond + [-d(x), d(y), -yle(x, y)])
    if COLS == 'down' or glob:                                          # witness-freeness on columns ≤ u
        for u in range(n):
            for y in range(n):
                if glob or le[y][u]:
                    for x in range(n): nw(x, y, [] if glob else [-U(u)])
    else:                                                               # columns determined by u and v = F(a, u)
        for u in range(n):
            for a in range(n):
                for v in range(n):
                    w = meet[u][v]
                    named = {'u': u, 'w': w, 'v': v, 't': join[u][v]}
                    ys = (sorted({named[k] for k in COLS[6:].split(',')}) if COLS.startswith('named:') else
                          [y for y in range(n) if le[w][y] and le[y][u]] if COLS == 'interval' else
                          [y for y in range(n) if le[y][u] or le[y][v]] if COLS == 'updown' else
                          [y for y in range(n) if le[y][join[u][v]]] if COLS == 'join' else sorted({u, w}))
                    for y in ys:
                        for x in range(n): nw(x, y, [-U(u), -A(a), -f(a, u, v)])
                    if SV:                              # the interval [s, v]
                        for sc in range(n):
                            for y in range(n):
                                if le[sc][y] and le[y][v]:
                                    for x in range(n): nw(x, y, [-U(u), -A(a), -f(a, u, v), -S_(sc)])
                    if PJ:                              # joins of atoms below u ⊔ v
                        tt = join[u][v]; ats = [e for e in range(n) if rk[e] == 1 and le[e][tt]]
                        for p_, q_ in itertools.combinations_with_replacement(ats, 2):
                            y = join[p_][q_]
                            if not le[y][tt]: continue
                            if PJ == 'all': conds = [[]]
                            elif PJ == 'D': conds = [[-d(p_), -d(q_)]]
                            else: conds = [[-S_(p_)], [-S_(q_)]]          # 's': one of them is the centre
                            for cnd in conds:
                                for x in range(n): nw(x, y, [-U(u), -A(a), -f(a, u, v)] + cnd)
                    if BOTDOWN:                         # only F(⊥, y) ≰ ⊥ on every column y ≤ u ⊔ v
                        for y in range(n):
                            if le[y][join[u][v]]: E.cl([-U(u), -A(a), -f(a, u, v), d(y), -fle(bot, y, bot)])
    for u in range(n):                                                  # relay at u
        E.cl([-U(u), -d(u)])
        for s in range(n): E.cl([-U(u), -S_(s), fle(bot, u, s)])
        for b in range(n):
            E.cl([-U(u), -B(b), fle(b, u, u)])
            for a in range(n): E.cl([-U(u), -B(b), -A(a), fle(b, u, a)])
    # end case at w = u ⊓ F(a, u)
    for u in range(n):
        for a in range(n):
            for v in range(n):
                w = meet[u][v]; ctx = [-U(u), -A(a), -f(a, u, v)]
                if case == 'terminal':
                    E.cl(ctx + [d(w)])
                else:
                    E.cl(ctx + [-d(w)])
                    for b in range(n):
                        E.cl(ctx + [-B(b), f(b, w, a)])                    # F b w = a
                    if le[a][w]: E.cl(ctx)                              # a ≰ w
                    for s in range(n):
                        for p in range(n):                              # p = F s u: atom < a, F s w = p, p ≤ w
                            c2 = ctx + [-S_(s), -f(s, u, p)]
                            if not (rk[p] == 1 and le[p][a] and p != a and le[p][w] and meet[w][a] == p):
                                E.cl(c2)
                            else:
                                E.cl(c2 + [f(s, w, p)])
                                if nearcell:                            # near-cell at p, with nw at its column
                                    ncs = []
                                    for x in (p, a):
                                        for y in range(n):
                                            if y == p or not le[p][y]: continue
                                            o = E.v('nc', u, a, s, p, x, y)
                                            E.iff_and(o, [-d(y), yle(x, y)] if False else [-d(y)])
                                            ok = E.v('ncok', u, a, s, p, x, y)
                                            # y ≤ p ⊔ F(x, y) and y ≰ F(x, y)
                                            lits = [f(x, y, t) for t in range(n) if le[y][join[p][t]] and not le[y][t]]
                                            E.iff_or(ok, lits)
                                            sel = E.v('ncsel', u, a, s, p, x, y)
                                            E.cl([-sel, o]); E.cl([-sel, ok]); ncs.append(sel)
                                            for x2 in range(n): nw(x2, y, [-sel])
                                    E.cl(c2 + ncs)
    return E

def decode(E):
    m = set(x for x in E.S.get_model() if x > 0); L = E.L; n = L.n
    F = [[next(v for v in range(n) if E.vars[('f', x, y, v)] in m) for y in range(n)] for x in range(n)]
    D = [E.vars[('d', e)] in m for e in range(n)]
    pick = {k: next(e for e in range(n) if E.vars[(k, e)] in m) for k in 'sabu'}
    return F, D, pick

def check(L, F, D, pick, case):
    s, a, b, u = pick['s'], pick['a'], pick['b'], pick['u']; le = L.le; n = L.n
    assert all(le[F[x][y]][F[x2][y2]] for x in range(n) for x2 in range(n) if le[x][x2] for y in range(n) for y2 in range(n) if le[y][y2])
    assert not D[u] and le[F[L.bot][u]][s] and le[F[b][u]][u] and le[F[b][u]][a]
    w = L.meet[u][F[a][u]]
    for y in range(n):
        v = F[a][u]
        named = {'u': u, 'w': w, 'v': v, 't': L.join[u][v]}
        inc = (y in {named[k] for k in COLS[6:].split(',')} if COLS.startswith('named:') else
               le[y][u] if COLS == 'down' else (le[w][y] and le[y][u]) if COLS == 'interval' else
               (le[y][u] or le[y][v]) if COLS == 'updown' else le[y][L.join[u][v]] if COLS == 'join' else y in (u, w))
        if inc and not D[y]:
            for x in range(n):
                if D[x]: assert not le[F[x][y]][x] and not le[y][F[x][y]]
    return D[w] if case == 'terminal' else (not D[w] and F[b][w] == a and not le[a][w])

def lattices(args):
    if args[0] == 'sweep':
        import nodesc_sweep as ns
        for fam in ns.moore_families(int(args[1])):
            if len(fam) <= int(args[2]): yield ss.Lat(fam)
    else:
        k, m, sd, cnt = (int(x) for x in args[1:5]); rng = random.Random(sd)
        for _ in range(cnt): yield ss.Lat(ss.closure_system(k, m, rng))

if __name__ == '__main__':
    args = sys.argv[1:]; case = args.pop(0)
    nearcell = 'nearcell' in args; glob = 'global' in args
    FOREST = 'forest' in args; BOTDOWN = 'botdown' in args; SV = 'sv' in args
    for x in args:
        if x.startswith('orbit='): ORBIT = int(x.split('=')[1])
        if x.startswith('rows='): ROWS = int(x.split('=')[1])
        if x.startswith('pj='): PJ = x.split('=')[1]
    args = [x for x in args if not x.startswith('orbit=') and not x.startswith('rows=') and not x.startswith('pj=')]
    for c in ('interval', 'two', 'updown', 'join'):
        if c in args: COLS = c
    for x in args:
        if x.startswith('named:'): COLS = x
    args = [x for x in args if not x.startswith('named:')]
    args = [x for x in args if x not in ('nearcell', 'global', 'interval', 'two', 'updown', 'join', 'forest', 'botdown', 'sv')]
    T = collections.Counter(); best = None
    for L in lattices(args):
        if L.height < 3: continue
        E = build(L, case, nearcell, glob)
        if E.S.solve():
            F, D, pick = decode(E); assert check(L, F, D, pick, case)
            T['SAT'] += 1
            if best is None or L.n < best[0].n: best = (L, F, D, pick)
        else: T['UNSAT'] += 1
        E.S.delete()
    print(f"case {case}{f' (u = orbit value {ORBIT})' if ORBIT else ''}{f' (row orbits {ROWS})' if ROWS else ''}{f' (atom joins {PJ})' if PJ else ''}{' (star forest)' if FOREST else ''}{' + near-cell' if nearcell else ''}{' (global witness-freeness)' if glob else f' (witness-free columns: {COLS})'}: {dict(T)}", flush=True)
    if best:
        L, F, D, pick = best; w = max(s.bit_length() for s in L.S)
        nm = lambda i: '{' + ''.join(str(j) for j in range(w) if L.S[i] >> j & 1) + '}'
        print(f"smallest model: |L| = {L.n}, height {L.height}, D = {[nm(i) for i in range(L.n) if D[i]]}, "
              + ', '.join(f"{k} = {nm(v)}" for k, v in pick.items()), flush=True)
        import json; json.dump(dict(sets=L.S, F=F, D=D, pick=pick), open(f"relay_{case}{'_nc' if nearcell else ''}.json", 'w'))
