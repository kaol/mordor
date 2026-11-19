"""Bare RowCell / RowLT: no orbit hypotheses (log §34.3z²⁰⁷).

Any monotone F on a fixed finite lattice, any m ≠ ⊤ (optionally rank(m) = R: 'rank=R').  y* = the greatest post-fixed
point of y ↦ m ⊔ F(m, y), w = F(m, y*) ≱ m, x = F(⊥, w) ≠ w of rank 1.  Counterexample to
  'cell': row x has no interval cell at a column z > x with m ≰ z;
  'lt'  : row x has no LT pair (v > x, m ≰ v, F(x, v) ≤ v, F(⊥, v) ≤ x);
  'ic'  : row x has no interval cell at all (z > x);
  'tbot': row x has no interval cell and F(⊥, F(x, w)) ≠ ⊥ (the claim: a cell-free x forces F(⊥, t) = ⊥);
  'yxbot': row x has no interval cell and F(⊥, y_x) ≠ ⊥, y_x the greatest post-fixed point of y ↦ x ⊔ F(x, y);
  'tyx' : row x has no interval cell and not (t ⊓ y_x > x and F(⊥, t ⊓ y_x) = ⊥), t = F(x, w);
  'xorbz': x = F(⊥, w) cell-free and no element v of the x-orbit v ↦ F(x, v) from w has rank ≥ 2 and F(⊥, v) = ⊥;
  'gxorbz': the same for the orbit u ↦ x ⊔ F(x, u) from w;
  'prefx': x = F(⊥, w) cell-free and row x has no pre-fixed column z with x < z ≤ y (F(x, z) ≤ z);
  'prefw': x = F(⊥, w) cell-free and row x has no pre-fixed column z > x with F(⊥, z) ≤ w;
  'deep': x a rank-1 term of the ⊥-descent from w with x ≤ m and x ≠ F(⊥, w) (no conclusion: is a deep atom below m possible?);
  'ic3' : x a rank-1 term of the ⊥-descent from w, conclusion IC(x) (no interval cell at all is the violation);
  'ic2' : as 'cell2' (x a rank-1 term of the ⊥-descent from w, conclusion a cell off m), intended with t1b only;
  'cell2': as 'cell' with x any rank-1 term of the ⊥-descent v ↦ F(⊥, v) from w (chain positions encoded exactly).
Flags: 'noic' (¬IC(m)); orbit hypotheses 'new' (m ∈ R_2 ∖ R_1), 't1' (R_1 of rank ≤ 1), 't2' (R_2 of rank ≤ 2);
parts (§34.3z²⁰⁸): 't1a' rank a(⊥) ≤ 1, 't1b' b(z) = ⊥ ⇒ rank z ≤ 1, 't2a' x ∈ R_1 ⇒ rank a(x) ≤ 2, 't2b' b(z) ∈ R_1 ⇒ rank z ≤ 2;
'par': x ∥ m; local parts for the selected row x: 'ax' rank a(x) ≤ 2, 'bx' b(z) ≤ x ⇒ rank z ≤ 2; 'anyfix': any fixed point y = m ⊔ F(m, y), not only y*.  Every model is re-checked in Python.
   python3 bare_rowcell.py (cell|lt) [noic] [rank=R] (sweep N MAX | closure K M SEED CNT)
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from gfp_top import ystar
from rstages import stages, a_of, b_of
mode = sys.argv[1]; NOIC = 'noic' in sys.argv; HYP = [a for a in ('new', 't1', 't2', 't1a', 't1b', 't2a', 't2b', 'par', 'ax', 'bx', 'anyfix', 'yxny') if a in sys.argv]
RANK = next((int(a[5:]) for a in sys.argv if a.startswith('rank=')), None)
args = [a for a in sys.argv[2:] if a not in ('noic', 'new', 't1', 't2', 't1a', 't1b', 't2a', 't2b', 'par', 'ax', 'bx', 'anyfix', 'yxny') and not a.startswith('rank=')]
C = collections.Counter(); best = None
def check(L, F, m):
    n = L.n; le = L.le; bot = L.rank.index(0)
    if 'anyfix' in HYP:
        ws = [w for w in range(n) if not le[m][w] and F[m][L.join[m][w]] == w]
        return any(check1(L, F, m, w) for w in ws)
    ys = ystar(L, F, m); w = F[m][ys]
    return check1(L, F, m, w)
def check1(L, F, m, w):
    n = L.n; le = L.le; bot = L.rank.index(0)
    st = stages(L, F); inR = lambda z, j: st[z] is not None and st[z] <= j
    if le[m][w]: return False
    if mode in ('cell2', 'ic2', 'ic3', 'deep'):
        ch = [w]
        while F[bot][ch[-1]] not in ch: ch.append(F[bot][ch[-1]])
        xs = [x for x in ch if L.rank[x] == 1]
    else:
        xs = [F[bot][w]] if L.rank[F[bot][w]] == 1 and F[bot][w] != w else []
    if 'par' in HYP: xs = [x for x in xs if not le[x][m]]
    if 'ax' in HYP: xs = [x for x in xs if L.rank[a_of(L, F, x)] <= 2]
    if 'bx' in HYP: xs = [x for x in xs if not any(le[b_of(L, F, z)][x] and L.rank[z] > 2 for z in range(n))]
    if not xs: return False
    st = stages(L, F); inR = lambda z, j: st[z] is not None and st[z] <= j
    if 'new' in HYP and not (inR(m, 2) and not inR(m, 1)): return False
    if 't1' in HYP and any(inR(z, 1) and L.rank[z] > 1 for z in range(n)): return False
    if 't2' in HYP and any(inR(z, 2) and L.rank[z] > 2 for z in range(n)): return False
    if 't1a' in HYP and L.rank[a_of(L, F, bot)] > 1: return False
    if 't1b' in HYP and any(b_of(L, F, z) == bot and L.rank[z] > 1 for z in range(n)): return False
    if 't2a' in HYP and any(inR(g, 1) and L.rank[a_of(L, F, g)] > 2 for g in range(n)): return False
    if 't2b' in HYP and any(inR(b_of(L, F, z), 1) and L.rank[z] > 2 for z in range(n)): return False
    if NOIC and any(le[m][y] and y != m and (le[F[m][y]][m] or le[y][F[m][y]]) for y in range(n)): return False
    if mode == 'deep': return any(le[x][m] and x != F[bot][w] for x in xs)
    if mode == 'prefw':
        return any(not any(le[x][z] and z != x and (le[F[x][z]][x] or le[z][F[x][z]]) for z in range(n)) and not any(le[x][z] and z != x and le[F[x][z]][z] and le[F[bot][z]][w] for z in range(n)) for x in xs)
    if mode == 'prefx':
        yy = L.join[m][w]
        return any(not any(le[x][z] and z != x and (le[F[x][z]][x] or le[z][F[x][z]]) for z in range(n)) and not any(le[x][z] and z != x and le[z][yy] and le[F[x][z]][z] for z in range(n)) for x in xs)
    if mode in ('xorbz', 'gxorbz'):
        def orbz(x):
            ob = [w]
            while True:
                u = F[x][ob[-1]] if mode == 'xorbz' else L.join[x][F[x][ob[-1]]]
                if u in ob: break
                ob.append(u)
            return any(L.rank[v] >= 2 and F[bot][v] == bot for v in ob)
        return any(not any(le[x][z] and z != x and (le[F[x][z]][x] or le[z][F[x][z]]) for z in range(n)) and not orbz(x) for x in xs)
    if mode in ('ic', 'tbot', 'yxbot', 'tyx', 'ic3'):
        def yx_(x):
            y_ = L.top
            while L.join[x][F[x][y_]] != y_: y_ = L.join[x][F[x][y_]]
            return y_
        return any(not any(le[x][z] and z != x and (le[F[x][z]][x] or le[z][F[x][z]]) for z in range(n)) and (mode in ('ic', 'ic3') or (mode == 'tbot' and F[bot][F[x][w]] != bot) or (mode == 'yxbot' and F[bot][yx_(x)] != bot and not ('yxny' in HYP and le[yx_(x)][L.join[m][w]])) or (mode == 'tyx' and not (L.rank[L.S.index(L.S[F[x][w]] & L.S[yx_(x)])] >= 2 and F[bot][L.S.index(L.S[F[x][w]] & L.S[yx_(x)])] == bot))) for x in xs)
    if mode in ('cell', 'cell2', 'ic2'): return any(not any(le[x][z] and z != x and not le[m][z] and (le[F[x][z]][x] or le[z][F[x][z]]) for z in range(n)) for x in xs)
    return any(not any(le[x][v] and v != x and not le[m][v] and le[F[x][v]][v] and le[F[bot][v]][x] for v in range(n)) for x in xs)
for L in lattices(args):
    n = L.n; le = L.le; jn = L.join; bot = L.rank.index(0); hit = None
    for m in range(n):
        if m == L.top or (RANK is not None and L.rank[m] != RANK): continue
        E = Enc(L, 2); fle, yle, ic = helpers(E, L); f = lambda a, b, v: E.v('f', a, b, v); r = lambda j, z: E.v('r', j, z)
        if NOIC: E.S.add_clause([-ic(m)])
        if 'new' in HYP: E.S.add_clause([r(2, m)]); E.S.add_clause([-r(1, m)])
        A = lambda a_, g: E.v('A', a_, g); B = lambda y_, g: E.v('B', y_, g)
        for z in range(n):
            if 't1a' in HYP and L.rank[z] > 1: E.S.add_clause([-A(bot, z)])
            if 't1b' in HYP and L.rank[z] > 1: E.S.add_clause([-B(z, bot)])
            for g in range(n):
                if 't2a' in HYP and L.rank[z] > 2: E.S.add_clause([-r(1, g), -A(g, z)])
                if 't2b' in HYP and L.rank[z] > 2: E.S.add_clause([-r(1, g), -B(z, g)])
            if 't1' in HYP and L.rank[z] > 1: E.S.add_clause([-r(1, z)])
            if 't2' in HYP and L.rank[z] > 2: E.S.add_clause([-r(2, z)])
        sels = []
        for w in range(n):
            if le[m][w]: continue
            y = jn[m][w]
            if mode in ('cell2', 'ic2', 'ic3', 'deep'):
                P = lambda i, v: E.v('P', w, i, v)
                for i in range(n):
                    for v in range(n):
                        for u in range(n): E.S.add_clause([-P(i, v), -f(bot, v, u), P(i + 1, u)])
                        for u in range(v + 1, n): E.S.add_clause([-P(i, v), -P(i, u)])
            for x in range(n):
                if L.rank[x] != 1 or not le[x][w] or (x == w and mode not in ('cell2', 'ic2', 'ic3', 'deep')) or (mode == 'deep' and not le[x][m]) or ('par' in HYP and le[x][m]): continue
                o = E.v('sel', w, x); sels.append(o)
                E.S.add_clause([-o, f(m, y, w)])
                if mode == 'deep': E.S.add_clause([-o, -f(bot, w, x)])
                for z in range(n):
                    if L.rank[z] <= 2: continue
                    if 'ax' in HYP: E.S.add_clause([-o, -E.v('A', x, z)])
                    if 'bx' in HYP:
                        for g in range(n):
                            if le[g][x]: E.S.add_clause([-o, -E.v('B', z, g)])
                if mode in ('cell2', 'ic2', 'ic3', 'deep'): E.S.add_clause([-o, P(0, w)]); E.S.add_clause([-o] + [P(i, x) for i in range(n)])
                else: E.S.add_clause([-o, f(bot, w, x)])
                for z in range(n):
                    if le[z][y] or 'anyfix' in HYP: continue
                    for g in range(n):
                        if le[z][jn[m][g]]: E.S.add_clause([-o, -f(m, z, g)])
                if mode in ('yxbot', 'tyx'):
                    yl = []
                    for yx in range(n):
                        if not (le[x][yx] and yx != x) or ('yxny' in HYP and le[yx][y]): continue
                        for wx in range(n):
                            if jn[x][wx] != yx: continue
                            p_ = E.v('yxsel', w, x, yx, wx); yl.append(p_)
                            E.S.add_clause([-p_, f(x, yx, wx)])
                            if mode == 'yxbot': E.S.add_clause([-p_, -f(bot, yx, bot)])
                            else:
                                for t_ in range(n):
                                    q_ = L.S.index(L.S[t_] & L.S[yx])
                                    if L.rank[q_] >= 2: E.S.add_clause([-p_, -f(x, w, t_), -f(bot, q_, bot)])
                            for z in range(n):
                                if le[z][yx]: continue
                                for g in range(n):
                                    if le[z][jn[x][g]]: E.S.add_clause([-p_, -f(x, z, g)])
                    E.S.add_clause([-o] + yl)
                if mode == 'prefw':
                    for z in range(n):
                        if le[x][z] and z != x: E.S.add_clause([-o, -fle(x, z, z), -fle(bot, z, w)])
                if mode == 'prefx':
                    for z in range(n):
                        if le[x][z] and z != x and le[z][y]: E.S.add_clause([-o, -fle(x, z, z)])
                if mode in ('xorbz', 'gxorbz'):
                    ob = lambda v: E.v('xo', w, x, v)
                    E.S.add_clause([-o, ob(w)])
                    for v in range(n):
                        for u in range(n):
                            tgt = u if mode == 'xorbz' else jn[x][u]
                            E.S.add_clause([-ob(v), -f(x, v, u), ob(tgt)])
                        if L.rank[v] >= 2: E.S.add_clause([-ob(v), -f(bot, v, bot)])
                if mode == 'tbot':
                    for t_ in range(n): E.S.add_clause([-o, -f(x, w, t_), -f(bot, t_, bot)])
                for z in range(n):
                    if not (le[x][z] and z != x and (mode in ('ic', 'tbot', 'yxbot', 'tyx', 'ic3', 'xorbz', 'gxorbz', 'prefx', 'prefw') or not le[m][z])): continue
                    if mode in ('cell', 'cell2', 'ic', 'tbot', 'yxbot', 'tyx', 'ic2', 'ic3', 'xorbz', 'gxorbz', 'prefx', 'prefw'): E.S.add_clause([-o, -fle(x, z, x)]); E.S.add_clause([-o, -yle(x, z)])
                    else: E.S.add_clause([-o, -fle(x, z, z), -fle(bot, z, x)])
        if not sels: E.S.delete(); continue
        E.S.add_clause(sels)
        if E.S.solve():
            mod = set(l for l in E.S.get_model() if l > 0)
            F = [[next(v for v in range(n) if E.vars[('f', a, b, v)] in mod) for b in range(n)] for a in range(n)]
            assert check(L, F, m), 'decode mismatch'
            hit = (m, F)
        E.S.delete()
        if hit: break
    C['counterexample' if hit else 'none'] += 1
    if hit and (best is None or L.n < best[0].n): best = (L, hit)
print(f"bare {mode}{' noic' if NOIC else ''}{''.join(' ' + h_ for h_ in HYP)}{f' rank={RANK}' if RANK else ''}: {dict(C)}" + (f"; smallest |L| = {best[0].n}, rank(m) = {best[0].rank[best[1][0]]}" if best else ''))
if best: json.dump(dict(sets=best[0].S, F=best[1][1], m=best[1][0]), open(f"bare_{mode}{'_noic' if NOIC else ''}{''.join('_' + h_ for h_ in HYP)}{f'_rank{RANK}' if RANK else ''}_min{best[0].n}.json", 'w'))
