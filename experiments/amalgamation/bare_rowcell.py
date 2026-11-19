"""Bare RowCell / RowLT: no orbit hypotheses (log §34.3z²⁰⁷).

Any monotone F on a fixed finite lattice, any m ≠ ⊤ (optionally rank(m) = R: 'rank=R').  y* = the greatest post-fixed
point of y ↦ m ⊔ F(m, y), w = F(m, y*) ≱ m, x = F(⊥, w) ≠ w of rank 1.  Counterexample to
  'cell': row x has no interval cell at a column z > x with m ≰ z;
  'lt'  : row x has no LT pair (v > x, m ≰ v, F(x, v) ≤ v, F(⊥, v) ≤ x);
  'cell2': as 'cell' with x any rank-1 term of the ⊥-descent v ↦ F(⊥, v) from w (chain positions encoded exactly).
Flags: 'noic' (¬IC(m)); orbit hypotheses 'new' (m ∈ R_2 ∖ R_1), 't1' (R_1 of rank ≤ 1), 't2' (R_2 of rank ≤ 2).  Every model is re-checked in Python.
   python3 bare_rowcell.py (cell|lt) [noic] [rank=R] (sweep N MAX | closure K M SEED CNT)
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from gfp_top import ystar
from rstages import stages
mode = sys.argv[1]; NOIC = 'noic' in sys.argv; HYP = [a for a in ('new', 't1', 't2') if a in sys.argv]
RANK = next((int(a[5:]) for a in sys.argv if a.startswith('rank=')), None)
args = [a for a in sys.argv[2:] if a not in ('noic', 'new', 't1', 't2') and not a.startswith('rank=')]
C = collections.Counter(); best = None
def check(L, F, m):
    n = L.n; le = L.le; bot = L.rank.index(0)
    ys = ystar(L, F, m); w = F[m][ys]
    if le[m][w]: return False
    if mode == 'cell2':
        ch = [w]
        while F[bot][ch[-1]] not in ch: ch.append(F[bot][ch[-1]])
        xs = [x for x in ch if L.rank[x] == 1]
    else:
        xs = [F[bot][w]] if L.rank[F[bot][w]] == 1 and F[bot][w] != w else []
    if not xs: return False
    st = stages(L, F); inR = lambda z, j: st[z] is not None and st[z] <= j
    if 'new' in HYP and not (inR(m, 2) and not inR(m, 1)): return False
    if 't1' in HYP and any(inR(z, 1) and L.rank[z] > 1 for z in range(n)): return False
    if 't2' in HYP and any(inR(z, 2) and L.rank[z] > 2 for z in range(n)): return False
    if NOIC and any(le[m][y] and y != m and (le[F[m][y]][m] or le[y][F[m][y]]) for y in range(n)): return False
    if mode in ('cell', 'cell2'): return any(not any(le[x][z] and z != x and not le[m][z] and (le[F[x][z]][x] or le[z][F[x][z]]) for z in range(n)) for x in xs)
    return any(not any(le[x][v] and v != x and not le[m][v] and le[F[x][v]][v] and le[F[bot][v]][x] for v in range(n)) for x in xs)
for L in lattices(args):
    n = L.n; le = L.le; jn = L.join; bot = L.rank.index(0); hit = None
    for m in range(n):
        if m == L.top or (RANK is not None and L.rank[m] != RANK): continue
        E = Enc(L, 2); fle, yle, ic = helpers(E, L); f = lambda a, b, v: E.v('f', a, b, v); r = lambda j, z: E.v('r', j, z)
        if NOIC: E.S.add_clause([-ic(m)])
        if 'new' in HYP: E.S.add_clause([r(2, m)]); E.S.add_clause([-r(1, m)])
        for z in range(n):
            if 't1' in HYP and L.rank[z] > 1: E.S.add_clause([-r(1, z)])
            if 't2' in HYP and L.rank[z] > 2: E.S.add_clause([-r(2, z)])
        sels = []
        for w in range(n):
            if le[m][w]: continue
            y = jn[m][w]
            if mode == 'cell2':
                P = lambda i, v: E.v('P', w, i, v)
                for i in range(n):
                    for v in range(n):
                        for u in range(n): E.S.add_clause([-P(i, v), -f(bot, v, u), P(i + 1, u)])
                        for u in range(v + 1, n): E.S.add_clause([-P(i, v), -P(i, u)])
            for x in range(n):
                if L.rank[x] != 1 or not le[x][w] or (x == w and mode != 'cell2'): continue
                o = E.v('sel', w, x); sels.append(o)
                E.S.add_clause([-o, f(m, y, w)])
                if mode == 'cell2': E.S.add_clause([-o, P(0, w)]); E.S.add_clause([-o] + [P(i, x) for i in range(n)])
                else: E.S.add_clause([-o, f(bot, w, x)])
                for z in range(n):
                    if le[z][y]: continue
                    for g in range(n):
                        if le[z][jn[m][g]]: E.S.add_clause([-o, -f(m, z, g)])
                for z in range(n):
                    if not (le[x][z] and z != x and not le[m][z]): continue
                    if mode in ('cell', 'cell2'): E.S.add_clause([-o, -fle(x, z, x)]); E.S.add_clause([-o, -yle(x, z)])
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
