"""The gap configuration with T1b dropped (log §34.3z²¹²): which elements violate T1b, relative to v and g = F(x, v).

SAT models (several per lattice, blocking): m any, y the greatest post-fixed point of y ↦ m ⊔ F(m, y), w = F(m, y) ≱ m,
x = F(⊥, w) an atom ∥ m with no interval cell, and v with x < v ≤ y, F(⊥, v) = x, x ≤ g = F(x, v), y ⊓ g = x.
With 'exact': instead of sampling, ask for a gap model with F(⊥, g) ≠ ⊥ (the claim: F(⊥, g) = ⊥ in every gap).
   python3 gap_probe.py [exact] (sweep N MAX | closure K M SEED CNT) [per=K]
"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from gfp_top import ystar
PER = next((int(a[4:]) for a in sys.argv if a.startswith('per=')), 4)
EXACT = 'exact' in sys.argv; T1BX = 't1bx' in sys.argv   # 't1bx': T1b on every rank-≥2 element except g
T1BE = 't1be' in sys.argv   # 't1be': T1b only at x ⊔ e for the atoms e ≤ m with e ≰ w (the elements of the minimal cores)
args = [a for a in sys.argv[1:] if not a.startswith('per=') and a not in ('exact', 't1bx', 't1be')]
CE = collections.Counter(); best = None
C = collections.Counter()
for L in lattices(args):
    n = L.n; le = L.le; jn = L.join; bot = L.rank.index(0); h = L.rank
    mt = lambda a, b: L.S.index(L.S[a] & L.S[b])
    for m in range(n):
        if m == L.top: continue
        E = Enc(L, 1); fle, yle, ic = helpers(E, L); f = lambda a, b, v: E.v('f', a, b, v); sels = []
        for w in range(n):
            if le[m][w]: continue
            y = jn[m][w]
            for x in range(n):
                if h[x] != 1 or x == w or not le[x][w] or le[x][m]: continue
                for v in range(n):
                    if not (le[x][v] and v != x and le[v][y]): continue
                    for g in range(n):
                        if not (le[x][g] and mt(y, g) == x): continue
                        o = E.v('sel', w, x, v, g); sels.append(o)
                        for lit in (f(m, y, w), f(bot, w, x), f(bot, v, x), f(x, v, g)): E.S.add_clause([-o, lit])
                        if EXACT: E.S.add_clause([-o, -f(bot, g, bot)])
                        if T1BE:
                            for e in range(n):
                                if h[e] == 1 and le[e][m] and not le[e][w] and h[jn[x][e]] >= 2: E.S.add_clause([-o, -f(bot, jn[x][e], bot)])
                        if T1BX:
                            for z in range(n):
                                if h[z] >= 2 and z != g: E.S.add_clause([-o, -f(bot, z, bot)])
                        for z in range(n):
                            if not le[z][y]:
                                for gg in range(n):
                                    if le[z][jn[m][gg]]: E.S.add_clause([-o, -f(m, z, gg)])
                            if le[x][z] and z != x: E.S.add_clause([-o, -fle(x, z, x)]); E.S.add_clause([-o, -yle(x, z)])
        if not sels: E.S.delete(); continue
        E.S.add_clause(sels); k = 0
        if EXACT:
            r_ = E.S.solve(); CE['counterexample' if r_ else 'none'] += 1
            if r_ and (best is None or n < best):
                best = n; print('COUNTEREXAMPLE |L| =', n, 'm =', m, flush=True)
                mod = set(l for l in E.S.get_model() if l > 0)
                F = [[next(v for v in range(n) if E.vars[('f', a, b, v)] in mod) for b in range(n)] for a in range(n)]
                import json; json.dump(dict(sets=L.S, F=F, m=m, sel=list(next(t for t in E.vars if t[0] == 'sel' and E.vars[t] in mod)[1:])), open(f"gap_exact{'_t1bx' if T1BX else ''}{'_t1be' if T1BE else ''}_min{n}.json", 'w'))
            E.S.delete(); continue
        while k < PER and E.S.solve():
            mod = set(l for l in E.S.get_model() if l > 0); k += 1
            F = [[next(v for v in range(n) if E.vars[('f', a, b, v)] in mod) for b in range(n)] for a in range(n)]
            E.S.add_clause([-E.vars[('f', a, b, F[a][b])] for a in range(n) for b in range(n)])
            sel = next(t for t in E.vars if t[0] == 'sel' and E.vars[t] in mod); _, w, x, v, g = sel
            ys = ystar(L, F, m); assert jn[m][w] == ys and F[m][ys] == w
            Z = {z for z in range(n) if h[z] >= 2 and F[bot][z] == bot}
            C['models'] += 1
            cand = {'g': g, 'v⊔g': jn[v][g], 'F(x,g)': F[x][g], 'F(x,v⊔g)': F[x][jn[v][g]], 'x⊔F(m,g)': jn[x][F[m][g]],
                    'g⊓(m⊔F(m,g))': mt(g, jn[m][F[m][g]]), 'g⊓F(x,g)': mt(g, F[x][g]), 'x⊔F(⊥,g)': jn[x][F[bot][g]],
                    'v⊔F(x,g)': jn[v][F[x][g]], 'F(m,v⊔g)': F[m][jn[v][g]]}
            for k_, c in cand.items(): C[(k_, 'in Z', c in Z)] += 1
            C[('|Z|', len(Z))] += 1
            C[('F(⊥,g)', 'x' if F[bot][g] == x else '⊥' if F[bot][g] == bot else '≤g' if le[F[bot][g]][g] else 'other')] += 1
            C[('F(x,g) vs g', '≤' if le[F[x][g]][g] else '≥' if le[g][F[x][g]] else '∥')] += 1
        E.S.delete()
if EXACT: print('exact gap ⇒ F(⊥, g) = ⊥ (per (L, m) with a gap):', dict(CE), 'smallest', best)
for k_, v in sorted(C.items(), key=str): print(k_, v)
