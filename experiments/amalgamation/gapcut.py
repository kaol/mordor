"""GapCutStep, local form (log §34.3z²¹⁸).

Hypotheses (exact): m; a fixed point y = m ⊔ w with F(m, y) = w ≱ m (NOT assumed greatest unless 'full'); x = F(⊥, w) an
atom ∥ m; row x cell-free on (x, ⊤]; T1b↑ (F(⊥, z) ≠ ⊥ for z > x); a gap v, g = F(x, v): x < v ≤ y, F(⊥, v) = x,
y ⊓ g = x; and a final transition of g ⊓ u_n along a column orbit element u of m: g ⊓ u > x, g ⊓ (m ⊔ F(m, u)) = x.
Modes: 'orbit' (u on the column orbit of m from ⊤, positions exact), 'post' (any u ≥ y with m ⊔ F(m, u) ≤ u),
'full' (orbit + y greatest; control); 'wit' (orbit + y greatest, T1b↑ dropped, claim: F(⊥, g ⊓ u) = ⊥ at the
transition); 'witx' (as 'wit' with T1b↑ kept on every z > x except g ⊓ u); 'witx0' (as 'witx' without the claim: is the
configuration satisfiable at all?); 'lc1' / 'lc2' (T1b↑ dropped; claim F(⊥, g ⊓ u) ≤ g / ≤ x); 'witfx' (T1b↑ only
at F(x, c); claim F(⊥, c) = ⊥); 'witxo' (T1b↑ only on the x-orbit F(x, c), F(x, F(x, c)), ... above x; same claim).  A model is a counterexample to the local GapCutStep.
   python3 gapcut.py (orbit|post|full) (sweep N MAX | closure K M SEED CNT)
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
mode = sys.argv[1]; C = collections.Counter(); best = None
for L in lattices(sys.argv[2:]):
    n = L.n; le = L.le; jn = L.join; bot = L.rank.index(0); h = L.rank; hit = None
    mt = lambda a, b: L.S.index(L.S[a] & L.S[b])
    for m in range(n):
        if m == L.top or hit: continue
        E = Enc(L, 1); fle, yle, ic = helpers(E, L); f = lambda a, b, q: E.v('f', a, b, q); sels = []
        P = lambda i, u: E.v('P', i, u)
        if mode in ('orbit', 'full', 'wit', 'witx', 'witx0', 'lc1', 'lc2', 'witfx', 'witxo'):
            E.S.add_clause([P(0, L.top)])
            for i in range(n):
                for u in range(n):
                    for q in range(n): E.S.add_clause([-P(i, u), -f(m, u, q), P(i + 1, jn[m][q])])
                    for u2 in range(u + 1, n): E.S.add_clause([-P(i, u), -P(i, u2)])
        for w in range(n):
            if le[m][w]: continue
            y = jn[m][w]
            for x in range(n):
                if h[x] != 1 or x == w or not le[x][w] or le[x][m]: continue
                for v in range(n):
                    if not (le[x][v] and v != x and le[v][y]): continue
                    for g in range(n):
                        if not (le[x][g] and g != x and mt(y, g) == x): continue
                        for u in range(n):
                            if not le[y][u] or mt(g, u) == x: continue          # g ⊓ u > x (g ⊓ u ≥ x as y ≤ u)
                            for u2 in range(n):
                                if not (le[y][u2] and le[u2][u] and mt(g, u2) == x): continue
                                o = E.v('sel', w, x, v, g, u, u2); sels.append(o)
                                for lit in (f(m, y, w), f(bot, w, x), f(bot, v, x), f(x, v, g)): E.S.add_clause([-o, lit])
                                for q in range(n):
                                    if jn[m][q] != u2: E.S.add_clause([-o, -f(m, u, q)])   # u2 = m ⊔ F(m, u)
                                if mode in ('orbit', 'full', 'wit', 'witx', 'witx0', 'lc1', 'lc2', 'witfx', 'witxo'): E.S.add_clause([-o] + [P(i, u) for i in range(n)])
                                c = mt(g, u)
                                if mode in ('wit', 'witx', 'witfx', 'witxo'): E.S.add_clause([-o, -f(bot, c, bot)])
                                if mode == 'witfx':
                                    for d_ in range(n):
                                        if le[x][d_] and d_ != x: E.S.add_clause([-o, -f(x, c, d_), -f(bot, d_, bot)])
                                if mode == 'witxo':
                                    Q = lambda i, z_: E.v('Qx', w, x, v, g, u, u2, i, z_)
                                    for d_ in range(n): E.S.add_clause([-o, -f(x, c, d_), Q(0, d_)])
                                    for i in range(n):
                                        for z_ in range(n):
                                            if le[x][z_] and z_ != x: E.S.add_clause([-Q(i, z_), -f(bot, z_, bot)])
                                            for d_ in range(n): E.S.add_clause([-Q(i, z_), -f(x, z_, d_), Q(i + 1, d_)])
                                if mode in ('lc1', 'lc2'): E.S.add_clause([-o, -fle(bot, c, g if mode == 'lc1' else x)])
                                for z in range(n):
                                    if le[x][z] and z != x:
                                        E.S.add_clause([-o, -fle(x, z, x)]); E.S.add_clause([-o, -yle(x, z)])
                                        if mode not in ('wit', 'witx', 'witx0', 'lc1', 'lc2', 'witfx', 'witxo') or (mode in ('witx', 'witx0') and z != c): E.S.add_clause([-o, -f(bot, z, bot)])
                                    if mode in ('full', 'wit', 'witx', 'witx0', 'lc1', 'lc2', 'witfx', 'witxo') and not le[z][y]:
                                        for gg in range(n):
                                            if le[z][jn[m][gg]]: E.S.add_clause([-o, -f(m, z, gg)])
        if not sels: E.S.delete(); continue
        E.S.add_clause(sels)
        if E.S.solve():
            mod = set(l for l in E.S.get_model() if l > 0)
            F = [[next(q for q in range(n) if E.vars[('f', a, b, q)] in mod) for b in range(n)] for a in range(n)]
            sel = next(t for t in E.vars if t[0] == 'sel' and E.vars[t] in mod)
            hit = dict(sets=L.S, F=F, m=m, sel=list(sel[1:]))
        E.S.delete()
    C['counterexample' if hit else 'none'] += 1
    if hit and (best is None or L.n < best[0]): best = (L.n, hit)
print(f'local GapCutStep ({mode}):', dict(C), 'smallest', best[0] if best else None)
if best: json.dump(best[1], open(f'gapcut_{mode}_min{best[0]}.json', 'w'))
