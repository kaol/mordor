"""Near-models of MinH2 (log §34.3z²²⁸): for each single-column core of dich1_h0core.py (¬IC(m) used only at z), solve
H₀ with ¬IC(m) dropped at z, plus ¬MinH2; classify z relative to the model.   python3 dich1_near.py CORES.jsonl
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers
import separator_stages as ss
from rstages import stages, a_of, b_of
C = collections.Counter()
for line in open(sys.argv[1]):
    d = json.loads(line); core = [tuple(t) for t in d['core']]
    zs = {t[1] for t in core if t[0] in ('NL', 'NU')}
    if len(zs) != 1 or not any(t[0] == 'X' for t in core): continue
    z0 = zs.pop(); L = ss.Lat(d['sets']); n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top; m = d['m']; jn = L.join
    E = Enc(L, 3); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
    add([r(2, m)]); add([-r(1, m)]); add([-r(3, top)])
    for z in range(n):
        if le[m][z] and z != m and z != z0: add([-fle(m, z, m)]); add([-yle(m, z)])
    for y in range(n):
        if h[y] != 2 or le[m][y]: continue
        for c in L.covers_dn[y]:
            if h[c] == 1: add([-f(bot, y, c), -fle(c, y, y)]); add([-f(bot, y, c), -yle(c, y)])
    if not E.S.solve(): C['near-model UNSAT (core not minimal at z?)'] += 1; continue
    F = E.decode(); st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j
    cell = lambda x, y: le[F[x][y]][x] or le[y][F[x][y]]
    entries = [y for y in range(n) if le[m][y] and any(inR(x, 1) and cell(x, y) for x in range(n))]       # columns ≥ m that are R_1-row cells
    t = F[m][top]
    feats = {'z = ⊤': z0 == top, 'z = m ∨ F(m, ⊤)': z0 == jn[m][t], 'z = F(m, ⊤)': z0 == t, 'z an R_1-cell column ≥ m (m\'s entry)': z0 in entries,
             'z = a(m)': z0 == a_of(L, F, m), 'm-row cell at z is lower (F(m,z) ≤ m)': le[F[m][z0]][m], 'upper (z ≤ F(m,z))': le[z0][F[m][z0]],
             'z = m ∨ y for a height-2 y ≱ m': any(h[y] == 2 and not le[m][y] and jn[m][y] == z0 for y in range(n)), 'h(z)': h[z0],
             'z is the least entry column': bool(entries) and z0 == min(entries, key=lambda y: h[y]) and all(le[z0][e] for e in entries)}
    for k_, v in feats.items(): C[(k_, v)] += 1
    C['near-models'] += 1
for k_, v in sorted(C.items(), key=str): print(k_, v)
