"""Near-models of (A) (log §34.3z²⁴²): drop the single T2 instance g of a one-instance core, keep all other tightness,
and record how g enters R_2 (the row x ∈ R_1 and the route) relative to c, c' = F(⊥, a(c)), a(c) and p.
  python3 caseA_near.py (sweep N MAX | closure K M SEED CNT)
"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from rstages import stages, a_of, b_of
args = sys.argv[1:]; C = collections.Counter(); shown = 0
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top; jn = L.join
    if L.height < 3: continue
    nm = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
    for g0 in range(n):
        if h[g0] != 3: continue
        E = Enc(L, 3); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
        A_ = lambda x, g: E.v('A', x, g); NO = L.height + 1; D = lambda i, z: E.v('D', i, z)
        for z in range(n): add([D(0, z)] if z == top else [-D(0, z)])
        for i in range(NO):
            for z in range(n):
                lits = []
                for v in range(n): o = E.v('Ds', i, v, z); E.iff_and(o, [D(i, v), f(bot, v, z)]); lits.append(o)
                E.iff_or(D(i + 1, z), lits)
        atoms = [c for c in range(n) if h[c] == 1]
        At = {c: E.v('datom', c) for c in atoms}
        for c in atoms: E.iff_or(At[c], [D(i, c) for i in range(NO + 1)])
        add(list(At.values())); add([A_(bot, bot)])
        for c in atoms:
            add([-At[c]] + [A_(c, g) for g in range(n) if le[c][g] and g != c])
            for g in range(n):
                if le[c][g] and g != c: add([-At[c], -A_(c, g), -f(bot, g, c)])
        for z in range(n):
            if h[z] > 1: add([-r(1, z)])
            if h[z] > 2 and z != g0: add([-r(2, z)])
        if not E.S.solve(): E.S.delete(); continue
        F = E.decode(); E.S.delete(); st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j
        v = top; seq = []
        while v not in seq: seq.append(v); v = F[bot][v]
        c = next(x for x in seq if h[x] == 1); p = seq[seq.index(c) - 1]; ac = a_of(L, F, c); c2 = F[bot][ac]
        rows = [(x, 'a' if le[g0][a_of(L, F, x)] else 'b') for x in range(n) if inR(x, 1) and (le[g0][a_of(L, F, x)] or any(le[g0][y] and b_of(L, F, y) == x for y in range(n)))]
        lab = lambda x: '⊥' if x == bot else 'c' if x == c else "c'" if x == c2 else 'a(c)' if x == ac else ('atom' if h[x] == 1 else f'h{h[x]}')
        C[('g vs a(c)', 'g > a(c)' if le[ac][g0] else 'g ∦ a(c)', 'g vs p', 'g ≥ p' if le[p][g0] else ('g ≤ p' if le[g0][p] else 'g ∥ p'))] += 1
        C[('routes', tuple(sorted(set(f'{lab(x)}:{rt}' for x, rt in rows))))] += 1
        C[("c' kind", lab(c2) if c2 != c2 else ('⊥' if c2 == bot else 'atom'))] += 1
        if shown < 6: shown += 1; print('|L|', n, 'g', nm(g0), 'c', nm(c), 'a(c)', nm(ac), "c'", nm(c2), 'p', nm(p), 'routes', [(nm(x), rt) for x, rt in rows])
for k_, v_ in sorted(C.items(), key=lambda kv: -kv[1])[:20]: print(k_, v_)
