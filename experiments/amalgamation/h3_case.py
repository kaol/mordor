"""Height-3 Rise, the open subcase (log §34.3z¹⁵⁸): rigid F, v = F(⊥, ⊤) an atom, w = F(v, ⊤) < ⊤, and
q = F(v, w) an atom ≠ v. Is it possible, and if so how does w enter R₂?  python3 h3_case.py K M SEED COUNT
"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from rstages import stages, a_of, b_of
from rise_sat import lattices

C = collections.Counter(); ex = None
for L in lattices(['h3'] + sys.argv[1:5]):
    n = L.n; le = L.le; rk = L.rank; bot, top = L.bot, L.top
    atoms = [z for z in range(n) if rk[z] == 1]; mids = [z for z in range(n) if rk[z] == 2]
    E = Enc(L, 2); f = lambda x, y, v: E.v('f', x, y, v)
    E.S.add_clause([E.v('A', bot, bot)]); E.S.add_clause([E.v('B', top, top)])
    for c in range(n):
        if c not in (bot, top): E.S.add_clause([-f(c, c, c)])
    sel = []
    for v in atoms:
        for w in mids:
            if not le[v][w]: continue
            for q in atoms:
                if q == v or not le[q][w]: continue
                o = E.v('sel', v, w, q); E.iff_and(o, [f(bot, top, v), f(v, top, w), f(v, w, q)]); sel.append(o)
    if not sel: E.S.delete(); continue
    E.S.add_clause(sel)
    ok = E.S.solve(); C['SAT' if ok else 'UNSAT'] += 1
    if ok:
        F = E.decode(); st = stages(L, F); v = F[bot][top]; w = F[v][top]
        A = [a_of(L, F, x) for x in range(n)]; B = [b_of(L, F, y) for y in range(n)]
        R1 = [z for z in range(n) if st[z] is not None and st[z] <= 1]
        C[('w ∈ R_2', st[w] is not None and st[w] <= 2)] += 1
        C[('w ≤ a(x), x ∈ R_1', any(le[w][A[x]] for x in R1))] += 1
        C[('b(w) ∈ R_1', B[w] in R1)] += 1
        C[('b(w)', 'atom' if rk[B[w]] == 1 else rk[B[w]])] += 1
        if ex is None: ex = (L, F)
    E.S.delete()
for k, v in sorted(C.items(), key=str): print(k, v)
if ex:
    L, F = ex; n = L.n; w_ = max(x.bit_length() for x in L.S); nm = lambda i: '{' + ''.join(str(j) for j in range(w_) if L.S[i] >> j & 1) + '}'
    print('example elements', [nm(z) for z in range(n)])
    for x in range(n): print(' F', nm(x), [nm(F[x][y]) for y in range(n)])
    print(' b', {nm(y): nm(b_of(L, F, y)) for y in range(n)}, 'a', {nm(x): nm(a_of(L, F, x)) for x in range(n)})
