"""Name the single G-instance of the IC↑ cores (log §34.3z²¹⁵).

For each (m, w, x) whose minimal core (as in ic_core.py) contains one G(zG): drop it, sample models of the relaxed
problem (the core's other guards only), and test which F-expressions equal zG in every model.
   python3 ic_gname.py (sweep N MAX | closure K M SEED CNT)
"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
C = collections.Counter(); NG = 0
for L in lattices(sys.argv[1:]):
    n = L.n; le = L.le; jn = L.join; bot = L.rank.index(0); h = L.rank
    mt = lambda a, b: L.S.index(L.S[a] & L.S[b])
    for m in range(n):
        if m == L.top: continue
        for w in range(n):
            if le[m][w]: continue
            y = jn[m][w]
            for x in range(n):
                if h[x] != 1 or x == w or not le[x][w] or le[x][m]: continue
                E = Enc(L, 1); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u)
                E.S.add_clause([f(m, y, w)]); E.S.add_clause([f(bot, w, x)])
                guards = {}
                def guard(tag, clauses):
                    s_ = E.v('g', *tag); guards[s_] = tag
                    for c in clauses: E.S.add_clause([-s_] + c)
                for z in range(n):
                    if not le[z][y]: guard(('G', z), [[-f(m, z, g)] for g in range(n) if le[z][jn[m][g]]])
                    if le[x][z] and z != x:
                        guard(('CF', z), [[-fle(x, z, x)], [-yle(x, z)]]); guard(('T', z), [[-f(bot, z, bot)]])
                if E.S.solve(assumptions=list(guards)): E.S.delete(); continue
                core = E.S.get_core() or list(guards); i = 0
                while i < len(core):
                    t = core[:i] + core[i + 1:]
                    if not E.S.solve(assumptions=t): core = t
                    else: i += 1
                gs = [s_ for s_ in core if guards[s_][0] == 'G']
                if len(gs) != 1: E.S.delete(); continue
                NG += 1; zG = guards[gs[0]][1]; rest = [s_ for s_ in core if s_ not in gs]
                ok = collections.Counter(); k = 0; blk = []
                while k < 6 and E.S.solve(assumptions=rest + blk):
                    mod = set(l for l in E.S.get_model() if l > 0); k += 1
                    F = [[next(u for u in range(n) if E.vars[('f', a, b, u)] in mod) for b in range(n)] for a in range(n)]
                    t = F[x][w]; sy = F[x][y]
                    cand = {'y⊔F(x,y)': jn[y][sy], 'w⊔F(x,y)': jn[w][sy], 'y⊔t': jn[y][t], 'w⊔t': jn[w][t], 'm⊔F(x,y)': jn[m][sy],
                            'm⊔t': jn[m][t], 'F(x,y)': sy, 't': t, 'x⊔F(m,⊤)': jn[x][F[m][L.top]], 'm⊔F(m,y⊔F(x,y))': jn[m][F[m][jn[y][sy]]],
                            'y⊔F(x,⊤)': jn[y][F[x][L.top]], 'w⊔F(x,⊤)': jn[w][F[x][L.top]], 'm⊔F(x,⊤)': jn[m][F[x][L.top]]}
                    fam = {jn[a][sv] for a in (bot, x, w, m, y) for sv in (sy, t)}
                    cand['a⊔s (a ∈ {⊥,x,w,m,y*}, s ∈ {F(x,y*), t})'] = zG if zG in fam else -1
                    cand['zG ≥ w'] = zG if le[w][zG] else -1
                    for k_, c in cand.items(): ok[k_] += (c == zG)
                    # block this model on the relevant rows
                    cl = E.v('blk', len(blk), m, w, x); E.S.add_clause([-cl] + [-E.vars[('f', a, b, F[a][b])] for a in (bot, x, m) for b in range(n)]); blk.append(cl)
                for k_, c in ok.items(): C[(k_, 'always = zG', c == k)] += 1
                if False:
                    nm = lambda i_: '{' + ''.join(str(j) for j in range(8) if L.S[i_] >> j & 1) + '}'
                    mod = None
                    if E.S.solve(assumptions=rest):
                        mod = set(l for l in E.S.get_model() if l > 0)
                        F = [[next(u for u in range(n) if E.vars[('f', a, b, u)] in mod) for b in range(n)] for a in range(n)]
                        print(f'|L|={n} m={nm(m)} w={nm(w)} y={nm(y)} x={nm(x)} zG={nm(zG)} F(x,y)={nm(F[x][y])} t={nm(F[x][w])} F(x,⊤)={nm(F[x][L.top])} matches:', [k_ for k_, c in ok.items() if c == k], 'core:', ' '.join(f'{guards[s_][0]}{nm(guards[s_][1])}' for s_ in core))
                E.S.delete()
print('cores with one G instance:', NG)
for k_, v_ in sorted(C.items(), key=str): print(k_, v_)
