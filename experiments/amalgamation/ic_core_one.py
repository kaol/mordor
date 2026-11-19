"""Minimal IC↑ core for one stored triple (log §34.3z²¹⁶), and names of its G columns in sampled relaxed models.
   python3 ic_core_one.py FILE.json"""
import sys, json, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from amalg_sat import Enc
from tight_probe import helpers
d = json.load(open(sys.argv[1])); L = ss.Lat(d['sets']); m, w, x = d['m'], d['w'], d['x']
n = L.n; le = L.le; jn = L.join; bot = L.rank.index(0); y = jn[m][w]
mt = lambda a, b: L.S.index(L.S[a] & L.S[b])
nm = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
print('lattice', [nm(i) for i in range(n)]); print('m', nm(m), 'w', nm(w), 'y', nm(y), 'x', nm(x))
E = Enc(L, 1); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u)
E.S.add_clause([f(m, y, w)]); E.S.add_clause([f(bot, w, x)])
guards = {}
def guard(tag, clauses):
    s_ = E.v('g', *tag); guards[s_] = tag
    for c in clauses: E.S.add_clause([-s_] + c)
for z in range(n):
    if not le[z][y]: guard(('G', z), [[-f(m, z, g)] for g in range(n) if le[z][jn[m][g]]])
    if le[x][z] and z != x: guard(('CF', z), [[-fle(x, z, x)], [-yle(x, z)]]); guard(('T', z), [[-f(bot, z, bot)]])
assert not E.S.solve(assumptions=list(guards))
cores = []
for trial in range(4):          # several minimal cores, by rotating the deletion order
    core = list(guards); core = core[trial:] + core[:trial] if trial else core
    i = 0
    while i < len(core):
        t = core[:i] + core[i + 1:]
        if not E.S.solve(assumptions=t): core = t
        else: i += 1
    key = tuple(sorted(guards[s_] for s_ in core))
    if key in [c[0] for c in cores]: continue
    cores.append((key, core))
for key, core in cores:
    print('core:', ' '.join(f'{t[0]}{nm(t[1])}' for t in key))
    gs = [s_ for s_ in core if guards[s_][0] == 'G']
    for gsel in gs:
        zG = guards[gsel][1]; rest = [s_ for s_ in core if s_ != gsel]
        ok = collections.Counter(); k = 0; blk = []
        while k < 6 and E.S.solve(assumptions=rest + blk):
            mod = set(l for l in E.S.get_model() if l > 0); k += 1
            F = [[next(u for u in range(n) if E.vars[('f', a, b, u)] in mod) for b in range(n)] for a in range(n)]
            sv = F[x][y]; t = F[x][w]; s2 = F[x][sv]; t2 = F[x][t]
            yx = L.top
            while jn[x][F[x][yx]] != yx: yx = jn[x][F[x][yx]]
            cand = {'y⊔s': jn[y][sv], 's': sv, 'w⊔s': jn[w][sv], 'm⊔s': jn[m][sv], 'F(x,s)': s2, 'y⊔F(x,s)': jn[y][s2], 's⊔F(x,s)': jn[sv][s2],
                    'm⊔F(x,s)': jn[m][s2], 'w⊔F(x,s)': jn[w][s2], 't': t, 'F(x,t)': t2, 'y⊔F(x,t)': jn[y][t2], 'm⊔F(x,t)': jn[m][t2], 'w⊔F(x,t)': jn[w][t2],
                    'y_x': yx, 'y⊔y_x': jn[y][yx], 'm⊔y_x': jn[m][yx], 'w⊔y_x': jn[w][yx], 'w_x': F[x][yx], 'm⊔w_x': jn[m][F[x][yx]], 'y⊔w_x': jn[y][F[x][yx]],
                    'F(x,⊤)': F[x][L.top], 'm⊔F(x,⊤)': jn[m][F[x][L.top]], 'F(⊥,⊤)': F[bot][L.top], 'm⊔F(⊥,⊤)': jn[m][F[bot][L.top]]}
            for k_, c in cand.items(): ok[k_] += (c == zG)
            cl = E.v('blk', len(blk), gsel); E.S.add_clause([-cl] + [-E.vars[('f', a, b, F[a][b])] for a in (bot, x, m) for b in range(n)]); blk.append(cl)
        print('   G', nm(zG), 'always equals:', [k_ for k_, c in ok.items() if c == k], f'({k} models)')
