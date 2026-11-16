"""Print a single_claims.py model: elements, stages, F table, the singleton configuration and the a/b values (log §34.3z¹⁶⁴).
  python3 show_model.py FILE.json"""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ystar, ic
d = json.load(open(sys.argv[1])); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; n = L.n; le = L.le; h = L.rank
st = stages(L, F); W = max(x.bit_length() for x in L.S)
nm = lambda z: '{' + ''.join(str(i) for i in range(W) if L.S[z] >> i & 1) + '}'
print('elements (height, stage):', ', '.join(f'{nm(z)}:{h[z]},{st[z]}' for z in range(n)))
print('F rows:'); [print('  ', nm(x), '->', ' '.join(nm(F[x][y]) for y in range(n))) for x in range(n)]
print('a:', {nm(x): nm(a_of(L, F, x)) for x in range(n)}); print('b:', {nm(y): nm(b_of(L, F, y)) for y in range(n)})
ys = ystar(L, F, m); w = F[m][ys]; mp = b_of(L, F, m); K = h[m]
dd = ys
while True:
    nx = L.join[mp][F[mp][dd]]
    if nx == dd: break
    dd = nx
print(f"m {nm(m)} (h {K}, stage {st[m]}), m' = b(m) {nm(mp)} (stage {st[mp]}), F(m',m) {nm(F[mp][m])}, y* {nm(ys)}, w {nm(w)} (stage {st[w]}), d* {nm(dd)}, ic(m) {ic(L, F, m)}")
print('height-K elements of R_K:', [nm(z) for z in range(n) if h[z] == K and st[z] is not None and st[z] <= K])
