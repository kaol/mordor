"""Inspect the §34.3z¹⁷¹ counterexamples: the immediate drop r = F(m′, w), the tops of R_k, every descent witness
(x, v), and the raw feeder orbit r, F(m′, r), … to its fixed point e.   python3 check_drop171.py FILE.json ..."""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ystar
for fn in sys.argv[1:]:
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; n = L.n; le = L.le; h = L.rank; K = h[m]
    st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j
    W = max(x.bit_length() for x in L.S); nm = lambda i: '{' + ''.join(str(j) for j in range(W) if L.S[i] >> j & 1) + '}'
    mp = b_of(L, F, m); w = F[m][ystar(L, F, m)]; r = F[mp][w]
    Tk = [x for x in range(n) if inR(x, K - 1) and h[x] == K - 1]
    def dw(x, v): return le[x][v] and x != v and le[F[x][v]][v] and not le[m][v] and all(le[x][F[x][u]] for u in range(n) if le[x][u] and u != x and le[u][v] and le[F[x][u]][u])
    gen = [(x, v) for x in Tk for v in range(n) if dw(x, v)]
    e = r; orb = [r]
    while F[mp][e] != e: e = F[mp][e]; orb.append(e)
    rel = lambda x, y: '=' if x == y else '<' if le[x][y] else '>' if le[y][x] else '∥'
    print(f"{fn}: |L|={n} K={K} m={nm(m)} m'={nm(mp)} w={nm(w)} r={nm(r)} (h {h[r]}, stage {st[r]}, a(r) {nm(a_of(L, F, r))}) "
          f"T_k={[nm(x) for x in Tk]} raw orbit {[nm(x) for x in orb]} e vs m' {rel(e, mp)} a(m')={nm(a_of(L, F, mp))}")
    print('   witnesses', [(nm(x), nm(v), 'x vs r', rel(x, r), 'v vs w', rel(v, w)) for x, v in gen])
    for x in Tk:
        if le[x][r]: print('   top x ≤ r:', nm(x), 'F(x,w)', nm(F[x][w]), 'bad cols on (x,w]', [nm(u) for u in range(n) if le[x][u] and u != x and le[u][w] and le[F[x][u]][u] and not le[x][F[x][u]]])
