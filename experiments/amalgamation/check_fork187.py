"""Regression check of the §34.3z¹⁸⁷ fork models: re-verify the harness hypotheses, rebuild the Lean top graph, and
show (a) the all-bad fork of `fork_allbad_new_min17.json` (a node below k whose every top-edge child is bad) and
whether it is reachable from the feeder descent root; (b) the bad descent root of `fork_root_bad_L_min19.json`.
  python3 check_fork187.py [FILE.json ...]"""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ystar, ic
for fn in sys.argv[1:] or ['fork_allbad_new_min17.json', 'fork_allbad_new_sib_min31.json', 'fork_root_bad_L_min19.json']:
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; n = L.n; le = L.le; h = L.rank
    st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j; K = h[m]; k = K - 1
    W_ = max(x.bit_length() for x in L.S); nm = lambda q: '{' + ''.join(str(j_) for j_ in range(W_) if L.S[q] >> j_ & 1) + '}'
    mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for x2 in range(n) if le[x][x2] for y in range(n) for y2 in range(n) if le[y][y2])
    mp = b_of(L, F, m); tight = lambda j: all(h[x] <= j for x in range(n) if inR(x, j))
    new = lambda x, j: inR(x, j) and not inR(x, j - 1) and h[x] == j
    hyp = {'F monotone': mono, 'R_K, R_{K−1} tight': tight(K) and tight(K - 1), 'm new at K': new(m, K),
           "m′ = b(m) ⋖ m, F(m′,m) ≤ m′": mp in L.covers_dn[m] and le[F[mp][m]][mp], 'no interval cell at m': not ic(L, F, m)}
    fib = lambda pp, cc: [v for v in range(n) if le[cc][v] and v != cc and not le[m][v] and F[pp][v] == cc]
    node = lambda x: inR(x, h[x]) and 1 <= h[x] <= k
    def kids(x):
        out = {}
        for y in range(n):
            if not (le[x][y] and y != x and new(y, h[x] + 1)): continue
            if F[x][y] == x and fib(x, y): out[y] = 'B'
            elif le[y][F[x][y]] and not le[m][y]: out[y] = 'A'
        return out
    upat = lambda x: any(le[x][u] and u != x and not le[m][u] and (le[F[x][u]][x] or le[u][F[x][u]]) for u in range(n))
    X = [x for x in range(n) if node(x)]; KK = {x: kids(x) for x in X}; good = {}
    for s in range(k, 0, -1):
        for x in X:
            if h[x] == s: good[x] = upat(x) if s == k else any(good.get(y, False) for y in KK[x] if h[y] <= k)
    w = F[m][ystar(L, F, m)]; r, e, i = mp, w, 0
    while True:
        t = F[r][e]
        if le[t][r] or le[e][t]: z = e; break
        if le[r][t]: e = t; continue
        q = b_of(L, F, r); e2 = F[q][e]
        if le[e2][q]: r, z, i = q, e, i + 1; break
        r, e, i = q, e2, i + 1
    print(f'== {fn}: |L| = {n}, K = {K}, k = {k}; hypotheses all hold: {all(hyp.values())}', '' if all(hyp.values()) else hyp)
    print(f'   m = {nm(m)}, m′ = {nm(mp)}, w = {nm(w)}; descent depth {i}, root (r, z) = ({nm(r)}, {nm(z)}), h(z) = {h[z]}, '
          f'z new = {new(z, h[z])}, F(r, z) = {nm(F[r][z])}, z ∈ R_(h(z)−1) (early) = {inR(z, h[z] - 1)}, UpAt(z) = {upat(z)}')
    seen = set()
    if z in good:
        seen = {z}; todo = [z]
        while todo:
            x = todo.pop()
            for y in KK[x]:
                if h[y] <= k and y not in seen: seen.add(y); todo.append(y)
        print(f'   top graph from z: {sorted(nm(x) for x in seen)}; Good(z) = {good[z]}')
    for x in X:
        if h[x] < k and KK[x] and not any(good[y] for y in KK[x]):
            print(f'   ALL-BAD FORK at {nm(x)} (stage {h[x]}, new {new(x, h[x])}, reachable from z: {x in seen}, x vs m′: {"<" if le[x][mp] else ">" if le[mp][x] else "∥"})')
            for y, ty in KK[x].items():
                why = ('dead end below k' if not KK[y] else 'children all bad') if h[y] < k else 'stage-k top without an upward cell away from m'
                print(f'     child {nm(y)}: {ty}, stage {h[y]}, {why}; F(x, y) = {nm(F[x][y])}, fibre S(x, y; m) = {[nm(v) for v in fib(x, y)]}')
    ups = [nm(x) for x in range(n) if inR(x, k) and h[x] == k and upat(x)]
    print(f'   UpCell witnesses at stage k: {ups}')
