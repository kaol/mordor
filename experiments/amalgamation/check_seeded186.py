"""Regression check of the seeded dead ends (log §34.3z¹⁸⁶): re-verify the hypotheses from the JSON, confirm the
seeded root (r, z) below stage k has no B-edge (`SeedEdge`), that its only transitions are A-edges to a(z), and
classify every upward cell of a(z) away from m (why the Lean mixed graph stops there).
  python3 check_seeded186.py [FILE.json ...]   (default: the four §34.3z¹⁸⁶ models)"""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ystar, ic
for fn in sys.argv[1:] or ['seeded_deadend_min29.json', 'seeded_deadend_min32.json', 'seeded_topdead_min31.json', 'seeded_badterm_min21.json']:
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m, r, z = d['m'], d['r'], d['z']; n = L.n; le = L.le; h = L.rank
    st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j; K = h[m]; k = K - 1
    mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for x2 in range(n) if le[x][x2] for y in range(n) for y2 in range(n) if le[y][y2])
    mp = b_of(L, F, m)
    new = lambda x, j: inR(x, j) and not inR(x, j - 1) and h[x] == j
    fib = lambda pp, cc: [v for v in range(n) if le[cc][v] and v != cc and not le[m][v] and F[pp][v] == cc]
    sib = lambda pp, cc: new(cc, h[cc]) and inR(pp, h[cc] - 1) and h[pp] == h[cc] - 1 and le[pp][cc] and pp != cc and F[pp][cc] == pp and bool(fib(pp, cc))
    tight = lambda j: all(h[x] <= j for x in range(n) if inR(x, j))
    hyp = {'F monotone': mono, 'R_K, R_{K−1} index-tight': tight(K) and tight(K - 1), 'm new at K': new(m, K), "m′ = b(m) ⋖ m, F(m′,m) ≤ m′": mp in L.covers_dn[m] and le[F[mp][m]][mp],
           'no interval cell at m': not ic(L, F, m), '(r, z) SibConfig': sib(r, z), 'h(z) < k': h[z] < k}
    def bkids(c):
        out = set()
        for pp in range(n):
            if not sib(pp, c): continue
            for v in fib(pp, c):
                for v1 in range(n):
                    if not (le[c][v1] and v1 != c and le[v1][v] and le[F[c][v1]][v1]): continue
                    cands = {v1} | {F[c][u1] for u1 in range(n) if le[c][u1] and u1 != c and le[u1][v1] and le[F[c][u1]][u1]}
                    out |= {y for y in cands if le[y][v1] and le[F[c][y]][c] and new(y, h[c] + 1) and sib(c, y)}
        return out
    akids = lambda c: {y for y in range(n) if le[c][y] and y != c and le[y][F[c][y]] and not le[m][y] and new(y, h[c] + 1)}
    az = a_of(L, F, z)
    print(f'== {fn}: |L| = {n}, K = {K}, k = {k}, h(z) = {h[z]}; hypotheses all hold: {all(hyp.values())}', '' if all(hyp.values()) else hyp,
          f'; non-tight lower stages: {[j for j in range(K - 1) if not tight(j)]}')
    upcell = lambda c: any(le[c][u] and u != c and not le[m][u] and (le[F[c][u]][c] or le[u][F[c][u]]) for u in range(n))
    seen = {z}; todo = [z]; dead = []
    while todo:
        c = todo.pop(); kk = {y for y in range(n) if sib(c, y)} | akids(c)
        if h[c] < k and not kk: dead.append(c)
        for y in kk:
            if h[y] <= k and y not in seen: seen.add(y); todo.append(y)
    print(f'   top graph from z: reached {sorted(seen)}, dead ends below k {dead}, stage-k tops {[(c, upcell(c)) for c in seen if h[c] == k]} (top, UpCell)')
    print(f'   B-edges from (r, z): {sorted(bkids(z))}; A-edges from z: {sorted(akids(z))}' + (f'; a(z) = {az}' if akids(z) else ''))
    if not akids(z): continue
    y = az
    print(f'   a(z): h = {h[y]}, new = {new(y, h[y])}, SibConfig sources = {[p for p in range(n) if sib(p, y)]}, '
          f'B-edges = {sorted(bkids(y))}, A-edges = {sorted(akids(y))}')
    for x in range(n):
        if le[y][x] and x != y and not le[m][x] and (le[F[y][x]][y] or le[x][F[y][x]]):
            kind = 'lower' if le[F[y][x]][y] else 'upper'
            print(f'     cell (a(z), {x}): {kind}, h = {h[x]}, stage = {st[x]}, new at h(a(z))+1 = {new(x, h[y] + 1)}, '
                  f'SibConfig(a(z), x) = {sib(y, x)}, x ∈ R_k with h = k = {inR(x, k) and h[x] == k}')
    ups = [x for x in range(n) if inR(x, k) and h[x] == k and any(le[x][u] and u != x and not le[m][u] and (le[F[x][u]][x] or le[u][F[x][u]]) for u in range(n))]
    print(f'   UpCell witnesses at stage k: {ups}; their relation to a(z): {[("<" if le[y][x] else "∥") for x in ups]}')
