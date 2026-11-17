"""Regression check for §34.3z¹⁸⁸: (a) `cone_mixfail_min16.json`, a feeder root that is Good in the Lean top graph but
not in the mixed graph — print the good top-graph path and mark each B-edge with whether it is a SeedEdge (some source);
(b) the early-column roots of `fork_root_bad_L_min19.json` (= `chain_rescue_fail_min19.json`) and
`cone_early_min28.json`: the root, the stage-k UpCell witnesses x, and whether b(x) = x ∧ z < z is a B-source of x.   python3 check_cone188.py"""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ystar, ic

def load(fn):
    d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; n = L.n; le = L.le; h = L.rank
    st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j; K = h[m]; k = K - 1
    W_ = max(x.bit_length() for x in L.S); nm = lambda q: '{' + ''.join(str(j_) for j_ in range(W_) if L.S[q] >> j_ & 1) + '}'
    mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for x2 in range(n) if le[x][x2] for y in range(n) for y2 in range(n) if le[y][y2])
    mp = b_of(L, F, m); tight = lambda j: all(h[x] <= j for x in range(n) if inR(x, j))
    new = lambda x, j: inR(x, j) and not inR(x, j - 1) and h[x] == j
    hyp = mono and tight(K) and tight(K - 1) and new(m, K) and mp in L.covers_dn[m] and le[F[mp][m]][mp] and not ic(L, F, m)
    return d, L, F, m, n, le, h, st, inR, K, k, nm, mp, new, hyp

d, L, F, m, n, le, h, st, inR, K, k, nm, mp, new, hyp = load('cone_mixfail_min16.json')
fib = lambda pp, cc: [v for v in range(n) if le[cc][v] and v != cc and not le[m][v] and F[pp][v] == cc]
sib = lambda pp, cc: inR(pp, h[pp]) and new(cc, h[pp] + 1) and le[pp][cc] and pp != cc and F[pp][cc] == pp and bool(fib(pp, cc))
node = lambda x: inR(x, h[x]) and 1 <= h[x] <= k
def kids(x):
    out = {}
    for y in range(n):
        if not (le[x][y] and y != x and new(y, h[x] + 1)): continue
        if sib(x, y): out[y] = 'B'
        elif le[y][F[x][y]] and not le[m][y]: out[y] = 'A'
    return out
def seedkids(c):
    out = set()
    for pp in range(n):
        if not sib(pp, c): continue
        for v in fib(pp, c):
            for v1 in range(n):
                if not (le[c][v1] and v1 != c and le[v1][v] and le[F[c][v1]][v1]): continue
                cands = {v1} | {F[c][u1] for u1 in range(n) if le[c][u1] and u1 != c and le[u1][v1] and le[F[c][u1]][u1]}
                out |= {y for y in cands if le[y][v1] and le[F[c][y]][c] and sib(c, y)}
    return out
upat = lambda x: any(le[x][u] and u != x and not le[m][u] and (le[F[x][u]][x] or le[u][F[x][u]]) for u in range(n))
root = d['root']
print(f"== cone_mixfail_min16.json: |L| = {n}, K = {K}, k = {k}; harness hypotheses hold: {hyp}; root {nm(root)} (stage {h[root]}), "
      f"SibConfig sources of the root: {[nm(p) for p in range(n) if sib(p, root)]}")
def paths(x):
    if h[x] == k: return [[x]] if upat(x) else []
    return [[x] + p for y in kids(x) if h[y] <= k for p in paths(y)]
for p in paths(root):
    print('   good top path:', ' → '.join(f"{nm(a)} -{kids(a)[b]}{'(SeedEdge)' if kids(a)[b] == 'B' and b in seedkids(a) else ''}→" for a, b in zip(p, p[1:])) + f' {nm(p[-1])} (UpAt)')
for x in [x for x in range(n) if node(x) and le[root][x]]:
    if kids(x): print(f'   {nm(x)}: children {[(nm(y), t) for y, t in kids(x).items()]}, SeedEdge children {[nm(y) for y in seedkids(x)]}, a(x) = {nm(a_of(L, F, x))}')

for fn in ['fork_root_bad_L_min19.json', 'cone_early_min28.json']:
    d, L, F, m, n, le, h, st, inR, K, k, nm, mp, new, hyp = load(fn)
    upat = lambda x: any(le[x][u] and u != x and not le[m][u] and (le[F[x][u]][x] or le[u][F[x][u]]) for u in range(n))
    fib = lambda pp, cc: [v for v in range(n) if le[cc][v] and v != cc and not le[m][v] and F[pp][v] == cc]
    sib = lambda pp, cc: inR(pp, h[pp]) and new(cc, h[pp] + 1) and le[pp][cc] and pp != cc and F[pp][cc] == pp and bool(fib(pp, cc))
    w = F[m][ystar(L, F, m)]; r, e, i = mp, w, 0
    while True:
        t = F[r][e]
        if le[t][r] or le[e][t]: z = e; break
        if le[r][t]: e = t; continue
        q = b_of(L, F, r); e2 = F[q][e]
        if le[e2][q]: r, z, i = q, e, i + 1; break
        r, e, i = q, e2, i + 1
    rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
    print(f"== {fn} (early column): |L| = {n}, K = {K}, k = {k}; hypotheses hold: {hyp}; m = {nm(m)}, m′ = {nm(mp)}, w = {nm(w)}; "
          f"non-tight stages ≤ k: {[j for j in range(k + 1) if not all(h[x] <= j for x in range(n) if inR(x, j))]}")
    print(f"   root (r, z) = ({nm(r)}, {nm(z)}): stage(z) = {st[z]}, h(z) = {h[z]}, F(r, z) = {nm(F[r][z])}, UpAt(z) = {upat(z)}")
    for x in range(n):
        if inR(x, k) and h[x] == k and upat(x):
            s_ = b_of(L, F, x)
            print(f"   UpCell witness x = {nm(x)}: b(x) = {nm(s_)} = x ∧ z: {s_ == L.meet[x][z]}, b(x) < z: {le[s_][z] and s_ != z}, "
                  f"stage(b(x)) = {st[s_]}, h(b(x)) = {h[s_]}, SibConfig(b(x), x) (a B-edge b(x) → x) = {sib(s_, x)}, x vs z: {rl(x, z)}, x vs r: {rl(x, r)}")
