"""Full structural dump of bad1_union_misses_min20.json (log §34.3z²⁰³): elements with height and stage, the height-k
rows with a(x), b(x), their A/B orbits, the genuine A1 configurations with fibres, exceptions and row values, the
forbidden rows, the second tops, and cross-evaluations of every height-k row against the configuration columns."""
import json, sys
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ic
fn = sys.argv[1] if len(sys.argv) > 1 else 'bad1_union_misses_min20.json'
d = json.load(open(fn)); L = ss.Lat(d['sets']); F = d['F']; m = d['m']; n = L.n; le = L.le; h = L.rank; jn = L.join; mt = L.meet
st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j; K = h[m]; k = K - 1
W_ = max(z.bit_length() for z in L.S); nm = lambda z: '{' + ''.join(str(j_) for j_ in range(W_) if L.S[z] >> j_ & 1) + '}'
rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
A = lambda x: a_of(L, F, x); B = lambda x: b_of(L, F, x)
mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for x2 in range(n) if le[x][x2] for y in range(n) for y2 in range(n) if le[y][y2])
print(f'|L| = {n}, K = {K}, k = {k}; monotone {mono}; R_K tight {all(h[z] <= K for z in range(n) if inR(z, K))}; m = {nm(m)} new {inR(m, K) and not inR(m, K - 1)}; ¬IC(m) {not ic(L, F, m)}')
print('elements (name, height, stage):', [(nm(z), h[z], st[z]) for z in range(n)])
tops = [z for z in range(n) if inR(z, K) and h[z] == K]
print('height-K elements of R_K (tops):', [nm(z) for z in tops])
X = [x for x in range(n) if inR(x, k) and h[x] == k]
def orbit(f, x):
    o = [x]
    while f(o[-1]) not in o: o.append(f(o[-1]))
    return o
for x in X:
    ax = A(x)
    kind = 'stationary' if ax == x else 'target' if ax == m else 'other ascending' if le[x][ax] else 'non-ascending'
    pairs = [nm(v) for v in range(n) if le[x][v] and v != x and not le[m][v] and le[F[x][v]][v]]
    print(f'row {nm(x)}: a = {nm(ax)} [{kind}], b = {nm(B(x))}, A-orbit {[nm(z) for z in orbit(A, x)]}, B-orbit {[nm(z) for z in orbit(B, x)]}, '
          f'off-m pre-fixed columns {pairs}')
cfg = [(B(c), c, u) for c in X if B(c) in L.covers_dn[c] and not le[c][A(c)] for u in range(n) if le[c][u] and u != c and not le[m][u] and F[B(c)][u] == c]
for p, c, u in cfg:
    E = [nm(e) for e in range(n) if le[c][e] and e != c and le[e][u] and F[p][e] == p]
    print(f'genuine configuration p = {nm(p)} ⋖ c = {nm(c)}, u = {nm(u)}: t = F(c,u) = {nm(F[c][u])}, a(c) = {nm(A(c))}, exceptions {E}, m ⊔ u = {nm(jn[m][u])}')
    for x in X:
        print(f'   row {nm(x)} vs this configuration: x vs c {rl(x, c)}, x vs u {rl(x, u)}, F(x,u) = {nm(F[x][u])}, F(x, m ⊔ u) = {nm(F[x][jn[m][u]])}, '
              f'F(x, c ⊔ a(c)) = {nm(F[x][jn[c][A(c)]])}, x ⊔ c = {nm(jn[x][c])}, x ∧ c = {nm(mt[x][c])}, F(c, x ⊔ c) = {nm(F[c][jn[x][c]])}')
print('m row values on tops ⊔ m:', [(nm(z), nm(F[m][jn[m][z]])) for z in tops if z != m])
print('a-parents of each second top:', [(nm(z), [nm(x) for x in range(n) if inR(x, k) and le[z][F[x][z]]]) for z in tops if z != m])
print('B-sources of second tops:', [(nm(z), nm(B(z)), st[B(z)]) for z in tops if z != m])
