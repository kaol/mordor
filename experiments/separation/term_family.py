"""Explicit near-pencil family with long term1 runs (log §34.3z¹³³).

Near-pencil on k = m + 1 points: p = 0, lines l_i = {0, i} (1 ≤ i ≤ m), long line Λ = {1, ..., m}; height 3.
D = {⊥} ∪ atoms ∪ {l_j : j odd}.  F = make_F(g), the least monotone map above the generators
  g(⊥, ⊤) = {0},  g(⊤, ⊥) = l_1,
  for odd j < m:  g(l_j, ⊤) = l_{j+1},  g(l_j, l_{j+1}) = {j+1},  and g({j+1}, ⊤) = l_{j+2} when j + 2 ≤ m,
  for odd m:      g(l_m, ⊤) = ⊤.
Design: each new line is the only separator of its pair (lines are coatoms), and the long line stays out of the
depth-1 term closure until two atoms of Λ are present.  python3 term_family.py KMAX
"""
import sys
import separator_stages as ss
from general_sep import response_run
from term_rule import term_run

def family(k):
    m = k - 1
    sets = {0, (1 << k) - 1} | {1 << i for i in range(k)} | {1 | (1 << i) for i in range(1, k)} | {((1 << k) - 1) ^ 1}
    L = ss.Lat(sorted(sets, key=lambda x: (bin(x).count('1'), x))); idx = {s: i for i, s in enumerate(L.S)}
    bot, top = L.bot, L.top; at = lambda i: idx[1 << i]; ln = lambda i: idx[1 | (1 << i)]
    g = {(bot, top): at(0), (top, bot): ln(1)}
    for j in range(1, m, 2):
        g[(ln(j), top)] = ln(j + 1); g[(ln(j), ln(j + 1))] = at(j + 1)
        if j + 2 <= m: g[(at(j + 1), top)] = ln(j + 2)
    if m % 2: g[(ln(m), top)] = top
    D = [L.S[i] == 0 or bin(L.S[i]).count('1') == 1 or
         (bin(L.S[i]).count('1') == 2 and L.S[i] & 1 and (L.S[i] ^ 1).bit_length() % 2 == 0) for i in range(L.n)]
    return L, ss.make_F(L, g), D

if __name__ == '__main__':
    for k in range(3, int(sys.argv[1]) + 1):
        L, F, D = family(k); n = L.n
        mono = all(L.le[F[a][b]][F[a2][b2]] for a in range(n) for a2 in range(n) if L.le[a][a2]
                   for b in range(n) for b2 in range(n) if L.le[b][b2])
        cut = D[L.bot] and not D[L.top] and all(D[a] for a in range(n) for b in range(n) if L.le[a][b] and D[b])
        d1, s1 = term_run(L, F, D, 'term1_all'); d2, s2 = term_run(L, F, D, 'term1_one')
        deep = [len(term_run(L, F, D, 'all', depth=d)[1]) for d in (2, 3, 4)]
        mts = [len(term_run(L, F, D, 'all', meets=True, depth=d)[1]) for d in (1, 2, None)]
        print(f"k = {k}: |L| = {n}, height {L.height}, monotone {mono}, cut {cut}, term1_all {len(s1)} (descending {d1}), "
              f"term1_one {len(s2)}, (F,∨)-depth 2/3/4 {deep}, with meets depth 1/2/ω {mts}, "
              f"response {len(response_run(L, F, D)[1])}, existential maximal minimum {ss.exist_min(L, F, D)}", flush=True)
