"""The line-cycle family: maximal-separator descent fails at edge-height 3 (log §34.3z¹³⁶).

Near-pencil on k points 0, …, m (m = k − 1): lines l_i = {0, i}, long line Λ = {1, …, m}; height 3.
D = L ∖ {⊤}, so the only cross pairs are (x, ⊤).  F = make_F(g), the least monotone map above
  g(⊥, ⊤) = {0},   g(l_i, ⊤) = l_{i+1}  (indices mod m, a cycle on the lines through 0).
The maximal separators of (⊥, ⊤) are the lines; a line is a coatom, so the only separator of (l_i, ⊤) is l_{i+1},
with gap 4 = 3 + 3 − 2. Every maximal run therefore has stage gaps 6, 4, 4, … and walks the cycle: the existential
minimum is m = k − 1 and, for k ≥ 4, no maximal run has strictly decreasing maximum gap. With general separators the
response {0} ends the run at once. (F({0}, ⊤) ≤ ⋀ lines = {0} is a lower witness.)
  python3 cycle_family.py KMAX | tree FILE   (all maximal runs of a stored instance)
"""
import sys, itertools
import separator_stages as ss
from general_sep import exist_desc, gseps

def family(k):
    m = k - 1
    sets = {0, (1 << k) - 1} | {1 << i for i in range(k)} | {1 | (1 << i) for i in range(1, k)} | {((1 << k) - 1) ^ 1}
    L = ss.Lat(sorted(sets, key=lambda x: (bin(x).count('1'), x))); idx = {s: i for i, s in enumerate(L.S)}
    lines = [idx[1 | (1 << i)] for i in range(1, k)]
    g = {(L.bot, L.top): idx[1]}
    for i, l in enumerate(lines): g[(l, L.top)] = lines[(i + 1) % m]
    return L, ss.make_F(L, g), [x != L.top for x in range(L.n)]

def tree(L, F, D, T=None, depth=0, M0=None, nm=str):
    """Print every maximal-separator run, cut where the maximum gap fails to drop."""
    T = T or ss.mclose(L, {L.bot, L.top}); bad = ss.bad_pairs(L, F, D, T); pad = '  ' * depth
    if not bad or any(L.le[y][F[x][y]] for x, y in bad): print(pad + 'GOAL', 'stuck' if bad else 'separated'); return
    M = max(L.rank[y] + L.height - L.rank[x] for x, y in bad); stop = M0 is not None and M >= M0
    print(pad + f"T = {sorted(nm(e) for e in T)}, max gap {M}{' (no drop)' if stop else ''}, "
          f"bad (x, y, F) {[(nm(x), nm(y), nm(F[x][y])) for x, y in bad]}")
    if stop: return
    for ch in itertools.product(*[ss.max_separators(L, F[x][y], y) for x, y in bad]):
        print(pad + ' choose', [nm(s) for s in ch]); tree(L, F, D, ss.mclose(L, set(T) | set(ch)), depth + 1, M, nm)

if __name__ == '__main__':
    if sys.argv[1] == 'tree':
        import json
        d = json.load(open(sys.argv[2])); L = ss.Lat(d['sets'])
        nm = lambda i: '{' + ''.join(str(j) for j in range(L.S[-1].bit_length()) if L.S[i] >> j & 1) + '}'
        tree(L, d['F'], d['D'], nm=nm); sys.exit()
    for k in range(3, int(sys.argv[1]) + 1):
        L, F, D = family(k); n = L.n
        mono = all(L.le[F[a][b]][F[a2][b2]] for a in range(n) for a2 in range(n) if L.le[a][a2]
                   for b in range(n) for b2 in range(n) if L.le[b][b2])
        cut = D[L.bot] and not D[L.top] and all(D[a] for a in range(n) for b in range(n) if L.le[a][b] and D[b])
        em = ss.exist_min(L, F, D, limit=10 ** 7)
        md = exist_desc(L, F, D, lambda L, F, x, y: ss.max_separators(L, F[x][y], y), limit=10 ** 7)
        gd = exist_desc(L, F, D, gseps, limit=10 ** 7)
        print(f"k = {k}: |L| = {n}, height {L.height}, monotone {mono}, cut {cut}, existential minimum {em} (k − 1 = {k - 1}), "
              f"maximal-separator descent {md}, general-separator descent {gd}", flush=True)
