"""An explicit height-3 family refuting RB(3) (log §34.3z¹³²).

Near-pencil on k points: p, q_1..q_m (m = k − 1); lines l_i = {p, q_i}; long line Q = {q_1..q_m}. D = {⊥} ∪ atoms.
F(⊥, ⊤) = p, F(p, ⊤) = l_1, F(p, l_1) = q_1; for j < m: F(q_j, ⊤) = l_{j+1}, F(q_j, l_{j+1}) = q_{j+1};
F(q_m, ⊤) = ⊤; every other cell with an atom row, and the rest of the ⊥ row, is ⊥; every row outside D is ⊤.
Checked here for each k: F monotone, D a cut, and the response run has exactly 2k − 1 non-goal stages
(simulated with the reference `general_sep.response_run`).
  python3 pencil_family.py KMAX
"""
import sys
import separator_stages as ss
from general_sep import response_run

def family(k):
    m = k - 1
    sets = {0, (1 << k) - 1} | {1 << i for i in range(k)} | {1 | (1 << i) for i in range(1, k)} | {((1 << k) - 1) ^ 1}
    L = ss.Lat(sorted(sets, key=lambda x: (bin(x).count('1'), x))); idx = {s: i for i, s in enumerate(L.S)}
    bot, top = L.bot, L.top; p = idx[1]; q = [None] + [idx[1 << i] for i in range(1, k)]
    l = [None] + [idx[1 | (1 << i)] for i in range(1, k)]
    D = [L.S[i] == 0 or bin(L.S[i]).count('1') == 1 for i in range(L.n)]
    F = [[bot] * L.n for _ in range(L.n)]
    for x in range(L.n):
        if not D[x]:
            for y in range(L.n): F[x][y] = top
    F[bot][top] = p; F[p][top] = l[1]; F[p][l[1]] = q[1]
    for j in range(1, m):
        F[q[j]][top] = l[j + 1]; F[q[j]][l[j + 1]] = q[j + 1]
    F[q[m]][top] = top
    return L, F, D

if __name__ == '__main__':
    for k in range(3, int(sys.argv[1]) + 1):
        L, F, D = family(k); n = L.n
        mono = all(L.le[F[a][b]][F[a2][b2]] for a in range(n) for a2 in range(n) if L.le[a][a2]
                   for b in range(n) for b2 in range(n) if L.le[b][b2])
        cut = D[L.bot] and not D[L.top] and all(D[a] for a in range(n) for b in range(n) if L.le[a][b] and D[b])
        _, seq = response_run(L, F, D)
        ok = mono and cut and L.height == 3 and len(seq) == 2 * k - 1
        print(f"k = {k}: |L| = {n}, height {L.height}, monotone {mono}, cut {cut}, response-run length {len(seq)}"
              f" (2k − 1 = {2 * k - 1}) {'OK' if ok else 'FAIL'}", flush=True)
        assert ok
