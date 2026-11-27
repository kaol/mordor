"""Free check (no search) of the descent-maximal normal form F# on every stored model that lies in W0^desc
(= W0-flat with no height-2 row of Z landing on itself; contains W0).  Paper claim (brief §2, A1/A2):
  F#(bot, .) = F(bot, .);  F#(x, .) = top for x not in Z;
  F#(x, y) = meet over x' in Z with x <= x' of F(x', sigma_{x'}(y))   for x in Z \\ {bot},
  where sigma_{x'}(y) = least element of row x''s descent (from top) that is >= y.
Then F# is monotone, F <= F# on rows of Z, every row of Z has the same descent, Z and mu are unchanged, and F# is in W0
(Ta and Tb at every row of Z).  Also checks the M2-only normalization F' (F'(m,y) = F(m, sigma_m(y)) at high y)."""
import sys; sys.path.insert(0, '.'); from world import *
from collections import Counter
def mu(w, x):
    p = w.lam(x); return p if w.F[w.bot][p] == w.bot else w.F[w.bot][p]
def sharp(w, only_M2=False):
    n, le, h, L = w.n, w.le, w.h, w.L; Zs = set(w.Z); D = {x: w.desc(x) for x in w.Z}
    def sigma(x, y): return min((z for z in D[x] if le[y][z]), key=lambda z: h[z])
    G = [[w.top] * n for _ in range(n)]
    for y in range(n): G[w.bot][y] = w.F[w.bot][y]
    for x in w.Z:
        if x == w.bot: continue
        for y in range(n):
            if only_M2:
                G[x][y] = w.F[x][sigma(x, y)] if (h[x] == 2 and h[y] >= 3) else w.F[x][y]
            else:
                v = w.top
                for x2 in w.Z:
                    if le[x][x2]: v = L.meet[v][w.F[x2][sigma(x2, y)]]
                G[x][y] = v
    return G
print(__doc__)
C = Counter()
for name, w in dedup(load_all()):
    if not w.w0flat() or w.witnesses(): continue
    tag = 'W0' if w.w0() else 'W0desc-not-W0'
    for kind in ('F#', "F'(M2 only)"):
        G = sharp(w, only_M2=(kind != 'F#')); v = W(w.sets, G)
        ok_m = v.mono; ok_z = v.Z == w.Z
        ok_d = ok_z and all(v.desc(x) == w.desc(x) for x in w.Z)
        ok_mu = ok_d and all(mu(v, x) == mu(w, x) for x in w.Z)
        ok_w0 = ok_m and v.w0()
        ok_le = all(w.le[w.F[x][y]][G[x][y]] for x in w.Z for y in range(w.n))
        C[(tag, kind, 'mono', ok_m, 'Z', ok_z, 'desc', ok_d, 'mu', ok_mu, 'W0', ok_w0, 'F<=F#', ok_le)] += 1
for k in sorted(C, key=str): print(k, C[k])
