"""Room coordinates of the probe corpora (no search): |L|, height, width (largest antichain), and k = the largest number
of height-2 elements above one atom (a TwoRowTb counterexample needs an atom q with k >= 2 rows of Z above it, so that
a 3-row meet column can differ from every 2-row meet)."""
import sys, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation'); sys.path.insert(0, '/home/user/mordor/experiments/separation')
from tight_probe import lattices
import bank
for spec in [s.split() for s in sys.argv[1:]]:
    rows = []
    for L in lattices(spec):
        if L.rank[L.top] < 3: continue
        h = L.rank; at = [q for q in range(L.n) if h[q] == 1]
        k = max(sum(1 for m in range(L.n) if h[m] == 2 and L.le[q][m]) for q in at)
        rows.append((L.n, L.height, bank.width(L), k))
    ns = [r[0] for r in rows]; hs = sorted(set(r[1] for r in rows)); ws = [r[2] for r in rows]; ks = [r[3] for r in rows]
    print(' '.join(spec), f'| {len(rows)} lattices | |L| {min(ns)}-{max(ns)} | H {hs} | width {min(ws)}-{max(ws)} | k {min(ks)}-{max(ks)} (k>=2 on {sum(1 for x in ks if x >= 2)})')
