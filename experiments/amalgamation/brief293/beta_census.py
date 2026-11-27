"""Free census (samples only): beta = meet of phi over the high elements; which stored W0 models have an atom q of Z
with phi(w) >= q for every high w (hypothesis H1 of the UniformFibre theorem) and phi(r_q) in Z (UF')."""
import sys, collections, functools
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import load_all, dedup
C = collections.Counter()
for name, w in dedup(load_all()):
    if not (w.w0flat() and w.w0()): continue
    d, N = w.dN(); br = 'a' if w.h[d] == 2 else 'atom'
    beta = functools.reduce(lambda a, b: w.L.meet[a][b], [w.F[w.bot][y] for y in w.hi], w.top)
    H1 = [q for q in w.atoms if w.le[q][beta]]
    UF = [q for q in H1 if w.F[w.bot][w.F[w.bot][w.last_hi(q)]] == w.bot]
    C[(br, 'N1' if N == 1 else 'N>=2', 'h(beta)=%d' % w.h[beta], 'H1 atoms %d' % len(H1), 'UF %d' % len(UF))] += 1
for k, v in sorted(C.items()): print(v, k)
