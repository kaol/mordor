"""Free census (samples only) over stored models: corner-clean atoms (every corner G of every (q,x)-staircase,
x in Z above q, has phi(G) >= q) and sinks (every row of Z above q lands at lambda(q), a height-2 cover of q).
Worlds recomputed from the definitions: W0, W0^2 \\ W0, and relaxed NoFix models (base world + every row of Z lands +
lambda(m) not <= m, any Tb sub-world) for comparison."""
import sys, collections
sys.path.insert(0, '.'); from corners import staircase, w0sq
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import load_all, dedup
C = collections.Counter()
for name, w in dedup(load_all()):
    if not w.base() or any(w.lam(x) is None for x in w.Z): continue
    if any(w.h[x] == 2 and w.le[w.lam(x)][x] for x in w.Z): continue
    if not all(w.Ta(x) for x in w.Z): continue
    tag = 'W0' if (w.w0flat() and w.w0()) else ('W0sq\\W0' if w0sq(w) else 'relaxed')
    if tag == 'relaxed' and not w.nofix(): continue
    le, F, bot, h = w.le, w.F, w.bot, w.h
    for q in w.atoms:
        cc = True
        for x in w.Z:
            if not le[q][x]: continue
            G, kap, cs = staircase(w, q, x)
            if any(not le[q][F[bot][G(l, k)]] for (l, k) in cs): cc = False
        p = w.lam(q)
        sink = h[p] == 2 and le[q][p] and all(w.lam(x) == p for x in w.Z if le[q][x])
        ex = None if not sink else ('fixed' if F[bot][p] == q else ('exit to other atom' if F[bot][p] != bot else 'p in Z'))
        C[(tag + ('-nofix' if w.nofix() else ''), 'cornerclean' if cc else '-', 'sink' if sink else '-', ex)] += 1
for k, v in sorted(C.items(), key=str): print(v, k)
