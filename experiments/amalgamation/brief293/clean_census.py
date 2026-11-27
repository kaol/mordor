"""Free census (samples only) on stored W0 models: is the mu-fixed atom 'clean' (phi(r_q) = q and every corner G of
every (q, x)-staircase, x in Z above q, has phi(G) >= q)?  Are non-fixed atoms clean?  Does the fixed atom maximise
|phi^-1(up q) & high|?"""
import sys, collections
sys.path.insert(0, '.'); from corners import staircase
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import load_all, dedup
C = collections.Counter()
for name, w in dedup(load_all()):
    if not (w.w0flat() and w.w0()): continue
    le, F, bot = w.le, w.F, w.bot
    def clean(q):
        if F[bot][w.last_hi(q)] != q: return False
        for x in w.Z:
            if not le[q][x]: continue
            G, kap, cs = staircase(w, q, x)
            if any(not le[q][F[bot][G(l, k)]] for (l, k) in cs): return False
        return True
    pre = {q: sum(1 for y in w.hi if le[q][F[bot][y]]) for q in w.atoms}
    mx = max(pre.values())
    for q in w.atoms:
        C[('fixed' if w.fixed(q) else 'notfixed', 'clean' if clean(q) else 'unclean', 'maxpre' if pre[q] == mx else 'notmax')] += 1
for k, v in sorted(C.items()): print(v, k)
