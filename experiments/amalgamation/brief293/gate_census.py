"""Free census (samples only): gates q -> q' (q' = F(q, G) an atom at a corner G of a (q, x)-staircase, x in Z above q)
on stored W0^2 models; candidate ranks rho compared along every gate:
  pre(q) = #{high w : phi(w) >= q};  dep(q) = max{j : q <= t_j};  idx(q) = landing index i(q);  fib(q) = #{high w : phi(w) = q}.
Also: is the exit atom of every non-fixed sink the fixed atom?"""
import sys, collections
sys.path.insert(0, '.'); from corners import staircase, w0sq
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import load_all, dedup
C = collections.Counter()
for name, w in dedup(load_all()):
    if not w.base() or any(w.lam(x) is None for x in w.Z) or not w0sq(w): continue
    le, F, bot, h = w.le, w.F, w.bot, w.h; tb = w.tdesc()
    rho = {'pre': lambda q: sum(1 for y in w.hi if le[q][F[bot][y]]), 'fib': lambda q: sum(1 for y in w.hi if F[bot][y] == q),
           'dep': lambda q: max(j for j, t in enumerate(tb) if le[q][t]), 'idx': lambda q: w.lidx(q)}
    fixed = [q for q in w.atoms if w.fixed(q)]
    for q in w.atoms:
        gates = set()
        for x in w.Z:
            if not le[q][x]: continue
            G, kap, cs = staircase(w, q, x)
            for (l, k) in cs:
                e = F[q][G(l, k)]
                if h[e] == 1: gates.add(e)
        for g in gates:
            for nm, r in rho.items():
                C[(nm, '>' if r(g) > r(q) else ('=' if r(g) == r(q) else '<'))] += 1
            C[('gate target fixed', g in fixed)] += 1
        p = w.lam(q)
        if h[p] == 2 and le[q][p] and all(w.lam(x) == p for x in w.Z if le[q][x]) and F[bot][p] not in (q, bot):
            C[('nonfixed sink exits to fixed atom', F[bot][p] in fixed)] += 1
for k, v in sorted(C.items(), key=str): print(v, k)
