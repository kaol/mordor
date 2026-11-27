"""Save (copies of) the stored W0 models that refute this brief's located side-candidates (free, from the definitions):
  CleanExists : some atom q of Z has phi(r_q) = q and every corner G of every (q, x)-staircase has phi(G) >= q
  SinkExitFix : the exit atom phi(lambda(q)) of a non-fixed sink q is mu-fixed
  GateRank(r) : along every gate q -> q' (atom colour at a staircase corner) r(q') > r(q), r in pre, fib, dep, idx
Each file: list of {sets, F, source, refutes}."""
import sys, json, collections
sys.path.insert(0, '.'); from corners import staircase, w0sq
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import load_all, dedup
out = collections.defaultdict(list)
for name, w in dedup(load_all()):
    if not (w.w0flat() and w.w0()): continue
    le, F, bot, h = w.le, w.F, w.bot, w.h; tb = w.tdesc()
    def corners_ok(q):
        for x in w.Z:
            if not le[q][x]: continue
            G, kap, cs = staircase(w, q, x)
            if any(not le[q][F[bot][G(l, k)]] for (l, k) in cs): return False
        return True
    rec = lambda tag: out[tag].append(dict(sets=w.sets, F=w.F, source=name, refutes=tag))
    if not any(F[bot][w.last_hi(q)] == q and corners_ok(q) for q in w.atoms): rec('CleanExists')
    fixed = [q for q in w.atoms if w.fixed(q)]
    for q in w.atoms:
        p = w.lam(q)
        if h[p] == 2 and le[q][p] and all(w.lam(x) == p for x in w.Z if le[q][x]) and F[bot][p] not in (q, bot) and F[bot][p] not in fixed:
            rec('SinkExitFix'); break
    rho = {'pre': lambda q: sum(1 for y in w.hi if le[q][F[bot][y]]), 'fib': lambda q: sum(1 for y in w.hi if F[bot][y] == q),
           'dep': lambda q: max(j for j, t in enumerate(tb) if le[q][t]), 'idx': lambda q: w.lidx(q)}
    bad = set()
    for q in w.atoms:
        for x in w.Z:
            if not le[q][x]: continue
            G, kap, cs = staircase(w, q, x)
            for (l, k) in cs:
                e = F[q][G(l, k)]
                if h[e] == 1:
                    for nm, r in rho.items():
                        if r(e) <= r(q): bad.add(nm)
    for nm in bad: rec('GateRank_' + nm)
for tag, L in out.items():
    json.dump(L, open(f'cex/{tag}.json', 'w')); print(tag, len(L), 'smallest |L|', min(len(m['sets']) for m in L))
