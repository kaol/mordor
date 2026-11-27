"""Save stored W0-flat & NoFix models refuting AscentRows (some minimal descent column y has b(y) in Z with every ascent
element of column y lying on a row of Z whose descent passes through y). Exact models, found by free replay (feat11.py)."""
import sys, json; sys.path.insert(0, '.'); from world import *
import bank
def ascent(w, y):
    v = w.bot; ch = [v]
    while w.F[v][y] != v: v = w.F[v][y]; ch.append(v)
    return ch
for name, w in [(n, w) for n, w in dedup(load_all()) if w.w0flat() and w.nofix()]:
    le = w.le; Zs = set(w.Z)
    Y = set(v for x in w.Z for v in w.desc(x)[:w.lidx(x)]); Ym = [y for y in Y if not any(z != y and le[z][y] for z in Y)]
    AR = lambda y: w.b(y) in Zs and all(e in set(x for x in w.Z if y in w.desc(x)) for e in ascent(w, y)[1:])
    if any(AR(y) for y in Ym): continue
    d, N = w.dN()
    rec = dict(sets=w.sets, F=w.F, source=name, refutes=['AscentRows (W0-flat, NoFix: some y in Ymin has b(y) in Z and its ascent runs along rows through y)'],
               world='W0-flat & NoFix', coords=dict(n=w.n, H=w.L.height, width=bank.width(w.L), N=N, branch='a' if w.h[d] == 2 else 'atom',
               Ymin=Ym, ascents={y: ascent(w, y) for y in Ym}, witness=w.witnesses(), noexit=w.noexit()))
    fn = 'cex/ascentrows_' + name.replace('/', '_').replace('#', '_') + '.json'; json.dump(rec, open(fn, 'w')); print(fn, rec['coords'])
