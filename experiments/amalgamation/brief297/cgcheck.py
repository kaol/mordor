"""Free: for relaxed-world NoFix two-unbounded-colour models, does ColourGain (Lean colourGain, a W0 theorem) hold?
  CGreal   every row x of Z: some colour c <= lambda(x) with c not <= x
  CGvirt   every x not in Z whose minimal virtual row G_x lands at p: some colour c <= p with c not <= x
A model violating either is explained by TopRow' (its relaxation broke a Tb instance that TopRow' uses);
'informative' = satisfies both, so a proof must use something beyond single-row TopRow'."""
import sys, json, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W
import lib, footprint
print(__doc__)
C = collections.Counter(); keep = []
for fn in sys.argv[1:]:
    D = json.load(open(fn)); D = D if isinstance(D, list) else [D]
    for k, m in enumerate(D):
        w = W(m['sets'], m['F']); A = lib.colours(w); le = w.le; L = w.L; F = w.F; h = w.h
        if len(A) != 2 or lib.bounded(w, A) or not w.nofix(): C['out of class'] += 1; continue
        cgr = [x for x in w.Z if not any(le[c][w.lam(x)] and not le[c][x] for c in A)]
        cgv = []
        for x in range(w.n):
            if x in w.Z: continue
            zs = [z for z in w.Z if le[z][x]]
            v = w.top; seen = []
            while v not in seen and h[v] > 2:
                seen.append(v); u = w.bot
                for z in zs: u = L.join[u][F[z][v]]
                v = u
            if h[v] <= 2 and not any(le[c][v] and not le[c][x] for c in A): cgv.append(x)
        tag = ('CGreal ok' if not cgr else 'CGreal FAIL'), ('CGvirt ok' if not cgv else 'CGvirt FAIL')
        C[tag] += 1
        if not cgr and not cgv: keep.append(dict(sets=w.sets, F=w.F, src='%s#%d' % (fn, k)))
for k_, v in sorted(C.items(), key=str): print(v, k_)
if len(sys.argv) > 1: json.dump(keep, open(sys.argv[1].replace('.json', '') + '_informative.json', 'w'))
print('informative', len(keep))
