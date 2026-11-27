"""Free check (no SAT) of SelfShadow: some colour atom c (atom of Z with c = phi(w)) whose row lands has
c <= phi(r_c), r_c = the last high element of row c's descent.  (Consequence: lambda(c) >= c.)
Quantifier: per model, exists c.  FAIL = every colour row lands with phi(r_c) not >= c (or does not land).
Also SelfShadow2 (two colours only): the colour c with phi(r_c) >= c and the other colour c' has phi(r_c') >= c."""
import sys, json, collections, glob
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W
import lib
def ss(w):
    A = lib.colours(w); out = []
    for c in A:
        i = w.lidx(c)
        if i is None or i == 0: continue
        r = w.desc(c)[i - 1]
        if w.le[c][w.F[w.bot][r]]: out.append(c)
    return A, out
print(__doc__)
C = collections.Counter(); fails = []
def run(tag, models):
    for name, w in models:
        A, out = ss(w)
        unb = not lib.bounded(w, A)
        key = (tag, '|A|=%d' % len(A), 'unb' if unb else 'bdd', 'nofix' if w.nofix() else 'fix')
        C[key + ('SelfShadow holds' if out else 'SelfShadow FAIL',)] += 1
        if not out: fails.append((tag, name, w.n))
run('W0 stored', [(n, w) for n, w, i, l in lib.get() if i])
for fn in sys.argv[1:]:
    D = json.load(open(fn)); D = D if isinstance(D, list) else [D]
    run(fn.split('/')[-1].replace('.json', ''), [('%s#%d' % (fn, k), W(m['sets'], m['F'])) for k, m in enumerate(D)])
for k, v in sorted(C.items(), key=str): print(v, k)
print('fails', len(fails), fails[:12])
json.dump(fails, open('selfshadow_fails.json', 'w'))
