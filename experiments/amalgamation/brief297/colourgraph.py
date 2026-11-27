"""Free: R3 NoFix models with >= 3 colours (run 5): colour count and the colour map c -> colours below lambda(c) other
than c; whether it has a 2-cycle (a swap), and whether some colour row lands above its own colour."""
import sys, json, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W
import lib
C = collections.Counter(); small = None
for fn in sys.argv[1:]:
    for k, m in enumerate(json.load(open(fn))):
        w = W(m['sets'], m['F']); A = lib.colours(w); le = w.le
        g = {c: [c2 for c2 in A if c2 != c and le[c2][w.lam(c)]] for c in A}
        swap = any(c2 in g[c] and c in g[c2] for c in A for c2 in A if c != c2)
        selfcov = any(le[c][w.lam(c)] for c in A)
        d, N = w.dN()
        C[('|A|', len(A))] += 1; C[('has 2-cycle', swap)] += 1; C[('some c <= lam(c)', selfcov)] += 1
        C[('branch', 'a' if w.h[d] == 2 else 'atom', 'N', N)] += 1
        if small is None or w.n < small[0]: small = (w.n, fn, k, A, g, w.h[w.top])
for k_, v in sorted(C.items(), key=str): print(v, k_)
print('smallest', small)
