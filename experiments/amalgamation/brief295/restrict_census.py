"""Free check (no SAT): the restriction transfer for N >= 2.  For a stored W0 model with N >= 2 and an element s of the
bot-descent t_1 .. t_{N-1} that is high, put L' = down(s) (a sublattice, top s) and F'(x, y) = F(x, y) ^ s on L'.
Then phi' = phi on L', Z' = Z ^ down(s), and the bot-descent of F' is s, phi(s), ... (so N' = N - j for s = t_j).
Reported per model and s: whether F' lies in W0 (definitions recomputed on L'), and whether CertAtom(F') and CertAtom(F)
share a fixed atom (TRANSFER: every mu'-fixed atom is mu-fixed).  Samples only."""
import sys, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W, load_all, dedup

def restrict(w, s):
    keep = [v for v in range(w.n) if w.le[v][s]]
    idx = {v: i for i, v in enumerate(keep)}
    sets = [w.sets[v] for v in keep]
    F = [[idx[w.L.meet[w.F[x][y]][s]] for y in keep] for x in keep]
    return W(sets, F), keep

C = collections.Counter()
for name, w in dedup(load_all(sys.argv[1:])):
    try:
        if not (w.base() and w.w0flat() and w.w0()): continue
    except Exception: continue
    d, N = w.dN()
    if N < 2: continue
    tb = w.tdesc()
    fixF = {q for q in w.atoms if w.fixed(q)}
    for j in range(1, N):
        s = tb[j]
        if w.h[s] < 3: C[('N%d' % N, 's=t%d' % j, 'low, skipped')] += 1; continue
        try:
            w2, keep = restrict(w, s)
        except Exception as e:
            C[('N%d' % N, 's=t%d' % j, 'restriction not a lattice/loader error')] += 1; continue
        if not w2.mono: C[('N%d' % N, 's=t%d' % j, 'not monotone')] += 1; continue
        inW0 = w2.base() and w2.w0flat() and w2.w0()
        if not inW0:
            why = 'base fails' if not w2.base() else ('Ta fails' if not all(w2.Ta(x) for x in w2.Z) else 'Tb fails')
            C[('N%d' % N, 's=t%d' % j, "F' not in W0", why)] += 1; continue
        fix2 = {keep[q] for q in w2.atoms if w2.fixed(q)}
        tr = 'TRANSFER holds' if fix2 and fix2 <= fixF else ('no fixed atom in F\'' if not fix2 else 'TRANSFER FAILS')
        C[('N%d' % N, 's=t%d' % j, "F' in W0", tr)] += 1
print(__doc__)
for k, v in sorted(C.items(), key=str): print(v, k)
