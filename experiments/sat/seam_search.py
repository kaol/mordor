"""Round 23: polar realizable pairs on D_k / E_k commuting everywhere except on the last column (the seam)."""
import sys, time
pass
from lat import *
def seam_search(L, relaxed, extra_free=()):
    """polar realizable pair; a.b = b.a required except at elements in `relaxed`."""
    def extra(e):
        C, Dd = add_composites(e)
        for x in range(L.n):
            if x in relaxed: continue
            for w in range(L.n): e.cl += [[-C[x][w], Dd[x][w]], [C[x][w], -Dd[x][w]]]
    e = Enc(L, polar=True, commute=False, extra=extra); s = e.solver()
    if s.solve():
        F, a, b = e.decode(s.get_model()); a2, b2, m, nn, c = semantic(L, F)
        bad = [x for x in range(L.n) if a[b[x]] != b[a[x]]]
        return a, b, bad
    return None
for k in range(2, 8):
    L = D_cols(k); last = {2 + 2*(k-1), 3 + 2*(k-1)}
    r1 = seam_search(L, last)
    L2 = E(k); last2 = {2 + 3*(k-1), 3 + 3*(k-1), 4 + 3*(k-1)}
    r2 = seam_search(L2, last2)
    print(f"k={k}:  D_k seam-relaxed: {'SAT defects at '+str(r1[2]) if r1 else 'UNSAT'}   E_k seam-relaxed: {'SAT defects at '+str(r2[2]) if r2 else 'UNSAT'}", flush=True)
