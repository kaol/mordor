import sys; sys.path.insert(0, '.'); from world import *
ms = [(n, w) for n, w in dedup(load_all()) if w.w0flat() and w.nofix()]
print('W0flat & NoFix stored models (samples only):', len(ms))
from collections import Counter; C = Counter()
for name, w in ms:
    le, F, h = w.le, w.F, w.h; L = w.L
    ne = w.noexit(); tag = 'noexit' if ne else 'exit'
    W = w.witnesses()
    s2 = all(w.lam(m) == m for q in w.atoms for m in w.M2 if le[q][m] and w.lam(q) == m)
    upland = any(w.lam(q) in w.M2 and le[q][w.lam(q)] for q in w.atoms)
    # join mechanism at witness
    def joinlb(m):
        r = w.last_hi(m); v = w.bot
        for x in w.Z:
            if le[x][m] and x != m: v = L.join[v][F[x][r]]
        return v
    joinw = any(le[m][joinlb(m)] for m in W)
    stall = any(F[m][m] == m for m in W)
    # witness above two atoms landing at it
    two = any(sum(1 for q in w.atoms if le[q][m] and w.lam(q) == m) >= 2 for m in W)
    one = any(sum(1 for q in w.atoms if le[q][m] and w.lam(q) == m) >= 1 for m in W)
    # every atom below a witness lands at it?
    allbelow = any(all(w.lam(q) == m for q in w.atoms if le[q][m]) for m in W)
    # some witness is maximal in Z
    maxZ = any(all(not (le[m][y] and m != y) for y in w.Z) for m in W)
    for k, v in dict(S2=s2, upland=upland, join_lb=joinw, stall=stall, two_atoms_land=two, one_atom_lands=one,
                     all_atoms_below_land=allbelow, w_maxZ=maxZ, nW1=len(W) == 1).items():
        C[(tag, k, v)] += 1
for k in sorted(C): print(k, C[k])
