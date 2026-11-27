"""Free census (no SAT) of the 81 stored W0 models with exactly two colour atoms a, b unbounded in Z.
Reports where the (unique) fixed atom q* lands relative to P = a v b, and the paper facts of the two-colour trap:
 T1  phi(r_c) >= other colour, for the NON-fixed colour c (r_c = last high element of row c's descent)
 T2  lambda(q*) = P and phi(P) = q*
 T3  for the non-fixed colour c: lambda(c) >= other colour (ColourGain at c, a W0 fact only under NoFix; here informative)"""
import lib, collections
print(__doc__)
D = [(n, w) for n, w, i, l in lib.get() if i]
C = collections.Counter()
for name, w in D:
    A = lib.colours(w)
    if len(A) != 2 or lib.bounded(w, A): continue
    a, b = A; L = w.L; le = w.le; F = w.F; h = w.h; P = L.join[a][b]
    fx = [q for q in w.atoms if w.fixed(q)]
    C['models'] += 1
    C[('h(P)', h[P])] += 1
    q = fx[0]; c = b if q == a else a
    C[('fixed in A', q in A)] += 1
    C[('lam(q*) = P', w.lam(q) == P)] += 1
    rc = w.desc(c)[w.lidx(c) - 1]
    C[('T1 phi(r_c) >= q*', le[q][F[w.bot][rc]])] += 1
    C[('T3 lam(c) >= q*', le[q][w.lam(c)])] += 1
    C[('lam(c) in Z', w.lam(c) in w.Z)] += 1
for k, v in sorted(C.items(), key=str): print(v, k)
