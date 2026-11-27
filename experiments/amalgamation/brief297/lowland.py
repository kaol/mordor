"""Free census (no SAT) over every stored W0+n1 model: rows outside Z are free (w0_of_T), so for x not in Z any
monotone g >= G_x := join of F(z, .) over z in Z, z <= x, is a legitimate row of x. A legit row of x lands at p iff
there is a chain T = y_0 > y_1 > ... > y_i = p with y_j high (j < i), p low, G_x(y_j) <= y_(j+1)
(construction g(y) = G_x(y) v y_(j0+1), j0 = least j with y_j <= y). TopRow' (certAtom_of_topRow') then gives
CertAtom whenever every colour atom below p lies below x.
Statements (quantifier: per model, exists x not in Z):
  LowLand    some x not in Z has a legit row landing at some p <= x            (=> CertAtom: p <= x)
  TRexists   some x not in Z has a legit row landing at p with A cap down(p) <= down(x)   (=> CertAtom)
  SelfLand   some T not in Z with gfp(y -> G_T(y) v T) = T and the G_T-descent from T reaching a low element
             (the special chain: psi-descent from top to T, then G_T from T) (=> LowLand)
FAIL = no such x in that model (the statement is then refuted as a route on a model that has a fixed atom)."""
import lib, collections, sys, json
print(__doc__)
D = [(n, w) for n, w, i, l in lib.get() if i]
C = collections.Counter(); FL = collections.defaultdict(list)
for name, w in D:
    A = lib.colours(w); unb = not lib.bounded(w, A); L = w.L; F = w.F; le = w.le; h = w.h; n = w.n
    d, N = w.dN()
    hi = [y for y in range(n) if h[y] >= 3]; low = [y for y in range(n) if h[y] <= 2]
    def Gx(x):
        zs = [z for z in w.Z if le[z][x]]
        def g(y):
            v = w.bot
            for z in zs: v = L.join[v][F[z][y]]
            return v
        return [g(y) for y in range(n)]
    def search(x, okp):
        G = Gx(x); seen = set(); st = [w.top]
        while st:
            y = st.pop()
            if y in seen: continue
            seen.add(y)
            if any(le[G[y]][p] and le[p][y] and p != y and okp(p) for p in low): return True
            for y2 in hi:
                if y2 != y and le[y2][y] and le[G[y]][y2] and y2 not in seen: st.append(y2)
        return False
    nonZ = [x for x in range(n) if x not in w.Z]
    LowLand = [x for x in nonZ if search(x, lambda p, x=x: le[p][x])]
    TR = [x for x in nonZ if search(x, lambda p, x=x: all(le[c][x] for c in A if le[c][p]))]
    SL = []
    for T in nonZ:
        G = Gx(T); y = w.top
        while True:
            y2 = L.join[G[y]][T]
            if y2 == y: break
            y = y2
        if y != T: continue
        v = T; s = []
        while v not in s: s.append(v); v = G[v]
        if any(h[u] <= 2 for u in s): SL.append(T)
    tag = ('unb' if unb else 'bdd', '|A|=%d' % len(A), 'N1' if N == 1 else 'N>=2')
    for nm, lst in (('LowLand', LowLand), ('TRexists', TR), ('SelfLand', SL)):
        C[tag + (nm, 'holds' if lst else 'FAIL')] += 1
        if not lst: FL[nm].append(name)
    if unb and len(A) == 2:
        C[('unb |A|=2', 'LowLand x high' if any(h[x] >= 3 for x in LowLand) else 'LowLand only low x' if LowLand else '-')] += 1
for k, v in sorted(C.items(), key=str): print(v, k)
for k in FL: print('FAIL', k, len(FL[k]), FL[k][:8])
json.dump(FL, open('lowland_fails.json', 'w'))
