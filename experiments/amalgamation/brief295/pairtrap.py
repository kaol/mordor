"""Free analysis (no SAT; every quantity recomputed from the definitions via brief291/world.py).

PAIR STAIRCASE of two rows x, y of Z (both landing): v_j = (F x)^j T, w_k = (F y)^k T; for l < i(x):
  kappa(l) = least k with h(v_l ^ w_k) <= 2;  boundary point B_l = v_l ^ w_{kappa(l)-1} (high);
  value row q = x ^ y (must lie in Z), boundary value e_l = F(q, B_l)  (<= v_{l+1} ^ w_{kappa(l)}).

Statements checked (quantifier: for every stored model in the stated world, for every row x in Z):
  PairTrap   (paper, brief run 20 §4.1): if y = lambda(x) lies in Z and h(y) = 2, then some boundary point B_l of the
             (x, y)-staircase has F(q, B_l) an atom q' <= y with q' not <= x (and then q' = phi(B_l)).
             FAIL = a row x of Z with lambda(x) in M2 and no such boundary point (the paper proof would be wrong).
  AboveD     (paper corollary at N = 1): every row x of Z with x >= d exits, and its exit atom c(x) <= x.
             FAIL = a row above d that does not exit, or exits undominated.
  N1Cert     CertAtom at N = 1 (the theorem the two give): FAIL = N = 1 model with no mu-fixed atom.
Also, for models in relaxed worlds with N = 1 and NoFix (contradiction mode): which hypothesis of the A1 proof
is violated — Tb at q0 = m ^ d at a boundary point of the (d, m)-staircase (m = lambda(d)), lambda(m) <= m, lambda(d)
<= d, ZT, or none (then the proof is wrong)."""
import sys, json, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W, load_all, dedup

def U(w, x, j):
    v = w.top
    for _ in range(j): v = w.F[x][v]
    return v

def pair_boundary(w, x, y):
    """boundary points (l, kappa, B, e) of the (x, y)-staircase with value row x ^ y."""
    ix, iy = w.lidx(x), w.lidx(y)
    q = w.L.meet[x][y]; out = []
    for l in range(ix):
        vl = U(w, x, l); k = 0
        while w.h[w.L.meet[vl][U(w, y, k)]] >= 3: k += 1
        B = w.L.meet[vl][U(w, y, k - 1)]
        out.append((l, k, B, w.F[q][B]))
    return q, out

def pairtrap_ok(w, x):
    y = w.lam(x)
    if y is None or w.F[w.bot][y] != w.bot or w.h[y] != 2: return None          # hypothesis not met
    if w.lam(y) is None: return None
    q, bd = pair_boundary(w, x, y)
    if q not in w.Z: return 'q not in Z'
    wit = [(l, B, e) for (l, k, B, e) in bd if w.h[e] == 1 and w.le[e][y] and not w.le[e][x]]
    return bool(wit)

def a1_violation(w):
    """N = 1, NoFix model of a relaxed world: which step of the A1/N1 proof fails."""
    d, N = w.dN(); F, le, h = w.F, w.le, w.h
    if w.lam(d) is None: return 'd does not land'
    m = w.lam(d)
    if F[w.bot][m] != w.bot: return 'd exits (dominated exit; fixedBelow_of_exitDom hypotheses violated?)'
    if le[m][d]: return 'lambda(d) <= d (land_not_le at d violated)'
    if w.lam(m) is None: return 'm does not land'
    if w.lam(m) == m or le[w.lam(m)][m]: return 'lambda(m) <= m (land_not_le at m violated)'
    q, bd = pair_boundary(w, d, m)
    bad = [(l, B) for (l, k, B, e) in bd if le[e][q]]
    if bad: return 'Tb at q0=m^d fails at a (d,m) boundary point (h(q0)=%d, %d of %d points)' % (h[q], len(bad), len(bd))
    return 'NO VIOLATION FOUND (proof wrong?)'

if __name__ == '__main__':
    print(__doc__)
    C = collections.Counter(); seen = 0
    models = dedup(load_all(sys.argv[1:]))
    for name, w in models:
        try:
            if not w.base(): continue
            if any(w.lam(x) is None for x in w.Z): lands = False
            else: lands = True
        except Exception: continue
        inW0 = w.w0flat() and w.w0()
        d, N = w.dN()
        if d is None: continue
        br = 'a' if w.h[d] == 2 else 'atom'
        if inW0:
            seen += 1
            for x in w.Z:
                r = pairtrap_ok(w, x)
                if r is not None: C[('W0', 'PairTrap', 'holds' if r is True else 'FAIL:' + str(r))] += 1
                if r is False: print('PairTrap FAIL', name, 'x', x)
            if N == 1:
                for x in w.Z:
                    if le_ := w.le[d][x]:
                        ok = w.exits(x) and w.le[w.c(x)][x]
                        C[('W0', 'N1', br, 'AboveD', 'holds' if ok else 'FAIL')] += 1
                        if not ok: print('AboveD FAIL', name, 'x', x)
                C[('W0', 'N1', br, 'N1Cert', 'holds' if not w.nofix() else 'FAIL')] += 1
            else:
                C[('W0', 'N>=2', br, 'models')] += 1
        elif lands and N == 1 and w.nofix():
            v = a1_violation(w)
            C[('relaxed N1 NoFix', br, v)] += 1
            if 'NO VIOLATION' in v: print('A1 proof gap on', name)
    print('W0 models analysed', seen)
    for k, v in sorted(C.items(), key=str): print(v, k)
