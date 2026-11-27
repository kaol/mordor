"""Free footprint analysis (no SAT) of relaxed-world NoFix models with two colours a, b unbounded in Z.
For every violated W0 instance it prints where it sits. Classes for a Tb violation at an atom q, column B (high,
F(q, B) <= q; by TbFibre F(q,B) = q = phi(B)):
  OWN       B on row q's descent
  DESC(x)   B on the descent of a row x of Z above q
  PAIR(x,y) B = v ^ w with v on desc(x), w on desc(y), x, y in Z (x, y >= q), B a boundary point of the
            (x, y)-staircase (v ^ succ_y(w) low or v_succ ^ w ... as in pairStair: B = v_l ^ w_(kappa(l)-1))
  STUCK     B <= Y where Y = gfp of G_P (P = a v b) ... reported as a flag
Also reported: Ta violations, land_not_le violations (lambda(m) <= m), and per model the colour data
(lambda(a), lambda(b), exits)."""
import sys, json, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W
import lib
def U(w, x, j):
    v = w.top
    for _ in range(j): v = w.F[x][v]
    return v
def boundary(w, x, y):
    ix = w.lidx(x); out = []
    if ix is None or w.lidx(y) is None: return out
    for l in range(ix):
        vl = U(w, x, l); k = 0
        while w.h[w.L.meet[vl][U(w, y, k)]] >= 3: k += 1
        out.append(w.L.meet[vl][U(w, y, k - 1)])
    return out
def analyse(w, verbose=True):
    A = lib.colours(w); h = w.h; le = w.le; F = w.F; L = w.L
    res = collections.Counter()
    if len(A) != 2 or lib.bounded(w, A) or not w.nofix(): return None
    a, b = A; P = L.join[a][b]
    ZP = [z for z in w.Z if le[z][P]]; Y = lib.gfp_row(w, ZP)
    desc = {x: set(w.desc(x)[:w.lidx(x) + 1]) for x in w.Z}
    viol = []
    for x in w.Z:
        for y in w.hi:
            if le[y][F[x][y]]: viol.append(('Ta', x, y))
            if le[F[x][y]][x]: viol.append(('Tb', x, y))
        if x != w.bot and le[w.lam(x)][x]: viol.append(('land_not_le', x, w.lam(x)))
    cls = []
    for kind, x, y in viol:
        if kind != 'Tb' or h[x] != 1: cls.append((kind, x, y, 'h(row)=%d' % h[x])); continue
        tags = []
        if y in desc[x]: tags.append('OWN')
        for z in w.Z:
            if z != x and le[x][z] and y in desc[z]: tags.append('DESC(%d)' % z)
        for z1 in w.Z:
            for z2 in w.Z:
                if z1 == z2 or not (le[x][z1] and le[x][z2]): continue
                if y in boundary(w, z1, z2): tags.append('BND(%d,%d)' % (z1, z2))
        tags.append('<=Y' if le[y][Y] else 'not<=Y')
        cls.append((kind, x, y, ' '.join(tags)))
    if verbose:
        d, N = w.dN()
        print('  model n=%d H=%d N=%d a=%d b=%d P=%d h(P)=%d Y=%d h(Y)=%d  lam(a)=%s %s  lam(b)=%s %s' % (
            w.n, h[w.top], N, a, b, P, h[P], Y, h[Y], w.lam(a), ('exit->%d' % w.c(a)) if w.exits(a) else 'inZ',
            w.lam(b), ('exit->%d' % w.c(b)) if w.exits(b) else 'inZ'))
        for c in cls: print('     ', c)
    return cls
if __name__ == '__main__':
    print(__doc__)
    C = collections.Counter()
    for fn in sys.argv[1:]:
        D = json.load(open(fn)); D = D if isinstance(D, list) else [D]
        for k, m in enumerate(D):
            w = W(m['sets'], m['F']); print('==', fn, k)
            cls = analyse(w)
            if cls is None: print('   (not in the NoFix two-unbounded-colour class)'); continue
            atomtb = [c for c in cls if c[0] == 'Tb' and 'h(row)' not in c[3]]
            C['models'] += 1
            C['some atom-Tb violation at a BND point'] += any('BND' in c[3] for c in atomtb)
            C['some atom-Tb violation'] += bool(atomtb)
            C['some height-2 Tb violation'] += any(c[0] == 'Tb' and c[3] == 'h(row)=2' for c in cls)
            C['some land_not_le violation'] += any(c[0] == 'land_not_le' for c in cls)
    print(dict(C))
