"""Free: stored relaxed-world models (base world, every Z-row lands, not W0) with NoFix and colours unbounded in Z.
Prints which W0 conditions fail: Ta/Tb violations (row, column) with locations."""
import lib
D = [(n, w) for n, w, i, l in lib.get() if (not i) and l]
for name, w in D:
    if not w.nofix(): continue
    A = lib.colours(w)
    if lib.bounded(w, A) or len(A) < 2: continue
    d, N = w.dN(); h = w.h; le = w.le; F = w.F
    print('==', name, 'n', w.n, 'H', h[w.top], 'N', N, 'A', A, 'Z', w.Z)
    for x in w.Z:
        ta = [y for y in w.hi if le[y][F[x][y]]]; tb = [(y, F[x][y]) for y in w.hi if le[F[x][y]][x]]
        print('   row', x, 'h', h[x], 'lam', w.lam(x), 'exit->%s' % w.c(x) if w.exits(x) else 'inZ', 'desc', w.desc(x)[:w.lidx(x)+1], 'Ta-viol', ta, 'Tb-viol', tb)
