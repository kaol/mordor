import sys, lib, collections
D = [(n, w) for n, w, i, l in lib.get() if i]
C = collections.Counter(); sel = []
for name, w in D:
    A = lib.colours(w)
    if lib.bounded(w, A): continue
    L = w.L; X = A[0]
    for c in A: X = L.join[X][c]
    ZX = [z for z in w.Z if w.le[z][X]]
    Y = lib.gfp_row(w, ZX)
    stuck = w.h[Y] > 2
    YA = lib.gfp_row(w, [w.bot] + A)
    C[(len(A), 'X stuck' if stuck else 'X lands', 'A-row stuck' if w.h[YA] > 2 else 'A-row lands', 'h(X)=%d' % w.h[X])] += 1
    if stuck and len(A) == 2: sel.append((w.n, name, w, X, Y))
for k, v in sorted(C.items(), key=str): print(v, k)
sel.sort(key=lambda t: t[0])
for n, name, w, X, Y in sel[:int(sys.argv[1])]:
    A = lib.colours(w); a, b = A; h = w.h; le = w.le; F = w.F; L = w.L
    d, N = w.dN(); fx = [q for q in w.atoms if w.fixed(q)]
    print('=== ', name, 'n', n, 'H', h[w.top], 'N', N, 'd', d, 'h(d)', h[d], 'A', A, 'fixed', fx, 'X', X, 'h(X)', h[X], 'Y', Y, 'h(Y)', h[Y])
    print('  sets', w.sets)
    print('  Z atoms', w.atoms, 'M2', w.M2, ' M2 above:', {m: [c for c in A if le[c][m]] for m in w.M2})
    for x in w.Z:
        print('   row', x, 'h', h[x], 'cols', [c for c in A if le[c][x]], 'desc', w.desc(x)[:w.lidx(x)+1], 'lam', w.lam(x), 'inZ' if w.lam(x) in w.Z else 'exit->%s' % w.c(x), 'F(x,Y)', F[x][Y], 'descY', lib.descfrom(w, x, Y)[:4])
    print('  phi of high:', sorted({F[w.bot][y] for y in w.hi}), ' tdesc', w.tdesc(), 'phi(Y)', F[w.bot][Y])
