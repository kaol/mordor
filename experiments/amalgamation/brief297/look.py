import sys, lib
D = [(n, w) for n, w, i, l in lib.get() if i]
sel = []
for name, w in D:
    A = lib.colours(w)
    if len(A) == 2 and not lib.bounded(w, A): sel.append((w.n, name, w))
sel.sort(key=lambda t: t[0])
for n, name, w in sel[:int(sys.argv[1])]:
    A = lib.colours(w); a, b = A; h = w.h; le = w.le; F = w.F; L = w.L
    d, N = w.dN()
    fx = [q for q in w.atoms if w.fixed(q)]
    print('=== ', name, 'n', n, 'H', h[w.top], 'N', N, 'd', d, 'h(d)', h[d], 'A', A, 'fixed', fx, 'a|b', L.join[a][b], 'h', h[L.join[a][b]])
    print('  Z atoms', w.atoms, 'M2', w.M2, ' M2 above:', {m: [c for c in A if le[c][m]] for m in w.M2})
    for x in w.Z:
        print('   row', x, 'h', h[x], 'cols', [c for c in A if le[c][x]], 'desc', w.desc(x)[:w.lidx(x)+1], 'lam', w.lam(x), 'inZ' if w.lam(x) in w.Z else 'exit->%s' % w.c(x), 'mu', (w.lam(x) if w.lam(x) in w.Z else w.c(x)))
    print('  phi of high:', sorted({F[w.bot][y] for y in w.hi}), ' tdesc', w.tdesc())
