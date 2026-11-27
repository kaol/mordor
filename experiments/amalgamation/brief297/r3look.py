"""Free: print the colour-row structure of R3-type models (rows bot, a, b): descents, landings, phi on them, and
which colour rows satisfy ColourGain."""
import sys, json
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W
import lib
D = json.load(open(sys.argv[1])); D.sort(key=lambda m: len(m['sets']))
for m in D[:int(sys.argv[2])]:
    w = W(m['sets'], m['F']); A = lib.colours(w); a, b = A; L = w.L; le = w.le; F = w.F; h = w.h
    P = L.join[a][b]; d, N = w.dN()
    print('== n', w.n, 'sets', w.sets, 'H', h[w.top], 'A', A, 'P', P, 'h(P)', h[P], 'Z', w.Z, 'tdesc', w.tdesc(), 'N', N)
    print('   phi:', {y: F[w.bot][y] for y in range(w.n) if F[w.bot][y] != w.bot})
    for c in A:
        ds = w.desc(c); i = w.lidx(c)
        print('   row', c, 'desc', ds[:i+1], 'lam', ds[i], 'inZ' if ds[i] in w.Z else 'exit->%d' % F[w.bot][ds[i]],
              'phi on desc', [F[w.bot][y] for y in ds[:i]], 'CG', any(le[c2][ds[i]] and not le[c2][c] for c2 in A))
