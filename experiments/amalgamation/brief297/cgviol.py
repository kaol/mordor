"""Free: in CGWnoCG models (ColourGain dropped), which real rows violate ColourGain, by type."""
import sys, json, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W
import lib
C = collections.Counter()
for fn in sys.argv[1:]:
    for k, m in enumerate(json.load(open(fn))):
        w = W(m['sets'], m['F']); A = lib.colours(w); le = w.le; h = w.h
        a, b = A
        bad = [x for x in w.Z if x != w.bot and not any(le[c][w.lam(x)] and not le[c][x] for c in A)]
        typ = lambda x: ('colour' if x in A else 'atom0') if h[x] == 1 else ('h2:' + ''.join('a' if le[a][x] else '' for _ in [0]) + ('b' if le[b][x] else '') or 'h2:0')
        kinds = tuple(sorted(set(typ(x) + ('/exit' if w.exits(x) else '/inZ') for x in bad)))
        C[kinds] += 1
        if k < 3: print(fn, k, 'n', w.n, 'A', A, 'bad rows', [(x, h[x], w.lam(x), 'exit->%s' % w.c(x) if w.exits(x) else 'inZ') for x in bad])
for k_, v in sorted(C.items(), key=str): print(v, k_)
