"""Free census (samples only) over every stored model in the repository that lies in W0 + n1 (checked from the
definitions by brief291/world.py): branch, N, the mu-fixed atoms, and whether the fixed atom is d."""
import sys, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import load_all, dedup
C = collections.Counter()
for name, w in dedup(load_all()):
    if not (w.w0flat() and w.w0()): continue
    d, N = w.dN(); br = 'a' if w.h[d] == 2 else 'atom'
    fx = [q for q in w.atoms if w.fixed(q)]
    C[(br, 'N1' if N == 1 else 'N>=2', 'fixed=d' if fx == [d] else ('fixed<=d' if all(w.le[q][d] for q in fx) else 'fixed elsewhere'), len(fx))] += 1
for k, v in sorted(C.items()): print(v, k)
