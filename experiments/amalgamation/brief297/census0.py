"""Free census (no SAT) over every stored model JSON under experiments/amalgamation (and extra paths).
Classifies each distinct model: W0+n1 or relaxed (base world + every Z-row lands); NoFix; colour set A =
{atoms c of Z : c = phi(w) some w}; bounded (some z in Z above all of A); N; branch."""
import sys, collections, json, pickle
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W, load_all, dedup
def colours(w):
    F = w.F; b = w.bot
    return sorted({F[b][y] for y in range(w.n) if F[b][y] in w.atoms})
def info(w):
    A = colours(w); bounded = any(all(w.le[c][z] for c in A) for z in w.Z)
    d, N = w.dN(); br = None if d is None else ('a' if w.h[d] == 2 else 'atom')
    return A, bounded, d, N, br
if __name__ == '__main__':
    models = dedup(load_all(sys.argv[1:]))
    C = collections.Counter(); keep = []
    for name, w in models:
        try:
            if not w.base(): C['not base'] += 1; continue
            lands = all(w.lam(x) is not None for x in w.Z)
            A, bounded, d, N, br = info(w)
            inW0 = w.w0flat() and w.w0()
            nf = w.nofix()
        except Exception as e:
            C['err'] += 1; continue
        world = 'W0' if inW0 else ('relaxed-lands' if lands else 'relaxed-noland')
        C[(world, 'nofix' if nf else 'fix', '|A|=%d' % len(A), 'bdd' if bounded else 'unb', 'N>=2' if (N or 0) >= 2 else 'N1')] += 1
        keep.append((name, world, nf, len(A), bounded, N, br))
    for k, v in sorted(C.items(), key=str): print(v, k)
    json.dump(keep, open('census0_index.json', 'w'))
