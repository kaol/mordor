"""Detail of the F# Tb violations of stored relaxed-world NoFix models: for each violating (q, w), the minimal row pairs
{x1, x2} (x_i in Z, x_i >= q) with succ_{x1}(sigma_{x1}(w)) ^ succ_{x2}(sigma_{x2}(w)) <= q, their sigma/succ, phi(w)."""
import sys, json, itertools, functools
sys.path.insert(0, '.'); from dmaxviol import sharp, W
def detail(d, tag=''):
    w = W(d['sets'], d['F']); G, sig = sharp(w); n, le, h, L, bot = w.n, w.le, w.h, w.L, w.bot
    lam = {x: w.lam(x) for x in w.Z if x != bot}
    print(f'{tag} n={n} H={h[w.top]} d,N={w.dN()} landings', {x: (lam[x], 'exit' if w.exits(x) else 'Z') for x in lam},
          'r', {x: w.last_hi(x) for x in lam})
    for q in w.atoms:
        rows = [x for x in w.Z if x != bot and le[q][x]]
        for y in w.hi:
            if not le[G[q][y]][q]: continue
            pairs = [(x1, x2) for x1, x2 in itertools.combinations_with_replacement(rows, 2)
                     if le[L.meet[w.F[x1][sig(x1, y)]][w.F[x2][sig(x2, y)]]][q]]
            desc = [(x1, sig(x1, y), w.F[x1][sig(x1, y)], 'r' if sig(x1, y) == w.last_hi(x1) else w.desc(x1).index(sig(x1, y)),
                     x2, sig(x2, y), w.F[x2][sig(x2, y)], 'r' if sig(x2, y) == w.last_hi(x2) else w.desc(x2).index(sig(x2, y))) for x1, x2 in pairs]
            print(f'   q={q} w={y} h={h[y]} phi(w)={w.F[bot][y]} pairs (x1,sig,succ,idx,x2,sig,succ,idx):', desc)
if __name__ == '__main__':
    for f in sys.argv[1:]:
        D = json.load(open(f)); D = D if isinstance(D, list) else [D]
        for k, d in enumerate(D): detail(d, f.split('/')[-1] + f'#{k}')
