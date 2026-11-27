"""Free (samples only): for stored W0 models whose mu-fixed atom q is unclean, why: phi(r_q) != q, and/or corners with
phi(G) not >= q (what phi(G) is, and the corner colour's height)."""
import sys, collections
sys.path.insert(0, '.'); from corners import staircase
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import load_all, dedup
C = collections.Counter(); ex = []
for name, w in dedup(load_all()):
    if not (w.w0flat() and w.w0()): continue
    le, F, bot, h = w.le, w.F, w.bot, w.h
    for q in w.atoms:
        if not w.fixed(q): continue
        pr = F[bot][w.last_hi(q)]
        why = ['phi(r_q)=q' if pr == q else ('phi(r_q)=lam(q)' if pr == w.lam(q) else 'phi(r_q) other')]
        for x in w.Z:
            if not le[q][x]: continue
            G, kap, cs = staircase(w, q, x)
            for (l, k) in cs:
                g = G(l, k); pg = F[bot][g]
                if not le[q][pg]: why.append(('B corner', 'h(phiG)=%d' % h[pg], 'h(colour)=%d' % h[F[q][g]], 'x=q' if x == q else ('x M2')))
        if len(why) > 1 or why[0] != 'phi(r_q)=q':
            C[tuple(sorted(set(map(str, why))))] += 1; ex.append(name)
for k, v in C.most_common(): print(v, k)
print('examples', ex[:5])
