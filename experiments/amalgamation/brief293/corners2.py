"""Corner colours, refined (free; from the definitions). For every W0^2 stored model, atom q, row x >= q in Z:
  C4'  if every corner colour e = F(q, G) has height 2, then lambda(x) = lambda(q) (= that colour);
  bad corner = corner whose colour is an atom q' (then q' != q and phi(G) = q').  Statistics on bad corners:
  is q' <= x?  is q v q' in Z?  is q' the mu-fixed atom?  is the bad corner's G in the q'-fibre (phi(G) = q')?"""
import sys, collections
sys.path.insert(0, '.'); from corners import w0sq, staircase
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W, load_all, dedup
S = collections.Counter()
for name, w in dedup(load_all()):
    if not w.base() or any(w.lam(x) is None for x in w.Z) or not w0sq(w): continue
    tag = 'W0' if (w.w0flat() and w.w0()) else 'W0sq\\W0'
    le, h, F, bot, L = w.le, w.h, w.F, w.bot, w.L
    fixed = [q for q in w.atoms if w.fixed(q)]
    for q in w.atoms:
        for x in w.Z:
            if not le[q][x]: continue
            G, kap, cs = staircase(w, q, x)
            cols = [F[q][G(l, k)] for (l, k) in cs]
            all2 = all(h[e] == 2 for e in cols)
            same = w.lam(x) == w.lam(q)
            S[(tag, "C4'", (not all2) or same)] += 1
            if not all2:
                for (l, k), e in zip(cs, cols):
                    if h[e] != 1: continue
                    g = G(l, k); j = L.join[q][e]
                    S[(tag, 'bad', 'phiG=e' if F[bot][g] == e else 'phiG!=e', "q'<=x" if le[e][x] else "q'!<=x",
                       'qvq\' in Z' if F[bot][j] == bot else 'qvq\' not in Z', 'q\' fixed' if e in fixed else ('q fixed' if q in fixed else 'neither fixed'))] += 1
for k, v in sorted(S.items(), key=str): print(v, k)
