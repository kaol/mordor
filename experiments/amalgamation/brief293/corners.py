"""Staircase / corner-colour analysis (free; from the definitions, no SAT).
For an atom q of Z and a row x in Z with q <= x: G(j,k) = u_j(q) ^ u_k(x) (u = row descents from top).
H = {(j,k) : h(G(j,k)) >= 3} is a down-set of the grid; a corner is (l,k) in H with (l+1,k), (l,k+1) not in H.
Corner colour e = F(q, G(l,k)); case A iff phi(G(l,k)) >= q, case B otherwise.
Claims checked (CornerColour lemma, paper proof in brief.md):
  (C0) W0^2 at q gives F(q,G) not <= q at every corner (Tb at a two-row meet column);
  (C1) at a case-A corner, e is a height-2 cover of q and G(l+1,k+1) = G(l+1,k) = G(l,k+1) = e;
  (C2) consecutive corner colours lie below one common low element (G(l+1, K));
  (C3) first corner colour <= lambda(x), last corner colour <= lambda(q);
  (C4) all corners case A  ==>  lambda(x) = lambda(q), a height-2 cover of q.
World membership (W0, W0^2 = Meet2, NoFix) is recomputed from the definitions."""
import sys, json, itertools, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W, load_all, dedup
def w0sq(w):
    """W0^2 from the definitions: a(bot)=bot, ZT, n1, h(top)>=3, every row of Z lands, lambda(m) not <= m on M2,
    Tb at atom rows q only at high u ^ v (u in desc(q), v in desc(x), x in Z, q <= x), Tb at bot (= ZT)."""
    if not w.base(): return False
    for x in w.Z:
        if w.lam(x) is None: return False
        if x != w.bot and w.h[x] == 2 and w.le[w.lam(x)][x]: return False
    for q in w.atoms:
        for x in w.Z:
            if not w.le[q][x]: continue
            for u in w.desc(q):
                for v in w.desc(x):
                    g = w.L.meet[u][v]
                    if w.h[g] >= 3 and w.le[w.F[q][g]][q]: return False
    return True
def staircase(w, q, x):
    dq, dx = w.desc(q), w.desc(x); iq, ix = w.lidx(q), w.lidx(x)
    uq = lambda j: dq[min(j, len(dq) - 1)] if j < len(dq) else w.a(q)
    ux = lambda k: dx[min(k, len(dx) - 1)] if k < len(dx) else w.a(x)
    # descents are eventually constant at a(.); desc() lists distinct elements until repeat
    def U(row, j):
        v = w.top
        for _ in range(j): v = w.F[row][v]
        return v
    G = lambda j, k: w.L.meet[U(q, j)][U(x, k)]
    hi = lambda j, k: w.h[G(j, k)] >= 3
    kap = []
    for j in range(iq):
        k = 0
        while hi(j, k): k += 1
        kap.append(k)
    corners = [(l, kap[l] - 1) for l in range(iq) if (l == iq - 1 or kap[l + 1] < kap[l])]
    return G, kap, corners
def analyse(w, stats, tag):
    bot = w.bot; le, h, F = w.le, w.h, w.F
    for q in w.atoms:
        for x in w.Z:
            if not le[q][x]: continue
            G, kap, cs = staircase(w, q, x)
            info = []
            for (l, k) in cs:
                g = G(l, k); e = F[q][g]; A = le[q][F[bot][g]]
                c0 = not le[e][q]
                c1 = (not A) or (h[e] == 2 and le[q][e] and G(l + 1, k + 1) == e == G(l + 1, k) == G(l, k + 1))
                info.append((l, k, g, F[bot][g], e, A, c0, c1))
            c2 = all(le[info[i][4]][G(cs[i][0] + 1, kap[cs[i + 1][0]])] and le[info[i + 1][4]][G(cs[i][0] + 1, kap[cs[i + 1][0]])]
                     and h[G(cs[i][0] + 1, kap[cs[i + 1][0]])] <= 2 for i in range(len(cs) - 1))
            c3 = le[info[0][4]][w.lam(x)] and le[info[-1][4]][w.lam(q)]
            allA = all(t[5] for t in info)
            same = w.lam(x) == w.lam(q)
            c4 = (not allA) or (same and h[w.lam(q)] == 2 and le[q][w.lam(q)])
            stats[(tag, 'C0', all(t[6] for t in info), 'C1', all(t[7] for t in info), 'C2', c2, 'C3', c3, 'C4', c4)] += 1
            stats[(tag, 'pair', 'allA' if allA else 'someB', 'sameLanding' if same else 'diffLanding')] += 1
if __name__ == '__main__':
    print(__doc__)
    stats = collections.Counter(); seen = 0
    extra = sys.argv[1:]
    for name, w in dedup(load_all(extra)):
        if not w.base(): continue
        try:
            if any(w.lam(x) is None for x in w.Z): continue
        except Exception: continue
        if w0sq(w):
            tag = ('W0' if (w.w0flat() and w.w0()) else 'W0sq-not-W0') + ('-nofix' if w.nofix() else '')
            analyse(w, stats, tag); seen += 1
    print('models analysed', seen)
    for k, v in sorted(stats.items(), key=str): print(v, k)
