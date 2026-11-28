"""Run-28 briefer: lattice corpora.  Delegates to tight_probe.lattices, plus
  planted H M SEED CNT k : a tall lattice of height exactly H with a PLANTED element P of height 2 covering exactly k
      atoms (k >= 3 gives room in |C(m)|, the number of colours below one pair-join).  Construction on K' = H + k - 2
      points: a maximal chain that jumps from one point of P to all of P (so every chain meets P in {}, a singleton or P),
      the k singletons of P, and M random sets each repaired so that it meets P in {}, one point, or all of P; closed
      under intersections.  Every set meets P in {}, a singleton or P, so P covers exactly the k singletons and the
      height is exactly H.  Each lattice is checked (assertion)."""
import random, itertools, sys
sys.path.insert(0,'/home/user/mordor/experiments/amalgamation'); sys.path.insert(0,'/home/user/mordor/experiments/separation')
import tight_probe as tp
ss = tp.ss
def planted(H, M, sd, cnt, k):
    rng = random.Random(sd); K = H + k - 2
    for _ in range(cnt):
        pts = list(range(K)); rng.shuffle(pts); P = pts[:k]; Pm = sum(1 << i for i in P)
        fam = {0, (1 << K) - 1, Pm} | {1 << i for i in P}
        acc = 1 << P[0]; fam.add(acc); acc |= Pm; fam.add(acc)
        rest = pts[k:]; rng.shuffle(rest)
        for i in rest: acc |= 1 << i; fam.add(acc)
        for _ in range(M):
            r = rng.getrandbits(K); inter = r & Pm; c = bin(inter).count('1')
            if 2 <= c < k:
                if rng.random() < 0.5: r |= Pm
                else: r = (r & ~Pm) | (1 << rng.choice([i for i in P if inter >> i & 1]))
            fam.add(r)
        ch = True
        while ch:
            ch = False
            for a, b in itertools.combinations(list(fam), 2):
                if a & b not in fam: fam.add(a & b); ch = True
        L = ss.Lat(sorted(fam, key=lambda x: (bin(x).count('1'), x)))
        ip = L.idx[Pm]
        assert L.rank[ip] == 2 and L.height == H and sum(1 for j in range(L.n) if L.le[j][ip] and L.rank[j] == 1) == k
        yield L
def lattices(args):
    if args[0] == 'planted':
        H, M, sd, cnt, k = (int(x) for x in args[1:6]); yield from planted(H, M, sd, cnt, k)
    else: yield from tp.lattices(args)
if __name__ == '__main__':
    for L in lattices(sys.argv[1:]):
        w = max(sum(1 for j in range(L.n) if L.rank[j] == r) for r in range(L.height + 1))
        m3 = max((sum(1 for a in range(L.n) if L.rank[a] == 1 and L.le[a][z]) for z in range(L.n) if L.rank[z] == 2), default=0)
        print(f'n={L.n} H={L.height} max-rank-level={w} max atoms under a height-2 element={m3}')
