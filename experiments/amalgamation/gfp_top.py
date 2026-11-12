"""The orbit criterion for interval cells (log §34.3z¹⁵³).

For m < ⊤ let y*(m) be the limit of ⊤, m ⊔ F(m, ⊤), m ⊔ F(m, m ⊔ F(m, ⊤)), … (the greatest fixed point of
y ↦ m ⊔ F(m, y) on [m, ⊤]). GFP(m): y*(m) = m (then the last orbit value above m is a lower cell) or
F(m, y*(m)) = y*(m) (an upper cell). GFP(m) ⇒ IC(m). On random tight stages, counts:
  IC at some top, GFP at some top, IC but no GFP at any top; and per top element IC(m) vs GFP(m).
  python3 gfp_top.py SEED SECONDS
"""
import sys, random, time, collections, json
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages

def ystar(L, F, m):
    y = L.top
    while True:
        y2 = L.join[m][F[m][y]]
        if y2 == y: return y
        y = y2

def gfp_ok(L, F, m):
    y = ystar(L, F, m); return y == m or F[m][y] == y

def ic(L, F, m):
    return any(y != m and L.le[m][y] and (L.le[F[m][y]][m] or L.le[y][F[m][y]]) for y in range(L.n))

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter(); ex = None
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 2 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F); n = L.n
        for k in range(st[L.top] - 1):
            R = [z for z in range(n) if st[z] <= k]
            if max(L.rank[z] for z in R) != k: continue
            Tk = [z for z in R if L.rank[z] == k]
            I = [ic(L, F, m) for m in Tk]; G = [gfp_ok(L, F, m) for m in Tk]
            T['tight stages'] += 1; T[('IC at some top', any(I))] += 1; T[('GFP at some top', any(G))] += 1
            if any(I) and not any(G):
                T['IC but no GFP'] += 1
                if ex is None or n < ex['n']: ex = dict(n=n, sets=L.S, F=F, k=k)
            for i, gg in zip(I, G): T[('per top: (IC, GFP)', i, gg)] += 1
    print(dict(sorted(T.items(), key=str)), 'smallest IC-but-no-GFP:', ex and ex['n'], flush=True)
    if ex: json.dump(ex, open(f'gfp_top_fail_s{sys.argv[1]}.json', 'w'))
