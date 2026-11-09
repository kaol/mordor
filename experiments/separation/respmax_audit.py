"""Stage potentials along shortest response-or-maximal runs (log §34.3z¹³⁷).

Separators: the response F(x, y) or a maximal separator (exist_cegar --respmax). For each instance, all shortest
terminating runs are enumerated; for each candidate stage potential (a function of the stage's bad set, ranks
h = L.rank) the audit records whether SOME shortest run has it strictly decreasing:
  maxgap = max h(y) + H − h(x);  maxdiff = max h(y) − h(x);  maxy = max h(y);  negminx = −min h(x);
  neg_minx_then_maxy = (−min h(x), max h(y)) lexicographically;  maxdiff_lexy = (max h(y) − h(x), max h(y)).
Also the shortest length minus H − 1.
  python3 respmax_audit.py random SEED SECONDS     random closure-system instances (4–5 points, |L| ≤ 18, H ≥ 3)
  python3 respmax_audit.py hard SHARD NSHARDS      exact H − 1 witnesses (CEGAR) on all 4-point closure systems,
                                                   plus 300 mutations each
"""
import sys, json, random, itertools, collections, time
import separator_stages as ss
import exist_cegar as ec
ec.RESPMAX = True
STATS = {
  'maxgap': lambda L, bad: max(L.rank[y] + L.height - L.rank[x] for x, y in bad),
  'maxdiff': lambda L, bad: max(L.rank[y] - L.rank[x] for x, y in bad),
  'maxy': lambda L, bad: max(L.rank[y] for x, y in bad),
  'negminx': lambda L, bad: -min(L.rank[x] for x, y in bad),
  'neg_minx_then_maxy': lambda L, bad: (-min(L.rank[x] for x, y in bad), max(L.rank[y] for x, y in bad)),
  'maxdiff_lexy': lambda L, bad: (max(L.rank[y] - L.rank[x] for x, y in bad), max(L.rank[y] for x, y in bad)),
}
def runs_all(L, F, D, k):
    """all terminating runs with < k stages (respmax), as lists of bad sets"""
    out = []
    def go(T, hist):
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad): out.append(hist); return
        if len(hist) >= k - 1: return
        for ch in itertools.product(*[ec.seps(L, F, x, y) for x, y in bad]):
            go(ss.mclose(L, set(T) | set(ch)), hist + [bad])
            if len(out) > 5000: return
    go(ss.mclose(L, {L.bot, L.top}), []); return out
def shortest(L, F, D):
    for k in range(1, 3 * L.height + 3):
        r = runs_all(L, F, D, k)
        if r: return [x for x in r if len(x) == min(map(len, r))]
def audit(L, F, D, tally, minbad):
    R = shortest(L, F, D)
    if R is None: return
    m = len(R[0]); tally['instances'] += 1; tally[('len-(H-1)', m - (L.height - 1))] += 1
    for nm, f in STATS.items():
        ok = any(all(f(L, a) > f(L, b) for a, b in zip(r, r[1:])) for r in R)
        tally[(nm, ok)] += 1
        if not ok and nm not in minbad: minbad[nm] = (L.n, L.height)
if __name__ == '__main__':
    if sys.argv[1] == 'random':
        rng = random.Random(int(sys.argv[2])); t0 = time.time(); tally = collections.Counter(); minbad = {}
        while time.time() - t0 < float(sys.argv[3]):
            L = ss.Lat(ss.closure_system(rng.choice([4, 5]), rng.choice([6, 8, 10]), rng))
            if L.height < 3 or L.n > 18: continue
            L2, g, gens = ss.random_instance(0, 0, rng, L)
            F = ss.make_F(L, g); D = ss.Dof(L, gens)
            audit(L, F, D, tally, minbad)
        print(dict(sorted(tally.items(), key=str)), minbad, flush=True)
    else:
        import nodesc_sweep as ns
        shard, nsh = int(sys.argv[2]), int(sys.argv[3]); tally = collections.Counter(); minbad = {}; wits = []
        for i, fam in enumerate(ns.moore_families(4)):
            if i % nsh != shard: continue
            L = ss.Lat(fam)
            if L.height < 3: continue
            r, it = ec.at_least(L, L.height - 1, 60)
            if not r: continue
            F, D = r; wits.append(dict(sets=L.S, F=F, D=D))
            audit(L, F, D, tally, minbad)
            # also mutations of the witness
            rng = random.Random(i)
            for _ in range(300):
                g = {(a, b): F[a][b] for a in range(L.n) for b in range(L.n)}
                for _ in range(rng.randint(1, 3)):
                    a, b = rng.randrange(L.n), rng.randrange(L.n); g[(a, b)] = rng.randrange(L.n) if rng.random() < .5 else 0
                F2 = ss.make_F(L, g); audit(L, F2, D, tally, minbad)
        print(dict(sorted(tally.items(), key=str)), minbad, flush=True)
        json.dump(wits, open(f'respmax_hard_witnesses_{shard}.json', 'w'))
