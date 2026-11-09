"""Remaining distance from reachable states (log §34.3z¹³⁹).

dist(T) = fewest further RM stages from T to a goal state (Lean `ShortestRun.dist` for this separator class).
Reports, per height, the maximum of dist over all RM-reachable states, against H − 1 (the exact maximum of dist
at the initial state, §34.3z¹³⁶–¹³⁷), and the maximum of dist(T) + (stage index of T) along shortest paths.
  python3 remaining_dist.py random SEED SECONDS | hard FILE... | cycle KMAX
"""
import sys, json, random, itertools, time, collections
import separator_stages as ss
import exist_cegar as ec
from local_lex import goal
ec.RESPMAX = True

def graph(L, F, D, cap=4000):
    start = ss.mclose(L, {L.bot, L.top}); succ = {}; depth = {start: 0}; q = collections.deque([start])
    while q and len(succ) < cap:
        T = q.popleft(); bad = ss.bad_pairs(L, F, D, T)
        if goal(L, F, bad): succ[T] = None; continue
        succ[T] = set()
        for ch in itertools.product(*[ec.seps(L, F, x, y) for x, y in bad]):
            U = ss.mclose(L, set(T) | set(ch)); succ[T].add(U)
            if U not in depth: depth[U] = depth[T] + 1; q.append(U)
    if q: return None
    dist = {}
    def dd(T):
        if T in dist: return dist[T]
        dist[T] = 10 ** 9
        r = 0 if succ[T] is None else 1 + min(dd(U) for U in succ[T])
        dist[T] = r; return r
    for T in succ: dd(T)
    return start, succ, depth, dist

def audit(L, F, D, tally, ex):
    g = graph(L, F, D)
    if g is None: tally['capped'] += 1; return
    start, succ, depth, dist = g; H = L.height
    m = max(dist.values()); tally[(H, 'max dist - (H-1)', m - (H - 1))] += 1
    if m > H - 1 and (H not in ex or L.n < ex[H]['n']):
        T = max(dist, key=dist.get); ex[H] = dict(n=L.n, sets=L.S, F=F, D=D, T=sorted(T), dist=m)

if __name__ == '__main__':
    tally = collections.Counter(); ex = {}
    if sys.argv[1] == 'cycle':
        from cycle_family import family
        for k in range(4, int(sys.argv[2]) + 1):
            L, F, D = family(k); start, succ, depth, dist = graph(L, F, D)
            print(f"cycle family k = {k}: dist(start) = {dist[start]}, max dist over RM-reachable states = "
                  f"{max(dist.values())}, height {L.height}", flush=True)
        sys.exit()
    if sys.argv[1] == 'random':
        rng = random.Random(int(sys.argv[2])); t0 = time.time()
        while time.time() - t0 < float(sys.argv[3]):
            L = ss.Lat(ss.closure_system(rng.choice([4, 5]), rng.choice([6, 8, 10]), rng))
            if L.height < 3 or L.n > 18: continue
            _, g, gens = ss.random_instance(0, 0, rng, L)
            audit(L, ss.make_F(L, g), ss.Dof(L, gens), tally, ex)
    else:
        for f in sys.argv[2:]:
            for w in json.load(open(f)): audit(ss.Lat(w['sets']), w['F'], w['D'], tally, ex)
    print(dict(sorted(tally.items(), key=str)), flush=True)
    for H, e in ex.items():
        print(f"height {H}: a reachable state with dist {e['dist']} > H − 1 at |L| = {e['n']}", flush=True)
        json.dump(e, open(f"remaining_dist_fail_h{H}_{sys.argv[2] if sys.argv[1] == 'random' else 'hard'}.json", 'w'))
