"""The finite state graph of the separator process: completion distance, optimal gap-successors, exchange depth
(log §34.3z¹³⁰; brief Report A).

States: meet-closed T reachable from T₀ = {⊥, ⊤} by legal steps (all choices of one maximal separator per bad pair).
Goal(T): no bad pair or a stuck bad pair (Lean `ShortestRun.Goal`). d(T): completion distance (`ShortestRun.dist`).
M(T): maximum gap h(y) + H − h(x) over bad pairs. A successor T' of a non-goal T is *good* if d(T') = d(T) − 1 and
(Goal(T') or M(T') < M(T)).
(a) every reachable non-goal state has a good successor;
(b) the same for states on shortest paths from T₀ (dist₀(T) + d(T) = d(T₀));
(c) desc(T): a descending optimal continuation exists from T. For every shortest run from T₀ whose first
    non-descending transition is at stage k, the latest stage j ≤ k with desc(T_j) gives the exchange depth k − j
    (0: the failing stage itself has a good alternative; > 0: an earlier choice must be revised).
  python3 state_graph_audit.py records FILE | hunt SEED SECONDS FILES...
"""
import sys, json, random, itertools, time, collections
import separator_stages as ss

def graph(L, F, D, limit=30000):
    H = L.height; rk = L.rank; phi = lambda p: rk[p[1]] + H - rk[p[0]]
    T0 = ss.mclose(L, {L.bot, L.top}); succ = {}; goal = {}; M = {}; stack = [T0]; work = 0
    while stack:
        T = stack.pop()
        if T in succ: continue
        bad = ss.bad_pairs(L, F, D, T)
        goal[T] = not bad or any(L.le[y][F[x][y]] for x, y in bad)
        M[T] = max(phi(p) for p in bad) if bad else None
        succ[T] = []
        if goal[T]: continue
        for ch in itertools.product(*[ss.max_separators(L, F[x][y], y) for x, y in bad]):
            work += 1
            if work > limit: return None
            T2 = ss.mclose(L, set(T) | set(ch)); succ[T].append(T2)
            if T2 not in succ: stack.append(T2)
    d = {}
    def dist(T):
        if T in d: return d[T]
        d[T] = 0 if goal[T] else 1 + min(dist(T2) for T2 in set(succ[T]))
        return d[T]
    for T in list(succ): dist(T)
    return T0, succ, goal, M, d

def analyze(L, F, D):
    g = graph(L, F, D)
    if g is None: return None
    T0, succ, goal, M, d = g
    good = lambda T, T2: d[T2] == d[T] - 1 and (goal[T2] or M[T2] < M[T])
    # distance from T0
    d0 = {T0: 0}; frontier = [T0]
    while frontier:
        nxt = []
        for T in frontier:
            for T2 in set(succ[T]):
                if T2 not in d0: d0[T2] = d0[T] + 1; nxt.append(T2)
        frontier = nxt
    nongoal = [T for T in succ if not goal[T]]
    fa = [T for T in nongoal if not any(good(T, T2) for T2 in set(succ[T]))]
    onpath = [T for T in nongoal if d0[T] + d[T] == d[T0]]
    fb = [T for T in onpath if not any(good(T, T2) for T2 in set(succ[T]))]
    desc = {}
    def ds(T):
        if T in desc: return desc[T]
        desc[T] = goal[T] or any(good(T, T2) and ds(T2) for T2 in set(succ[T]))
        return desc[T]
    for T in succ: ds(T)
    depths = collections.Counter()
    def runs(T, path):                 # shortest runs from T0
        if goal[T]:
            seq = [M[S] for S in path if not goal[S]]
            k = next((i for i in range(len(seq) - 1) if seq[i + 1] >= seq[i]), None)
            if k is not None:
                j = max(i for i in range(k + 1) if desc[path[i]]) if any(desc[path[i]] for i in range(k + 1)) else None
                depths['none' if j is None else k - j] += 1
            return
        for T2 in set(succ[T]):
            if d[T2] == d[T] - 1: runs(T2, path + [T2])
    runs(T0, [T0])
    return dict(states=len(succ), dT0=d[T0], fail_a=len(fa), fail_b=len(fb), desc0=desc[T0], depths=dict(depths))

if __name__ == '__main__':
    if sys.argv[1] == 'records':
        for key, rs in json.load(open(sys.argv[2])).items():
            for r in rs:
                L = ss.Lat(r['sets']); print(key, r['height'], r['n'], analyze(L, r['F'], r['D']), flush=True)
    else:
        rng = random.Random(int(sys.argv[2])); t0 = time.time(); seeds = []
        for f in sys.argv[4:]:
            data = json.load(open(f)); recs = data['existential_maximal'] if isinstance(data, dict) else data
            seeds += [r for r in recs if r['exist_min'] >= 3]
        tally = collections.Counter(); depth = collections.Counter(); distinct = set(); ex = {}
        while time.time() - t0 < float(sys.argv[3]):
            r = rng.choice(seeds); L = ss.Lat(r['sets']); n = L.n
            g = {(a, b): r['F'][a][b] for a in range(n) for b in range(n)}
            for _ in range(rng.randint(1, 4)):
                a, b = rng.randrange(n), rng.randrange(n); g[(a, b)] = rng.randrange(n) if rng.random() < 0.5 else 0
            F = ss.make_F(L, g); D = r['D']
            key = hash((tuple(L.S), tuple(map(tuple, F)), tuple(D)))
            if key in distinct: continue
            distinct.add(key)
            a = analyze(L, F, D)
            if a is None or a['dT0'] < 3: continue
            tally['instances'] += 1
            tally['(a) fails somewhere'] += a['fail_a'] > 0
            tally['(b) fails on a shortest path'] += a['fail_b'] > 0
            tally['no descending shortest run'] += not a['desc0']
            for k, v in a['depths'].items(): depth[k] += v
            for k in ('fail_a', 'fail_b'):
                if a[k] and (k not in ex or n < ex[k][0]):
                    ex[k] = (n, L.height); json.dump(dict(sets=L.S, F=F, D=D), open(f"state_graph_{k}_s{sys.argv[2]}.json", 'w'))
        print(dict(tally), "exchange depth of non-descending shortest runs:", dict(sorted(depth.items(), key=str)),
              "smallest failures (|L|, height):", ex, flush=True)
