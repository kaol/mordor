"""Maximum-gap descent along runs of the separator process (log §34.3z¹²⁶; brief Part A).

M_n = max over bad pairs (x, y) of stage n of φ(x, y) = height(y) + (H − height(x)), H = height of the lattice.
A run has max-gap descent if M_{n+1} < M_n at every transition into a non-stuck stage with bad pairs (Lean
`MaxGap.cut_of_max_gap_drop`; equivalent to non-causal parent existence, `parent_iff_max_drop`).
For each instance, over all runs (all maximal-separator choices): does SOME run descend (existential), do ALL runs
(universal)? Failures of the universal form are minimized by size and reported with their M sequence.
  python3 gapmax_audit.py records FILE | random SEED N | hunt SEED SECONDS FILES... | rule FILE | rulehunt SEED SECONDS FILES...
"""
import sys, json, random, itertools, time
import separator_stages as ss

def runs_descent(L, F, D, limit=40000):
    H = L.height; rk = L.rank
    phi = lambda p: rk[p[1]] + H - rk[p[0]]
    start = ss.mclose(L, {L.bot, L.top}); work = [0]; res = dict(exists=False, all=True, aborted=False, bad_seq=None)
    def dfs(T, seq):
        if work[0] > limit: res['aborted'] = True; return
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad):
            if all(a > b for a, b in zip(seq, seq[1:])): res['exists'] = True
            else:
                res['all'] = False
                if res['bad_seq'] is None: res['bad_seq'] = seq
            return
        M = max(phi(p) for p in bad)
        for ch in itertools.product(*[ss.max_separators(L, F[x][y], y) for x, y in bad]):
            work[0] += 1
            dfs(ss.mclose(L, set(T) | set(ch)), seq + [M])
    dfs(start, [])
    return res

def lookahead_run(L, F, D, cap=60, limit=20000):
    """Deterministic rule: at each stage take the choice tuple minimizing the next maximum gap (ties: first found).
    Returns (descends, M sequence)."""
    H = L.height; rk = L.rank; phi = lambda p: rk[p[1]] + H - rk[p[0]]
    T = ss.mclose(L, {L.bot, L.top}); seq = []; work = 0
    for _ in range(cap):
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad):
            return all(a > b for a, b in zip(seq, seq[1:])), seq
        seq.append(max(phi(p) for p in bad)); best = None
        for ch in itertools.product(*[ss.max_separators(L, F[x][y], y) for x, y in bad]):
            work += 1
            if work > limit: return None, seq
            T2 = ss.mclose(L, set(T) | set(ch)); b2 = ss.bad_pairs(L, F, D, T2)
            stuck2 = any(L.le[y][F[x][y]] for x, y in b2)
            key = -1 if (not b2 or stuck2) else max(phi(p) for p in b2)
            if best is None or key < best[0]: best = (key, T2)
        T = best[1]
    return False, seq

if __name__ == '__main__' and sys.argv[1] == 'rule':
    data = json.load(open(sys.argv[2])); ok = fail = und = 0
    for key, rs in data.items():
        for r in rs:
            L = ss.Lat(r['sets']); d, seq = lookahead_run(L, r['F'], r['D'])
            print(f"{key} H={r['height']} |L|={r['n']}: lookahead rule descends {d}, M = {seq}", flush=True)
    raise SystemExit

if __name__ == '__main__' and sys.argv[1] == 'rulehunt':
    rng = random.Random(int(sys.argv[2])); t0 = time.time(); seeds = []
    for f in sys.argv[4:]:
        data = json.load(open(f)); recs = data['existential_maximal'] if isinstance(data, dict) else data
        seeds += [r for r in recs if r['exist_min'] >= 3]
    tested = fails = 0; distinct = set(); smallest = None
    while time.time() - t0 < float(sys.argv[3]):
        r = rng.choice(seeds); L = ss.Lat(r['sets']); n = L.n
        g = {(a, b): r['F'][a][b] for a in range(n) for b in range(n)}
        for _ in range(rng.randint(1, 4)):
            a, b = rng.randrange(n), rng.randrange(n); g[(a, b)] = rng.randrange(n) if rng.random() < 0.5 else 0
        F = ss.make_F(L, g); D = r['D']
        key = hash((tuple(L.S), tuple(map(tuple, F)), tuple(D)))
        if key in distinct: continue
        distinct.add(key)
        st = ss.exist_min(L, F, D)
        if st is None or st < 3: continue
        d, seq = lookahead_run(L, F, D); tested += 1
        if d is False:
            fails += 1
            if smallest is None or n < smallest['n']:
                smallest = dict(n=n, height=L.height, seq=seq, sets=L.S, F=F, D=D)
    print(f"lookahead rule on {tested} distinct mutated hard instances: fails {fails}", flush=True)
    if smallest:
        print(f"smallest failure: |L| = {smallest['n']}, height {smallest['height']}, M = {smallest['seq']}")
        json.dump(smallest, open(f"gapmax_lookahead_counterexample_s{sys.argv[2]}.json", 'w'))
    raise SystemExit

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'records':
        for key, rs in json.load(open(sys.argv[2])).items():
            for r in rs:
                L = ss.Lat(r['sets']); a = runs_descent(L, r['F'], r['D'])
                print(f"{key} H={r['height']} |L|={r['n']}: some run descends {a['exists']}, all runs descend "
                      f"{a['all']}{' (aborted)' if a['aborted'] else ''}; failing M-sequence {a['bad_seq']}", flush=True)
    elif mode == 'random':
        rng = random.Random(int(sys.argv[2])); t = dict(n=0, ex=0, all=0, aborted=0); smallest = None
        for _ in range(int(sys.argv[3])):
            L, g, gens = ss.random_instance(rng.choice([4, 5, 6]), rng.choice([6, 10, 14]), rng)
            F = ss.make_F(L, g); D = ss.Dof(L, gens); a = runs_descent(L, F, D)
            t['n'] += 1; t['ex'] += a['exists']; t['all'] += a['all']; t['aborted'] += a['aborted']
            if not a['all'] and (smallest is None or L.n < smallest['n']):
                smallest = dict(n=L.n, height=L.height, seq=a['bad_seq'], sets=L.S, F=F, D=D)
        print(json.dumps(t))
        if smallest:
            print(f"smallest instance where some run fails max-gap descent: |L| = {smallest['n']}, height "
                  f"{smallest['height']}, M-sequence {smallest['seq']}")
            json.dump(smallest, open(f"gapmax_universal_counterexample_s{sys.argv[2]}.json", 'w'))
    elif mode == 'hunt':
        rng = random.Random(int(sys.argv[2])); t0 = time.time(); seeds = []
        for f in sys.argv[4:]:
            data = json.load(open(f)); recs = data['existential_maximal'] if isinstance(data, dict) else data
            seeds += [r for r in recs if r['exist_min'] >= 3]
        tested = 0; exfail = 0; allfail = 0; distinct = set()
        while time.time() - t0 < float(sys.argv[3]):
            r = rng.choice(seeds); L = ss.Lat(r['sets']); n = L.n
            g = {(a, b): r['F'][a][b] for a in range(n) for b in range(n)}
            for _ in range(rng.randint(1, 4)):
                a, b = rng.randrange(n), rng.randrange(n); g[(a, b)] = rng.randrange(n) if rng.random() < 0.5 else 0
            F = ss.make_F(L, g); D = r['D']
            st = ss.exist_min(L, F, D)
            if st is None or st < 3: continue
            key = hash((tuple(L.S), tuple(map(tuple, F)), tuple(D)))
            if key in distinct: continue
            distinct.add(key); a = runs_descent(L, F, D); tested += 1
            if not a['exists'] and not a['aborted']:
                exfail += 1; print(f"EXISTENTIAL FAILURE |L| {n} height {L.height}", flush=True)
                json.dump(dict(sets=L.S, F=F, D=D), open(f"gapmax_existential_counterexample_s{sys.argv[2]}.json", 'w'))
            if not a['all']: allfail += 1
        print(f"tested {tested} distinct mutated hard instances (existential minimum ≥ 3): existential failures "
              f"{exfail}, instances with some non-descending run {allfail}", flush=True)
