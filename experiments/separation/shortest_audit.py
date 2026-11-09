"""Do shortest runs have maximum-gap descent? (log §34.3z¹²⁷)

For each instance: all runs (all maximal-separator choices); among the runs of minimum length (the existential
minimum of stages), count those with strictly decreasing stage maximum gap M_n (stuck stages exempt, as in
`MaxGap.cut_of_max_gap_drop`). Reported: instances where SOME shortest run descends, where ALL do, where NONE does;
also whether some descending run is longer than the shortest.
  python3 shortest_audit.py records FILE | hunt SEED SECONDS FILES...
"""
import sys, json, random, itertools, time
import separator_stages as ss

def runs(L, F, D, limit=40000):
    H = L.height; rk = L.rank; phi = lambda p: rk[p[1]] + H - rk[p[0]]
    start = ss.mclose(L, {L.bot, L.top}); out = []; work = [0]
    def dfs(T, seq):
        if work[0] > limit: raise RuntimeError
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad): out.append(seq); return
        M = max(phi(p) for p in bad)
        for ch in itertools.product(*[ss.max_separators(L, F[x][y], y) for x, y in bad]):
            work[0] += 1; dfs(ss.mclose(L, set(T) | set(ch)), seq + [M])
    try: dfs(start, [])
    except RuntimeError: return None
    return out

def classify(rs):
    desc = lambda s: all(a > b for a, b in zip(s, s[1:]))
    m = min(len(s) for s in rs); short = [s for s in rs if len(s) == m]
    k = sum(desc(s) for s in short)
    longer_desc = any(desc(s) for s in rs if len(s) > m)
    return ('all' if k == len(short) else 'some' if k else 'none'), longer_desc, m

if __name__ == '__main__':
    if sys.argv[1] == 'records':
        for key, rs in json.load(open(sys.argv[2])).items():
            for r in rs:
                L = ss.Lat(r['sets']); R = runs(L, r['F'], r['D'])
                print(key, r['height'], r['n'], classify(R) if R else 'aborted', flush=True)
    else:
        rng = random.Random(int(sys.argv[2])); t0 = time.time(); seeds = []
        for f in sys.argv[4:]:
            data = json.load(open(f)); recs = data['existential_maximal'] if isinstance(data, dict) else data
            seeds += [r for r in recs if r['exist_min'] >= 3]
        tally = {}; distinct = set(); none_ex = None
        while time.time() - t0 < float(sys.argv[3]):
            r = rng.choice(seeds); L = ss.Lat(r['sets']); n = L.n
            g = {(a, b): r['F'][a][b] for a in range(n) for b in range(n)}
            for _ in range(rng.randint(1, 4)):
                a, b = rng.randrange(n), rng.randrange(n); g[(a, b)] = rng.randrange(n) if rng.random() < 0.5 else 0
            F = ss.make_F(L, g); D = r['D']
            key = hash((tuple(L.S), tuple(map(tuple, F)), tuple(D)))
            if key in distinct: continue
            distinct.add(key); R = runs(L, F, D)
            if R is None: continue
            c, ld, m = classify(R)
            if m < 3: continue
            tally[(c, ld)] = tally.get((c, ld), 0) + 1
            if c == 'none' and (none_ex is None or n < none_ex['n']):
                none_ex = dict(n=n, height=L.height, sets=L.S, F=F, D=D, runs=[s for s in R if len(s) == m])
        print("shortest runs: (descending among shortest, some longer run descends) ->", tally, flush=True)
        if none_ex:
            print(f"smallest instance with no descending shortest run: |L| = {none_ex['n']}, height {none_ex['height']}, "
                  f"shortest M-sequences {none_ex['runs'][:4]}")
            json.dump(none_ex, open(f"shortest_nondescending_s{sys.argv[2]}.json", 'w'))
