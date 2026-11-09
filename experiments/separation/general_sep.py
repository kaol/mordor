"""General (not necessarily maximal) separators (log §34.3z¹³¹).

A general separator of a bad pair (x, y) is any s with F(x, y) ≤ s and y ≰ s; the process stays sound
(`separating_family_witness` needs only some separator) and legality becomes absolute (it refers to s, x, y, F(x, y)
only). Tested, with maximum-gap descent (stuck stages exempt):
  'response': the canonical rule s = F(x, y) (choice-free; the run is the meet-closed cross-closure);
  'polar1/2': responses outside D kept, responses in D replaced by a maximal separator (see polar_run);
  'exist':    existential descent over all general separators (exact branching, small instances), compared with the
              maximal-separator process.
  python3 general_sep.py records FILE | hunt SEED SECONDS FILES...
"""
import sys, json, random, itertools, time, collections
import separator_stages as ss

def gseps(L, F, x, y):
    return [s for s in range(L.n) if L.le[F[x][y]][s] and not L.le[y][s]]

def phi_of(L):
    H = L.height; rk = L.rank; return lambda p: rk[p[1]] + H - rk[p[0]]

def response_run(L, F, D, cap=200):
    phi = phi_of(L); T = ss.mclose(L, {L.bot, L.top}); seq = []
    for _ in range(cap):
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad):
            return all(a > b for a, b in zip(seq, seq[1:])), seq
        seq.append(max(phi(p) for p in bad)); T = ss.mclose(L, set(T) | {F[x][y] for x, y in bad})
    return False, seq

def polar_run(L, F, D, variant, cap=200):
    """Polar rules: a response outside D (a new column) is kept as the separator (lowest possible); a response in D
    (a new row) is replaced by a maximal separator ('polar1': greedy ascent; 'polar2': a maximal separator of greatest
    height, preferring members of D)."""
    phi = phi_of(L); T = ss.mclose(L, {L.bot, L.top}); seq = []
    for _ in range(cap):
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad):
            return all(a > b for a, b in zip(seq, seq[1:])), seq
        seq.append(max(phi(p) for p in bad)); new = set()
        for x, y in bad:
            z = F[x][y]
            if not D[z]: new.add(z)
            elif variant == 'polar1': new.add(ss.greedy_sep(L, z, y))
            else:
                ms = ss.max_separators(L, z, y)
                new.add(max(ms, key=lambda s: (D[s], L.rank[s], -s)))
        T = ss.mclose(L, set(T) | new)
    return False, seq

def exist_desc(L, F, D, sepfun, limit=60000):
    phi = phi_of(L); work = [0]; memo = {}
    def go(T, bound):
        key = (T, bound)
        if key in memo: return memo[key]
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad): memo[key] = True; return True
        M = max(phi(p) for p in bad)
        if bound is not None and M >= bound: memo[key] = False; return False
        res = False
        for ch in itertools.product(*[sepfun(L, F, x, y) for x, y in bad]):
            work[0] += 1
            if work[0] > limit: raise RuntimeError
            if go(ss.mclose(L, set(T) | set(ch)), M): res = True; break
        memo[key] = res; return res
    try: return go(ss.mclose(L, {L.bot, L.top}), None)
    except RuntimeError: return None

if __name__ == '__main__':
    if sys.argv[1] == 'records':
        for key, rs in json.load(open(sys.argv[2])).items():
            for r in rs:
                L = ss.Lat(r['sets']); F = r['F']; D = r['D']
                print(key, r['height'], r['n'], 'response rule:', response_run(L, F, D),
                      '| polar1:', polar_run(L, F, D, 'polar1'), '| polar2:', polar_run(L, F, D, 'polar2'),
                      '| existential (general):', exist_desc(L, F, D, gseps),
                      '| existential (maximal):', exist_desc(L, F, D, lambda L_, F_, x, y: ss.max_separators(L_, F_[x][y], y)), flush=True)
    else:
        rng = random.Random(int(sys.argv[2])); t0 = time.time(); seeds = []
        for f in sys.argv[4:]:
            data = json.load(open(f)); recs = data['existential_maximal'] if isinstance(data, dict) else data
            seeds += [r for r in recs if r['exist_min'] >= 3]
        tally = collections.Counter(); distinct = set(); smallest = None
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
            tally['instances'] += 1
            for v in ('polar1', 'polar2'):
                if not polar_run(L, F, D, v)[0]: tally[f'{v} fails'] += 1
            d, seq = response_run(L, F, D)
            if not d:
                tally['response rule fails'] += 1
                if smallest is None or n < smallest[0]:
                    smallest = (n, L.height, seq)
                    json.dump(dict(sets=L.S, F=F, D=D, seq=seq), open(f"response_rule_counterexample_s{sys.argv[2]}.json", 'w'))
            if len(sys.argv) > 4 and '--exist' in sys.argv:
                eg = exist_desc(L, F, D, gseps); tally[f'existential general: {eg}'] += 1
        print(dict(tally), "smallest response-rule failure (|L|, height, M):", smallest, flush=True)
