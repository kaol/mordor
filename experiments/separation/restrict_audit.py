"""Restricted existential descent (log §34.3z¹³⁵).

Does a maximum-gap-descending maximal-separator run still exist when each bad pair's choices are restricted to
  'nonD':  its maximal separators outside D, if there are any (else all);
  'good':  its maximal separators s whose addition alone creates no new bad pair, if any (else all);
  'both':  'nonD' then 'good' on what remains.
Existential: some descending run with choices in the restricted sets; '_forall': every such run descends.
Descent: M_n = max gap h(y) + H − h(x) over bad pairs strictly decreases along the non-goal stages, as in
`MaxGap.cut_of_max_gap_drop`. Memoized DFS over stages; 'cap' = branching budget exceeded.
  python3 restrict_audit.py stored | records FILE | branching FILE | trace FILE MODE | hunt SEED SECONDS FILES...
"""
import sys, json, random, itertools, time, glob, collections
import separator_stages as ss

def make_tools(L, F, D):
    H = L.height; rk = L.rank; phi = lambda p: rk[p[1]] + H - rk[p[0]]
    def goal(bad): return not bad or any(L.le[y][F[x][y]] for x, y in bad)
    def options(T, bad, mode):
        old = set(bad); out = []
        for x, y in bad:
            ms = ss.max_separators(L, F[x][y], y)
            if mode in ('nonD', 'both'):
                o = [s for s in ms if not D[s]]; ms = o or ms
            if mode in ('good', 'both'):
                g = [s for s in ms if set(ss.bad_pairs(L, F, D, ss.mclose(L, set(T) | {s}))) <= old]; ms = g or ms
            out.append(ms)
        return out
    return phi, goal, options

def desc_exists(L, F, D, mode, budget=20000):
    phi, goal, options = make_tools(L, F, D); memo = {}; work = [0]
    def rec(T):
        if T in memo: return memo[T]
        bad = ss.bad_pairs(L, F, D, T)
        if goal(bad): memo[T] = True; return True
        M = max(phi(p) for p in bad); res = False
        for ch in itertools.product(*options(T, bad, mode)):
            work[0] += 1
            if work[0] > budget: raise RuntimeError
            T2 = ss.mclose(L, set(T) | set(ch)); b2 = ss.bad_pairs(L, F, D, T2)
            if goal(b2) or (max(phi(p) for p in b2) < M and rec(T2)): res = True; break
        memo[T] = res; return res
    try: return rec(ss.mclose(L, {L.bot, L.top}))
    except RuntimeError: return None

def desc_forall(L, F, D, mode, budget=20000):
    """Does EVERY run with choices in the restricted sets descend?"""
    phi, goal, options = make_tools(L, F, D); memo = {}; work = [0]
    def rec(T):
        if T in memo: return memo[T]
        bad = ss.bad_pairs(L, F, D, T)
        if goal(bad): memo[T] = True; return True
        M = max(phi(p) for p in bad); res = True
        for ch in itertools.product(*options(T, bad, mode)):
            work[0] += 1
            if work[0] > budget: raise RuntimeError
            T2 = ss.mclose(L, set(T) | set(ch)); b2 = ss.bad_pairs(L, F, D, T2)
            if not (goal(b2) or (max(phi(p) for p in b2) < M and rec(T2))): res = False; break
        memo[T] = res; return res
    try: return rec(ss.mclose(L, {L.bot, L.top}))
    except RuntimeError: return None

MODES = ('all', 'nonD', 'good', 'both')

def audit(L, F, D):
    a = {m: desc_exists(L, F, D, m) for m in MODES}
    a.update({m + '_forall': desc_forall(L, F, D, m) for m in MODES})
    return a

def branching(L, F, D, budget=4000):
    """Over states reachable by 'all' runs: mean number of choice combinations, unrestricted vs 'both'."""
    phi, goal, options = make_tools(L, F, D); seen = set(); stack = [ss.mclose(L, {L.bot, L.top})]; tot = [0, 0, 0, 0]
    while stack and len(seen) < budget:
        T = stack.pop()
        if T in seen: continue
        seen.add(T); bad = ss.bad_pairs(L, F, D, T)
        if goal(bad): continue
        a = options(T, bad, 'all'); b = options(T, bad, 'both')
        ca = 1; cb = 1
        for o in a: ca *= len(o)
        for o in b: cb *= len(o)
        tot[0] += 1; tot[1] += ca; tot[2] += cb; tot[3] += (cb == 1)
        for ch in itertools.product(*a): stack.append(ss.mclose(L, set(T) | set(ch)))
    return tot

def first_failure(L, F, D, mode):
    """Print the first non-descending run (DFS order) with choices in the restricted sets."""
    phi, goal, options = make_tools(L, F, D); nm = lambda i: format(L.S[i], 'b')
    def rec(T, path):
        bad = ss.bad_pairs(L, F, D, T)
        if goal(bad): return True
        M = max(phi(p) for p in bad)
        for ch in itertools.product(*options(T, bad, mode)):
            T2 = ss.mclose(L, set(T) | set(ch)); b2 = ss.bad_pairs(L, F, D, T2)
            p2 = path + [(M, [(nm(x), nm(y), nm(F[x][y])) for x, y in bad], [(nm(s), 'D' if D[s] else 'U') for s in ch])]
            if goal(b2): continue
            if max(phi(p) for p in b2) >= M or not rec(T2, p2):
                if max(phi(p) for p in b2) >= M:
                    for st in p2: print('  stage max gap, bad pairs (x, y, F), added separators:', st)
                    print('  next max gap', max(phi(p) for p in b2), 'bad', [(nm(x), nm(y)) for x, y in b2])
                return False
        return True
    print("height", L.height, "|L|", L.n, "D", [nm(i) for i in range(L.n) if D[i]]); rec(ss.mclose(L, {L.bot, L.top}), [])

if __name__ == '__main__':
    if sys.argv[1] == 'trace':
        d = json.load(open(sys.argv[2])); first_failure(ss.Lat(d['sets']), d['F'], d['D'], sys.argv[3]); sys.exit()
    if sys.argv[1] == 'branching':
        acc = [0, 0, 0, 0]
        for key, rs in json.load(open(sys.argv[2])).items():
            for r in rs:
                L = ss.Lat(r['sets']); t = branching(L, r['F'], r['D']); acc = [u + v for u, v in zip(acc, t)]
        for f in sorted(glob.glob('*counterexample*.json') + glob.glob('state_graph_fail*.json') + glob.glob('*witness*.json')):
            d = json.load(open(f)); d = d[0] if isinstance(d, list) else d; L = ss.Lat(d['sets'])
            t = branching(L, d['F'], d['D']); acc = [u + v for u, v in zip(acc, t)]
        print(f"reachable non-goal states {acc[0]}: mean choice combinations, all {acc[1] / acc[0]:.2f}, "
              f"'both' {acc[2] / acc[0]:.2f}; 'both' unique in {acc[3]} ({100 * acc[3] / acc[0]:.1f} %)", flush=True)
        sys.exit()
    if sys.argv[1] == 'stored':
        for f in sorted(glob.glob('*counterexample*.json') + glob.glob('state_graph_fail*.json') + glob.glob('*witness*.json')):
            d = json.load(open(f)); d = d[0] if isinstance(d, list) else d; L = ss.Lat(d['sets'])
            print(f, L.n, L.height, audit(L, d['F'], d['D']), flush=True)
    elif sys.argv[1] == 'records':
        for key, rs in json.load(open(sys.argv[2])).items():
            for r in rs:
                L = ss.Lat(r['sets']); print(key, r['height'], r['n'], audit(L, r['F'], r['D']), flush=True)
    else:
        rng = random.Random(int(sys.argv[2])); t0 = time.time(); seeds = []
        for f in sys.argv[4:]:
            data = json.load(open(f)); recs = data['existential_maximal'] if isinstance(data, dict) else data
            seeds += [r for r in recs if r['exist_min'] >= 3]
        tally = collections.Counter(); distinct = set(); fails = {}
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
            a = audit(L, F, D); tally['instances'] += 1
            for m, v in a.items():
                tally[(m, v)] += 1
                if v is False and (m not in fails or n < fails[m]['n']):
                    fails[m] = dict(n=n, height=L.height, sets=L.S, F=F, D=D, audit=a)
        print(dict(sorted(tally.items(), key=str)), flush=True)
        for m, ex in fails.items():
            print(f"smallest '{m}' failure: |L| = {ex['n']}, height {ex['height']}, audit {ex['audit']}", flush=True)
            json.dump(ex, open(f"restrict_fail_{m}_s{sys.argv[2]}.json", 'w'))
