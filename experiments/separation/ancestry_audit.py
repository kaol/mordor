"""Separator ancestry, column coverage and fans along recorded runs (log §34.3z¹²³; brief A6, B5).

For each instance of stage_records.json, the existential-optimal run (first optimal path found by BFS over all
maximal-separator choices) and the greedy run are replayed. Every chosen separator is a token with its birth stage.
For each bad pair (x, y) at stage n:
  supports: minimum-size sets of tokens born before n (⊥ its own token, ⊤ the empty set) with meet x, resp. y;
  fresh: whether some support contains a token born at stage n-1 (every support must, by `fresh_token`);
  coverage: whether y was a bad column before, and whether x lies in its coverage cone ⋃ ↓x_s (must not);
Fans at each stage: rows of bad pairs sharing a column (join in D, or a minimal subset A whose join reaches a
minimal outside element below the join, |A| ≤ H by `minimal_join_support_bound`); dually columns sharing a row.
Cross-generation response matrix over all bad pairs of the run: entries F(x_i, y_j), i ≠ j, that are witnesses.
'aggregate': greedy with row-fan aggregation (one separator of (⋁X, y) when ⋁X ∈ D) against plain greedy.
  python3 ancestry_audit.py records stage_records.json
  python3 ancestry_audit.py aggregate SEED N
"""
import sys, json, itertools, random
import separator_stages as ss

def optimal_path(L, F, D):
    start = ss.mclose(L, {L.bot, L.top}); layer = {start: None}; hist = [layer]
    def term(T):
        bad = ss.bad_pairs(L, F, D, T); return not bad or any(L.le[y][F[x][y]] for x, y in bad)
    while True:
        done = [T for T in layer if term(T)]
        if done: break
        nxt = {}
        for T in layer:
            bad = ss.bad_pairs(L, F, D, T)
            for ch in itertools.product(*[ss.max_separators(L, F[x][y], y) for x, y in bad]):
                T2 = ss.mclose(L, set(T) | set(ch))
                if T2 not in nxt: nxt[T2] = (T, bad, ch)
        hist.append(nxt); layer = nxt
    T = done[0]; path = []
    for h in reversed(hist[1:]):
        T0, bad, ch = h[T]; path.append((T0, dict(zip(bad, ch)))); T = T0
    return list(reversed(path)), done[0]

def greedy_path(L, F, D):
    T = ss.mclose(L, {L.bot, L.top}); path = []
    while True:
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad): return path, T
        seps = {(x, y): ss.greedy_sep(L, F[x][y], y) for x, y in bad}
        path.append((T, seps)); T = ss.mclose(L, set(T) | set(seps.values()))

def min_support(L, e, tokens, H):
    if e == L.top: return []
    for k in range(1, H + 2):
        for A in itertools.combinations(tokens, k):
            m = L.top
            for v, _ in A: m = L.meet[m][v]
            if m == e: return list(A)
    return None

def analyze(L, F, D, path, final):
    H = L.height; tokens = [(L.bot, -1)]; cover = {}; pairs = []; out = dict(stages=len(path), fresh_ok=True,
        max_support=0, cone_violations=0, old_column_pairs=0, row_fans=[], col_fans=[], cross_witness=0, cross_total=0)
    stages = path + [(final, {})]
    for n, (T, seps) in enumerate(stages):
        bad = ss.bad_pairs(L, F, D, T)
        if n == len(path):           # the final (stuck or terminal) stage
            bad = bad
        for x, y in bad:
            A = min_support(L, x, tokens, H); B = min_support(L, y, tokens, H)
            out['max_support'] = max(out['max_support'], len(A or []), len(B or []))
            if n >= 1:
                fresh = any(b == n - 1 for _, b in (A or []) + (B or []))
                if not fresh: out['fresh_ok'] = False
            if y in cover:
                out['old_column_pairs'] += 1
                if any(L.le[x][xs] for xs in cover[y]): out['cone_violations'] += 1
            pairs.append((n, x, y, A, B))
        # fans
        bycol = {}
        for x, y in bad: bycol.setdefault(y, []).append(x)
        for y, X in bycol.items():
            if len(X) < 2: continue
            j = L.bot
            for x in X: j = L.join[j][x]
            if D[j]: out['row_fans'].append(('join in D', len(X)))
            else:
                us = [u for u in range(L.n) if not D[u] and L.le[u][j] and not any(
                    w != u and not D[w] and L.le[w][u] for w in range(L.n))]
                u = us[0]; best = None
                for k in range(1, len(X) + 1):
                    for Asub in itertools.combinations(X, k):
                        jj = L.bot
                        for a in Asub: jj = L.join[jj][a]
                        if L.le[u][jj]: best = k; break
                    if best: break
                out['row_fans'].append(('join outside', len(X), best, H))
        byrow = {}
        for x, y in bad: byrow.setdefault(x, []).append(y)
        for x, Y in byrow.items():
            if len(Y) < 2: continue
            m = L.top
            for y in Y: m = L.meet[m][y]
            out['col_fans'].append(('meet outside' if not D[m] else 'meet in D', len(Y)))
        for (x, y), s in seps.items():
            cover.setdefault(y, []).append(x)
        for s in set(seps.values()): tokens.append((s, n))
    for (n1, x1, _, _, _), (n2, _, y2, _, _) in itertools.permutations(pairs, 2):
        if n1 == n2: continue
        out['cross_total'] += 1
        if L.le[F[x1][y2]][x1] or L.le[y2][F[x1][y2]]: out['cross_witness'] += 1
    out['pairs'] = [(n, x, y, A, B) for n, x, y, A, B in pairs]
    return out

def agg_greedy(L, F, D, cap=100):
    T = ss.mclose(L, {L.bot, L.top}); st = 0
    while st < cap:
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad): return st
        seps = set(); bycol = {}
        for x, y in bad: bycol.setdefault(y, []).append(x)
        for y, X in bycol.items():
            j = L.bot
            for x in X: j = L.join[j][x]
            if D[j] and not L.le[y][F[j][y]]: seps.add(ss.greedy_sep(L, F[j][y], y))
            else:
                for x in X: seps.add(ss.greedy_sep(L, F[x][y], y))
        T = ss.mclose(L, set(T) | seps); st += 1
    return cap

if __name__ == '__main__':
    if sys.argv[1] == 'records':
        recs = json.load(open(sys.argv[2]))
        for key in recs:
            for r in recs[key]:
                L = ss.Lat(r['sets']); F = r['F']; D = r['D']
                for name, (path, final) in (('optimal', optimal_path(L, F, D)), ('greedy', greedy_path(L, F, D))):
                    a = analyze(L, F, D, path, final)
                    print(f"{key} H={r['height']} |L|={r['n']} {name}: {a['stages']} stages; max support {a['max_support']} "
                          f"(≤ H: {a['max_support'] <= r['height']}); fresh token in every later pair: {a['fresh_ok']}; "
                          f"old-column pairs {a['old_column_pairs']}, cone violations {a['cone_violations']}; "
                          f"row fans {a['row_fans']}; column fans {a['col_fans']}; cross-generation witnesses "
                          f"{a['cross_witness']}/{a['cross_total']}", flush=True)
                    if key == 'existential_maximal' and r['height'] == 4 and name == 'optimal':
                        for n, x, y, A, B in a['pairs']:
                            print(f"    stage {n}: bad ({x},{y}) row support {A} column support {B} "
                                  f"(token = (value, birth stage); ⊥ = (0,-1))", flush=True)
    elif sys.argv[1] == 'aggregate':
        rng = random.Random(int(sys.argv[2])); N = int(sys.argv[3]); fewer = more = same = 0; worst = 0
        for _ in range(N):
            L, g, gens = ss.random_instance(rng.choice([4, 5, 6]), rng.choice([6, 10, 14]), rng)
            F = ss.make_F(L, g); D = ss.Dof(L, gens)
            a = agg_greedy(L, F, D); b = ss.greedy_run(L, F, D)[0]
            if a < b: fewer += 1
            elif a > b: more += 1; worst = max(worst, a - b)
            else: same += 1
        print(f"aggregate-first greedy vs greedy on {N} instances: fewer stages {fewer}, more {more} (max +{worst}), same {same}")
