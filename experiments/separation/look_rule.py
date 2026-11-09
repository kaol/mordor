"""Lookahead term rules (log §34.3z¹³⁴).

At stage T with bad pairs B, let C be the depth-d term closure of T ∪ R (term_rule.py). For each bad pair p let M_p be
its C-maximal separators and good(s) ⟺ every bad pair of meetClose(T ∪ {s}) is already a bad pair of T (adding s
alone creates no new bad pair). Rule 'look': add, for every p, the good members of M_p if there are any, else all of
M_p. All data are terms over T ∪ R and F-values on T ∪ {s}, so bounded-depth versions are finitely determined.
  python3 look_rule.py families KMAX | stored | hunt SEED SECONDS FILES...
"""
import sys, json, random, time, collections, itertools, glob
import separator_stages as ss

def closure(L, F, base, depth, meets=True):
    C = set(base)
    for _ in itertools.count() if depth is None else range(depth):
        C2 = C | {F[a][b] for a in C for b in C} | {L.join[a][b] for a in C for b in C} | \
            ({L.meet[a][b] for a in C for b in C} if meets else set())
        if C2 == C: break
        C = C2
    return C

def look_run(L, F, D, depth=1, meets=True, cap=200):
    T = ss.mclose(L, {L.bot, L.top}); n = 0
    for _ in range(cap):
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad): return n
        n += 1; old = set(bad)
        C = closure(L, F, set(T) | {F[x][y] for x, y in bad}, depth, meets); new = set()
        for x, y in bad:
            cand = [s for s in C if L.le[F[x][y]][s] and not L.le[y][s]]
            mx = [s for s in cand if not any(t != s and L.le[s][t] for t in cand)]
            good = [s for s in mx if set(ss.bad_pairs(L, F, D, ss.mclose(L, set(T) | {s}))) <= old]
            new |= set(good) if good else set(mx)
        T = ss.mclose(L, set(T) | new)
    return None

if __name__ == '__main__':
    if sys.argv[1] == 'families':
        import pencil_family, term_family
        for k in range(3, int(sys.argv[2]) + 1):
            out = []
            for fam in (pencil_family, term_family):
                L, F, D = fam.family(k); out.append([look_run(L, F, D, d) for d in (1, 2, None)])
            print(f"k = {k}: look depth 1/2/ω on response family {out[0]}, on term family {out[1]}", flush=True)
    elif sys.argv[1] == 'stored':
        for f in sorted(glob.glob('*counterexample*.json') + glob.glob('state_graph_fail*.json') + glob.glob('term_*witness*.json')):
            d = json.load(open(f)); d = d[0] if isinstance(d, list) else d; L = ss.Lat(d['sets'])
            print(f, L.n, L.height, [look_run(L, d['F'], d['D'], dd) for dd in (1, 2, None)],
                  "existential", ss.exist_min(L, d['F'], d['D']), flush=True)
