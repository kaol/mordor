"""Term rules: absolute separator choices that can jump high (log §34.3z¹³³).

At a stage T with bad pairs B and responses R = {F(x, y) : (x, y) ∈ B}, let C_0 = T ∪ R and
C_{j+1} = C_j ∪ {F(a, b), a ∨ b (and a ∧ b if meets) : a, b ∈ C_j}; C = C_depth (depth None: the full closure, ω).
Rule '..._all': for each bad pair add every separator in C (F(x, y) ≤ s, y ≰ s) maximal among the separators in C;
'..._one': add one of greatest height.  Names: 'term1_all' / 'term1_one' (depth 1, no meets), 'term1m_*' (depth 1,
meets), or variant 'all' / 'one' with explicit meets= and depth=.
Bounded-depth rules are determined by finitely many terms over the run, the property the response transfer of
§34.3z¹³¹ uses (a transfer theorem for them is not formalized). The ω rule is not: in chain-finite lattices the
F/∧/∨-closure of a finite set can be infinite.
  python3 term_rule.py pencil KMAX | records FILE | stored | hunt SEED SECONDS FILES...
"""
import sys, json, random, time, collections, itertools
import separator_stages as ss
from general_sep import phi_of, response_run

def term_run(L, F, D, variant, cap=200, meets=None, depth=1):
    if meets is None: meets = variant.startswith('term1m')
    phi = phi_of(L); T = ss.mclose(L, {L.bot, L.top}); seq = []
    for _ in range(cap):
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad):
            return all(a > b for a, b in zip(seq, seq[1:])), seq
        seq.append(max(phi(p) for p in bad))
        base = set(T) | {F[x][y] for x, y in bad}
        C = set(base)
        for _ in itertools.count() if depth is None else range(depth):       # depth None: full closure (ω)
            C2 = C | {F[a][b] for a in C for b in C} | {L.join[a][b] for a in C for b in C} | \
                ({L.meet[a][b] for a in C for b in C} if meets else set())
            if C2 == C: break
            C = C2
        new = set()
        for x, y in bad:
            cand = [s for s in C if L.le[F[x][y]][s] and not L.le[y][s]]
            mx = [s for s in cand if not any(t != s and L.le[s][t] for t in cand)]
            if variant.endswith('all'): new |= set(mx)
            else: new.add(max(mx, key=lambda s: (L.rank[s], -s)))
        T = ss.mclose(L, set(T) | new)
    return False, seq

if __name__ == '__main__':
    if sys.argv[1] == 'pencil':
        from pencil_family import family
        for k in range(3, int(sys.argv[2]) + 1):
            L, F, D = family(k)
            print(f"k = {k}: response {len(response_run(L, F, D)[1])}, term1_all {len(term_run(L, F, D, 'term1_all')[1])}, "
                  f"term1_one {len(term_run(L, F, D, 'term1_one')[1])}", flush=True)
    elif sys.argv[1] == 'stored':                     # stored counterexamples of earlier rounds
        import glob
        for f in sorted(glob.glob('*counterexample*.json') + glob.glob('state_graph_fail*.json')):
            d = json.load(open(f)); d = d[0] if isinstance(d, list) else d; L = ss.Lat(d['sets'])
            print(f, L.n, L.height, {v: term_run(L, d['F'], d['D'], v) for v in ('term1_all', 'term1_one')}, flush=True)
    elif sys.argv[1] == 'records':
        for key, rs in json.load(open(sys.argv[2])).items():
            for r in rs:
                L = ss.Lat(r['sets'])
                print(key, r['height'], r['n'], {v: term_run(L, r['F'], r['D'], v) for v in ('term1_all', 'term1_one')}, flush=True)
    else:
        rng = random.Random(int(sys.argv[2])); t0 = time.time(); seeds = []
        for f in sys.argv[4:]:
            data = json.load(open(f)); recs = data['existential_maximal'] if isinstance(data, dict) else data
            seeds += [r for r in recs if r['exist_min'] >= 3]
        tally = collections.Counter(); distinct = set(); longest = collections.Counter()
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
            for v in ('term1_all', 'term1_one'):
                d, seq = term_run(L, F, D, v)
                if not d: tally[f'{v} non-descending'] += 1
                longest[(v, L.height)] = max(longest[(v, L.height)], len(seq))
            d, seq = response_run(L, F, D)
            if not d: tally['response non-descending'] += 1
            longest[('response', L.height)] = max(longest[('response', L.height)], len(seq))
        print(dict(tally), "longest run by (rule, height):", dict(sorted(longest.items())), flush=True)
