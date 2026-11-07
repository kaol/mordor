"""Package C audit: multisets of response closure ranks along every run (log §34.3z¹²²).
For each run of an instance (all separator choices) record, at every non-stuck stage n with bad pairs, the multiset
M_n = {{ ρ_{T_n}(F(x, y)) : (x, y) bad in T_n }}. A potential Φ(M) that strictly decreases along a run is impossible
if the run repeats a multiset (M_i = M_j, i < j). Reported: number of runs, and how many runs repeat a multiset.
  python3 multiset_audit.py stage_records.json
"""
import sys, json, itertools
import separator_stages as ss

def runs(L, F, D, limit=200000):
    start = ss.mclose(L, {L.bot, L.top}); out = []; work = [0]
    def dfs(T, seq):
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad):
            out.append(seq); return
        M = tuple(sorted(L.rank[ss.cl(L, T, F[x][y])] for x, y in bad))
        for ch in itertools.product(*[ss.max_separators(L, F[x][y], y) for x, y in bad]):
            work[0] += 1
            if work[0] > limit: return
            dfs(ss.mclose(L, set(T) | set(ch)), seq + [M])
    dfs(start, [])
    return out

if __name__ == '__main__':
    recs = json.load(open(sys.argv[1]))
    for key in recs:
        for r in recs[key]:
            L = ss.Lat(r['sets']); rs = runs(L, r['F'], r['D'])
            rep = [s for s in rs if len(set(s)) < len(s)]
            ex = min(rs, key=len)
            print(f"{key} height {r['height']} |L| {r['n']}: {len(rs)} runs, {len(rep)} repeat a multiset; "
                  f"a shortest run: {ex}", flush=True)
