"""Strict interval containment of causal parents (log §34.3z¹²⁵; brief Programme B).

For an instance and every run (all maximal-separator choices): does SOME terminal run have, at every transition into
a non-stuck stage, for every bad child (x', y') a causal parent (x, y) (bad at the previous stage, its chosen
separator s above x' or y') with
  'contain': x ≤ x' ≤ y' ≤ y and (x, y) ≠ (x', y')  (the brief's strict geometric form), or
  'gap':     rank y' − rank x' < rank y − rank x     (∃-gap-RP)?
Also reported: whether x ≤ y holds for every non-stuck bad pair on such a run.
  python3 containment_audit.py records stage_records.json | random SEED N
"""
import sys, json, random, itertools
import separator_stages as ss

def rel(L, kind):
    rk = L.rank; le = L.le
    if kind == 'contain':
        return lambda c, p: le[p[0]][c[0]] and le[c[0]][c[1]] and le[c[1]][p[1]] and c != p
    return lambda c, p: rk[c[1]] - rk[c[0]] < rk[p[1]] - rk[p[0]]

def exists_run(L, F, D, R, limit=40000):
    start = ss.mclose(L, {L.bot, L.top}); work = [0]; diag = [True]
    def dfs(T):
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad): return True
        for ch in itertools.product(*[ss.max_separators(L, F[x][y], y) for x, y in bad]):
            work[0] += 1
            if work[0] > limit: return None
            sep = dict(zip(bad, ch)); T2 = ss.mclose(L, set(T) | set(ch)); bad2 = ss.bad_pairs(L, F, D, T2)
            if not any(L.le[y2][F[x2][y2]] for x2, y2 in bad2):
                ok = all(any((L.le[c[0]][sep[p]] or L.le[c[1]][sep[p]]) and R(c, p) for p in bad) for c in bad2)
                if not ok: continue
            r = dfs(T2)
            if r: return True
            if r is None: return None
        return False
    return dfs(start)

def xle_y_on_optimal(L, F, D):
    import ancestry_audit as aa
    path, final = aa.optimal_path(L, F, D)
    return all(L.le[x][y] for T, seps in path for (x, y) in seps)

if __name__ == '__main__':
    if sys.argv[1] == 'records':
        recs = json.load(open(sys.argv[2]))
        for key in recs:
            for r in recs[key]:
                L = ss.Lat(r['sets'])
                res = {k: exists_run(L, r['F'], r['D'], rel(L, k)) for k in ('contain', 'gap')}
                print(f"{key} H={r['height']} |L|={r['n']}: {res}; x ≤ y on every processed pair of an optimal run: "
                      f"{xle_y_on_optimal(L, r['F'], r['D'])}", flush=True)
    else:
        rng = random.Random(int(sys.argv[2])); tally = {'contain': [0, 0, 0], 'gap': [0, 0, 0]}; xy = [0, 0]; smallest = {}
        for _ in range(int(sys.argv[3])):
            L, g, gens = ss.random_instance(rng.choice([4, 5]), rng.choice([6, 10]), rng)
            F = ss.make_F(L, g); D = ss.Dof(L, gens)
            for k in tally:
                r = exists_run(L, F, D, rel(L, k))
                tally[k][0 if r else (1 if r is False else 2)] += 1
                if r is False and (k not in smallest or L.n < smallest[k][0]): smallest[k] = (L.n, L.height)
            xy[xle_y_on_optimal(L, F, D)] += 1
        print("survives / fails / undecided:", tally, "; smallest failure (|L|, height):", smallest,
              f"; optimal runs with x ≤ y on all processed pairs: {xy[1]} of {sum(xy)}")
