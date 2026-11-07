"""Existential parent-decrease test for candidate potentials φ(T, x, y) (log §34.3z¹²³; brief Deliverable 5).

φ-RP for a run: at every transition into a non-stuck stage, every bad pair (x', y') of T_{n+1} has a causal parent
(x, y), bad in T_n with chosen separator s and x' ≤ s or y' ≤ s, with φ(T_{n+1}, x', y') < φ(T_n, x, y).
φ bounded on bad pairs makes a φ-RP run end within (range of φ) stages. Tested, for each instance, by exhaustive search
over all maximal-separator choices: does SOME terminal run satisfy φ-RP?
Candidates: resp = rank cl_T F(x,y) (refuted, §34.3z¹²²); col = rank y; gap = rank y - rank x;
respgap = rank cl_T F(x,y) - rank x; colsum = rank y + (H - rank x)... (equivalent ordering to gap).
  python3 potential_audit.py random SEED N | records FILE.json | hunt SEED SECONDS K | hunt_from SEED SECONDS FILES...
"""
import sys, json, random, itertools
import separator_stages as ss

def phis(L):
    rk = L.rank
    return {
        'resp': lambda T, F, x, y: rk[ss.cl(L, T, F[x][y])],
        'col': lambda T, F, x, y: rk[y],
        'gap': lambda T, F, x, y: rk[y] - rk[x],
        'respgap': lambda T, F, x, y: rk[ss.cl(L, T, F[x][y])] - rk[x],
    }

def exists_rp(L, F, D, phi, limit=20000):
    start = ss.mclose(L, {L.bot, L.top}); work = [0]; aborted = [False]
    def dfs(T):
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad): return True
        for ch in itertools.product(*[ss.max_separators(L, F[x][y], y) for x, y in bad]):
            work[0] += 1
            if work[0] > limit: aborted[0] = True; return False
            sep = dict(zip(bad, ch)); T2 = ss.mclose(L, set(T) | set(ch)); bad2 = ss.bad_pairs(L, F, D, T2)
            if not any(L.le[y2][F[x2][y2]] for x2, y2 in bad2):
                ok = all(any((L.le[x2][sep[p]] or L.le[y2][sep[p]]) and phi(T2, F, x2, y2) < phi(T, F, *p) for p in bad)
                         for x2, y2 in bad2)
                if not ok: continue
            if dfs(T2): return True
        return False
    r = dfs(start)
    return None if aborted[0] and not r else r

def hunt(seed, seconds, k):
    """Hill-climb (F, D) on closure systems on k points toward large existential minimum; test gap / respgap at every
    accepted state and report the first failure (a minimal-size one is kept)."""
    import time
    rng = random.Random(seed); t0 = time.time(); tested = 0; found = {}
    while time.time() - t0 < seconds:
        L, g, gens = ss.random_instance(k, rng.choice([6, 10, 14]), rng)
        if L.height < k - 1: continue
        F = ss.make_F(L, g); D = ss.Dof(L, gens); cur = ss.exist_min(L, F, D)
        if cur is None: continue
        for _ in range(40):
            if time.time() - t0 > seconds: break
            g2 = dict(g); gens2 = list(gens)
            for _ in range(rng.randint(1, 3)):
                if rng.random() < 0.8:
                    a, b = rng.randrange(L.n), rng.randrange(L.n)
                    if rng.random() < 0.6: g2[(a, b)] = rng.randrange(L.n)
                    else: g2.pop((a, b), None)
                else: gens2 = sorted(set(gens2) ^ {rng.randrange(L.n - 1)}) or [0]
            F2 = ss.make_F(L, g2); D2 = ss.Dof(L, gens2); st = ss.exist_min(L, F2, D2)
            if st is None or st < cur: continue
            g, gens, cur, F, D = g2, gens2, st, F2, D2
            tested += 1
            for kk in ('gap', 'respgap'):
                r = exists_rp(L, F, D, phis(L)[kk])
                if r is False and (kk not in found or L.n < found[kk]['n']):
                    found[kk] = dict(n=L.n, height=L.height, exist_min=cur, sets=L.S, F=F, D=D)
                    print(f"{kk} FAILS: |L| {L.n}, height {L.height}, existential minimum {cur}", flush=True)
    print(f"tested {tested} accepted states (k={k}); failures: {sorted(found)}", flush=True)
    if found: json.dump(found, open(f"potential_counterexamples_k{k}_s{seed}.json", 'w'))

def hunt_from(seed, seconds, files, floor=3):
    """Mutate hard recorded instances (existential minimum ≥ floor), keep mutations with existential minimum ≥ floor,
    test gap / respgap on each kept state."""
    import time
    rng = random.Random(seed); t0 = time.time(); seeds = []
    for f in files:
        data = json.load(open(f)); recs = data['existential_maximal'] if isinstance(data, dict) else data
        seeds += [r for r in recs if r['exist_min'] >= floor]
    tested = 0; found = {}; hist = {}; distinct = set()
    while time.time() - t0 < seconds:
        r = rng.choice(seeds); L = ss.Lat(r['sets']); n = L.n
        F = [row[:] for row in r['F']]; D = list(r['D'])
        # perturb F by re-closing a random sparse generator on top of the recorded table
        g = {(a, b): F[a][b] for a in range(n) for b in range(n)}
        for _ in range(60):
            if time.time() - t0 > seconds: break
            g2 = dict(g)
            for _ in range(rng.randint(1, 4)):
                a, b = rng.randrange(n), rng.randrange(n); g2[(a, b)] = rng.randrange(n) if rng.random() < 0.5 else 0
            F2 = ss.make_F(L, g2); D2 = D
            if rng.random() < 0.2:
                gens = [i for i in range(n) if D[i]]; c = rng.randrange(n - 1)
                D2 = ss.Dof(L, sorted(set(gens) ^ {c}) or [0])
            st = ss.exist_min(L, F2, D2)
            if st is None or st < floor: continue
            g, F, D = g2, F2, D2; tested += 1; hist[st] = hist.get(st, 0) + 1
            distinct.add(hash((tuple(L.S), tuple(map(tuple, F)), tuple(D))))
            for kk in ('gap', 'respgap'):
                rr = exists_rp(L, F, D, phis(L)[kk])
                if rr is False and (kk not in found or L.n < found[kk]['n']):
                    found[kk] = dict(n=L.n, height=L.height, exist_min=st, sets=L.S, F=F, D=D)
                    print(f"{kk} FAILS: |L| {L.n}, height {L.height}, existential minimum {st}", flush=True)
    print(f"tested {tested} states ({len(distinct)} distinct) with existential minimum ≥ {floor} "
          f"(histogram {dict(sorted(hist.items()))}); "
          f"failures: {sorted(found)}", flush=True)
    if found: json.dump(found, open(f"potential_counterexamples_s{seed}.json", 'w'))

if __name__ == '__main__' and sys.argv[1] == 'hunt_from':
    hunt_from(int(sys.argv[2]), float(sys.argv[3]), sys.argv[4:]); raise SystemExit

if __name__ == '__main__' and sys.argv[1] == 'hunt':
    hunt(int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])); raise SystemExit

if __name__ == '__main__':
    insts = []
    if sys.argv[1] == 'random':
        rng = random.Random(int(sys.argv[2]))
        for _ in range(int(sys.argv[3])):
            L, g, gens = ss.random_instance(rng.choice([4, 5]), rng.choice([6, 10]), rng)
            insts.append((f"random", L, ss.make_F(L, g), ss.Dof(L, gens)))
    else:
        recs = json.load(open(sys.argv[2]))
        for key in recs:
            for r in recs[key]: insts.append((f"{key} H={r['height']} |L|={r['n']}", ss.Lat(r['sets']), r['F'], r['D']))
    tally = {k: [0, 0, 0] for k in ['resp', 'col', 'gap', 'respgap']}
    fails = {k: [] for k in tally}
    for name, L, F, D in insts:
        for k, phi in phis(L).items():
            r = exists_rp(L, F, D, phi)
            tally[k][0 if r else (1 if r is False else 2)] += 1
            if r is False: fails[k].append((L.n, L.height, name))
        if sys.argv[1] == 'records':
            print(name, {k: exists_rp(L, F, D, phi) for k, phi in phis(L).items()}, flush=True)
    print("survives / fails / undecided:", tally)
    for k, f in fails.items():
        if f: print(f"  smallest failure of {k}: |L| = {min(f)[0]}, height {min(f)[1]} ({min(f)[2]})")
