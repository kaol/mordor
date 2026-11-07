"""Rank-parent audit of the separator process (log §34.3z¹²²; brief §3, §6).

For an instance (lattice, F, D) every run is enumerated (all choices of one maximal separator per bad pair at each
stage). For a transition T → T' with chosen separators sep[(x, y)] and every bad pair (x', y') of T':
  RP-causal: some bad pair (x, y) of T with x' ≤ sep or y' ≤ sep (its causal parent) and
             ρ_{T'}(F(x', y')) < ρ_T(F(x, y))      (ρ_T(z) = rank of cl_T z);
  RP-any:    the same without the causal condition.
A stuck stage (some bad pair with y' ≤ F(x', y')) ends the run with a witness and is exempt from RP.
Reported per instance: whether SOME terminal run satisfies RP at every transition (existential RP), whether ALL
runs do (universal RP), the existential minimum of stages; and, along causal edges parent → child → grandchild, whether
the carriers of Package B nest (v₁ < v₂). Carrier of a causal edge with separator s and child (x', y'):
  both ≤ s: v = s ⊔ F(s, s) (if F(s, s) ≰ s; else 'IH': a witness inside ↓s exists by Cut at lower height),
  otherwise v = s ⊔ x' ⊔ y'.
  python3 rank_audit.py random SEED N        random small instances (closure systems on 4–5 points)
  python3 rank_audit.py records FILE.json    the recorded maximal instances
"""
import sys, json, random, itertools
import separator_stages as ss

def audit(L, F, D, limit=20000):
    rk = L.rank
    rho = lambda T, z: rk[ss.cl(L, T, z)]
    start = ss.mclose(L, {L.bot, L.top})
    res = dict(exists_causal=False, exists_any=False, all_causal=True, all_any=True, min_stages=None,
               nest=0, nonnest=0, ih=0, work=0, aborted=False)
    def terminal(T, bad):
        return not bad or any(L.le[y][F[x][y]] for x, y in bad)
    def dfs(T, depth, ok_c, ok_a, prev_edges):
        if res['aborted']: return
        bad = ss.bad_pairs(L, F, D, T)
        if terminal(T, bad):
            if res['min_stages'] is None or depth < res['min_stages']: res['min_stages'] = depth
            if ok_c: res['exists_causal'] = True
            if ok_a: res['exists_any'] = True
            return
        opts = [ss.max_separators(L, F[x][y], y) for x, y in bad]
        for ch in itertools.product(*opts):
            res['work'] += 1
            if res['work'] > limit: res['aborted'] = True; return
            sep = dict(zip(bad, ch)); T2 = ss.mclose(L, set(T) | set(ch))
            bad2 = ss.bad_pairs(L, F, D, T2)
            c_ok = a_ok = True; edges = []
            stuck2 = any(L.le[y2][F[x2][y2]] for x2, y2 in bad2)     # a stuck stage ends the run with a witness
            for x2, y2 in ([] if stuck2 else bad2):
                r2 = rho(T2, F[x2][y2])
                causal = [(x, y) for (x, y) in bad if L.le[x2][sep[(x, y)]] or L.le[y2][sep[(x, y)]]]
                if not any(r2 < rho(T, F[x][y]) for x, y in causal): c_ok = False
                if not any(r2 < rho(T, F[x][y]) for x, y in bad): a_ok = False
                for (x, y) in causal:
                    s = sep[(x, y)]
                    if L.le[x2][s] and L.le[y2][s]:
                        if L.le[F[s][s]][s]: res['ih'] += 1; v = None
                        else: v = L.join[s][F[s][s]]
                    else: v = L.join[L.join[s][x2]][y2]
                    edges.append(((x2, y2), (x, y), v))
            # carrier nesting: an edge parent→child at this step, child's own edge → grandchild at the previous step
            for (child, parent, v2) in edges:
                for (c1, p1, v1) in prev_edges:
                    if c1 == parent and v1 is not None and v2 is not None:
                        if L.le[v1][v2] and v1 != v2: res['nest'] += 1
                        else: res['nonnest'] += 1
            if not c_ok: res['all_causal'] = False
            if not a_ok: res['all_any'] = False
            dfs(T2, depth + 1, ok_c and c_ok, ok_a and a_ok, edges)
    dfs(start, 0, True, True, [])
    return res

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'random':
        rng = random.Random(int(sys.argv[2])); N = int(sys.argv[3])
        tally = dict(n=0, aborted=0, ex_c=0, ex_a=0, all_c=0, all_a=0, nest=0, nonnest=0, ih=0, nontrivial=0)
        worst = None
        for _ in range(N):
            L, g, gens = ss.random_instance(rng.choice([4, 5]), rng.choice([6, 10]), rng)
            F = ss.make_F(L, g); D = ss.Dof(L, gens)
            r = audit(L, F, D)
            if r['aborted']: tally['aborted'] += 1; continue
            tally['n'] += 1
            if r['min_stages'] >= 2: tally['nontrivial'] += 1
            tally['ex_c'] += r['exists_causal']; tally['ex_a'] += r['exists_any']
            tally['all_c'] += r['all_causal']; tally['all_a'] += r['all_any']
            for k in ('nest', 'nonnest', 'ih'): tally[k] += r[k]
            if not r['exists_causal'] and (worst is None or L.n < worst[0]):
                worst = (L.n, L.height, r['min_stages'], r['exists_any'], L.S, F, D)
        print(json.dumps(tally))
        if worst:
            print(f"smallest instance with NO run satisfying RP-causal: |L| = {worst[0]}, height {worst[1]}, "
                  f"existential minimum {worst[2]}, RP-any run exists: {worst[3]}")
            json.dump(dict(sets=worst[4], F=worst[5], D=worst[6]), open('rp_counterexample.json', 'w'))
    elif mode == 'records':
        recs = json.load(open(sys.argv[2]))
        for key in recs:
            for r in recs[key]:
                L = ss.Lat(r['sets']); a = audit(L, r['F'], r['D'], limit=200000)
                print(f"{key} height {r['height']} |L| {r['n']}: existential min {a['min_stages']}"
                      f"{' (aborted)' if a['aborted'] else ''}; some run RP-causal {a['exists_causal']}, RP-any "
                      f"{a['exists_any']}; all runs RP-causal {a['all_causal']}; carriers nest {a['nest']} / "
                      f"not {a['nonnest']}, IH-branch {a['ih']}", flush=True)
