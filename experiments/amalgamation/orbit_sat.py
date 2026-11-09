"""Uniform R-orbit length: is R_K = L for every F? (log §34.3z¹⁴⁰)

amalg_sat.Enc unrolled K stages, with the query ¬ r[K][⊤] (some monotone F leaves ⊤ outside R_K). For each lattice
the least K with UNSAT is the exact maximum stage of ⊤ over all monotone F; compared with the edge-height H.
Every SAT model is re-simulated with rstages.stages.
  python3 orbit_sat.py (mn N | pencil K | chain N | closure K MM SEED COUNT | sweep P NMAX)
"""
import sys, random, itertools
sys.path.insert(0, '../separation')
import separator_stages as ss
from amalg_sat import Enc
from rstages import stages

def max_top_stage(L, kmax=None):
    kmax = kmax or L.n
    for K in range(0, kmax + 1):
        E = Enc(L, K); E.S.add_clause([-E.v('r', K, L.top)])
        if not E.S.solve(): E.S.delete(); return K
        F = E.decode(); E.S.delete(); st = stages(L, F)
        assert st[L.top] is None or st[L.top] > K, "model does not reproduce"
    return None

def report(name, L):
    K = max_top_stage(L)
    print(f"{name}: |L| = {L.n}, height {L.height}, max stage of ⊤ over all F = {K} "
          f"({'= H' if K == L.height else '< H' if K < L.height else '> H !'})", flush=True)
    return K

if __name__ == '__main__':
    fam = sys.argv[1]
    if fam == 'mn': N = int(sys.argv[2]); report(f'M_{N}', ss.Lat([0] + [1 << i for i in range(N)] + [(1 << N) - 1]))
    elif fam == 'chain': report(f'chain {sys.argv[2]}', ss.Lat([(1 << i) - 1 for i in range(int(sys.argv[2]))]))
    elif fam == 'pencil':
        import pencil_family; report(f'near-pencil {sys.argv[2]}', pencil_family.family(int(sys.argv[2]))[0])
    elif fam == 'closure':
        k, m, sd, cnt = (int(x) for x in sys.argv[2:6]); rng = random.Random(sd)
        for _ in range(cnt): report(f'closure {k}', ss.Lat(ss.closure_system(k, m, rng)))
    elif fam == 'sweep':
        import nodesc_sweep as ns
        P, NMAX = int(sys.argv[2]), int(sys.argv[3]); import collections; tally = collections.Counter()
        for fam_ in ns.moore_families(P):
            if len(fam_) > NMAX: continue
            L = ss.Lat(fam_); K = max_top_stage(L); tally[(L.height, K - L.height)] += 1
        print(f"all closure systems on {P} points (|L| ≤ {NMAX}): (height, max stage of ⊤ − H) -> {dict(sorted(tally.items()))}", flush=True)
