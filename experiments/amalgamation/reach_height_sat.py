"""Exact check of the orbit-height invariant (log §34.3z¹⁴⁰).

(f)  For every monotone F and every k:  ⊤ ∉ R_k  ⟹  R_k contains an element of height ≥ k.
(At k = H only ⊤ has height H, so (f) gives R_H = L: the orbit-length conjecture ORB(H).)
SAT query per k = 1..H−1: some F with every element of height ≥ k outside R_k (amalg_sat.Enc).
UNSAT for all k on a lattice proves (f) on that lattice (solver result).
  python3 reach_height_sat.py (mn N | pencil K | closure K MM SEED COUNT | sweep P NMAX)
"""
import sys, random, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from amalg_sat import Enc
from rstages import stages

def check(L):
    for k in range(1, L.height):
        E = Enc(L, k)
        for z in range(L.n):
            if L.rank[z] >= k: E.S.add_clause([-E.v('r', k, z)])
        if E.S.solve():
            F = E.decode(); st = stages(L, F)
            assert all(st[z] > k for z in range(L.n) if L.rank[z] >= k)
            return k, F
        E.S.delete()
    return None

if __name__ == '__main__':
    fam = sys.argv[1]
    if fam == 'sweep':
        import nodesc_sweep as ns
        P, NMAX = int(sys.argv[2]), int(sys.argv[3]); tally = collections.Counter(); bad = None
        for f in ns.moore_families(P):
            if len(f) > NMAX: continue
            L = ss.Lat(f); r = check(L); tally[(L.height, r is None)] += 1
            if r and (bad is None or L.n < bad[0].n): bad = (L, r)
        print(f"closure systems on {P} points: (height, (f) holds) -> {dict(sorted(tally.items()))}", flush=True)
        if bad: print("smallest violation:", bad[0].n, bad[0].height, bad[0].S, "k =", bad[1][0], flush=True)
    else:
        if fam == 'mn': N = int(sys.argv[2]); Ls = [(f'M_{N}', ss.Lat([0] + [1 << i for i in range(N)] + [(1 << N) - 1]))]
        elif fam == 'pencil':
            import pencil_family; Ls = [(f'near-pencil {sys.argv[2]}', pencil_family.family(int(sys.argv[2]))[0])]
        else:
            k, m, sd, cnt = (int(x) for x in sys.argv[2:6]); rng = random.Random(sd)
            Ls = [(f'closure {k}', ss.Lat(ss.closure_system(k, m, rng))) for _ in range(cnt)]
        for name, L in Ls:
            r = check(L)
            print(f"{name}: |L| = {L.n}, height {L.height}: (f) {'holds (UNSAT for every k)' if r is None else f'FAILS at k = {r[0]}'}", flush=True)
