"""Exact check of the rising-escape step P1' (log §34.3z¹⁴⁰).

At a tight stage k (every element of R_k has height ≤ k) with ⊤ ∉ R_{k+1}, P1' says some m ∈ R_k of height k has
some y > m in R_{k+1}. SAT query (amalg_sat.Enc, k + 1 stages): tight at k, ⊤ ∉ R_{k+1}, and for every m of height
k: m ∈ R_k → no y > m lies in R_{k+1}. (Tightness with OH forces some m of height k into R_k; the query does not
assume OH.) UNSAT for all k proves P1' together with (OH) at k + 1 on that lattice.
With --upc: the stronger orbit-local statement that some height-k element m ∈ R_k has a witness cell (x, y),
x ≤ m < y (F(x, y) ≤ x or y ≤ F(x, y)).
  python3 rising_sat.py [--upc] (sweep P NMAX | closure K MM SEED COUNT | pencil K)
"""
import sys, random, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from amalg_sat import Enc
from rstages import stages

def check_upc(L):
    """Tight stage k, ⊤ ∉ R_{k+1}, and no element m of height k in R_k satisfies UPC(m)."""
    for k in range(0, L.height - 1):
        E = Enc(L, k + 1); r = lambda j, z: E.v('r', j, z); n = L.n
        E.S.add_clause([-r(k + 1, L.top)])
        for z in range(n):
            if L.rank[z] > k: E.S.add_clause([-r(k, z)])
        def fle(x, y, s):
            key = ('fle', x, y, s)
            if key not in E.vars:
                o = E.v(*key); E.iff_or(o, [E.v('f', x, y, w) for w in range(n) if L.le[w][s]])
            return E.vars[key]
        def yle(x, y):
            key = ('yle', x, y)
            if key not in E.vars:
                o = E.v(*key); E.iff_or(o, [E.v('f', x, y, w) for w in range(n) if L.le[y][w]])
            return E.vars[key]
        for m in range(n):
            if L.rank[m] != k: continue
            for x in range(n):
                if not L.le[x][m]: continue
                for y in range(n):
                    if y != m and L.le[m][y]:
                        E.S.add_clause([-r(k, m), -fle(x, y, x)]); E.S.add_clause([-r(k, m), -yle(x, y)])
        if E.S.solve():
            F = E.decode(); return k, F
        E.S.delete()
    return None

def check(L):
    for k in range(0, L.height - 1):
        E = Enc(L, k + 1); r = lambda j, z: E.v('r', j, z)
        E.S.add_clause([-r(k + 1, L.top)])
        for z in range(L.n):
            if L.rank[z] > k: E.S.add_clause([-r(k, z)])
        for m in range(L.n):
            if L.rank[m] != k: continue
            for y in range(L.n):
                if y != m and L.le[m][y]: E.S.add_clause([-r(k, m), -r(k + 1, y)])
        if E.S.solve():
            F = E.decode(); return k, F
        E.S.delete()
    return None

if __name__ == '__main__':
    if '--upc' in sys.argv: sys.argv.remove('--upc'); check = check_upc; NAME = 'UPC at some top element'
    else: NAME = "P1'"
    if sys.argv[1] == 'sweep':
        import nodesc_sweep as ns
        P, NMAX = int(sys.argv[2]), int(sys.argv[3]); T = collections.Counter(); bad = None
        for f in ns.moore_families(P):
            if len(f) > NMAX: continue
            L = ss.Lat(f); res = check(L); T[(L.height, res is None)] += 1
            if res and (bad is None or L.n < bad[0].n): bad = (L, res)
        print(f"closure systems on {P} points: (height, {NAME} holds) -> {dict(sorted(T.items()))}", flush=True)
        if bad:
            L, (k, F) = bad; st = stages(L, F)
            print(f"smallest {NAME} failure: |L| = {L.n}, height {L.height}, k = {k}, sets {L.S}, stages {st}", flush=True)
    else:
        if sys.argv[1] == 'pencil':
            import pencil_family; Ls = [pencil_family.family(int(sys.argv[2]))[0]]
        else:
            k, m, sd, cnt = (int(x) for x in sys.argv[2:6]); rng = random.Random(sd)
            Ls = [ss.Lat(ss.closure_system(k, m, rng)) for _ in range(cnt)]
        for L in Ls:
            res = check(L)
            print(f"|L| = {L.n}, height {L.height}: {NAME} {'holds' if res is None else f'FAILS at k = {res[0]}'}", flush=True)
