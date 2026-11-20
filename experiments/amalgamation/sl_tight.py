"""Lower-stage tightness in the SingletonLower configuration (log §34.3z²⁴⁹).
Hypotheses (SingletonLower at k, without its conclusion): ⊤ ∉ R_{k+2}; R_k, R_{k+1} tight; m the unique element of height
k + 1 in R_{k+1}; m ∈ R_{k+1} \\ R_k; m' ∈ R_k, h(m') = k, m' < m, F(m', m) ≤ m'.
  python3 sl_tight.py k J (sweep N MAX | closure K M SEED CNT) [noic]
SAT = a model where R_J (J < k) is non-tight.  'noic': add "m has no interval cell" (vacuous if SingletonLower holds).
'vac': drop the non-tightness requirement (model count).
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from rstages import stages
k = int(sys.argv[1]); J = int(sys.argv[2]); NOIC = 'noic' in sys.argv; VAC = 'vac' in sys.argv
args = [a for a in sys.argv[3:] if a not in ('noic', 'vac')]
C = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; top = L.top
    for m in range(n):
        if h[m] != k + 1 or L.height <= k + 1: continue
        E = Enc(L, k + 2); fle, yle, ic = helpers(E, L); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
        add([-r(k + 2, top)]); add([r(k + 1, m)]); add([-r(k, m)])
        if NOIC: add([-ic(m)])
        for z in range(n):
            if h[z] > k: add([-r(k, z)])
            if h[z] > k + 1: add([-r(k + 1, z)])
            if h[z] == k + 1 and z != m: add([-r(k + 1, z)])
        fe = []
        for mp in range(n):
            if h[mp] == k and le[mp][m]: o = E.v('feed', mp); E.iff_and(o, [r(k, mp), fle(mp, m, mp)]); fe.append(o)
        if not fe: E.S.delete(); continue
        add(fe)
        if not VAC: add([r(J, z) for z in range(n) if h[z] > J])
        if E.S.solve():
            F = E.decode(); st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j
            assert VAC or any(h[z] > J and inR(z, J) for z in range(n))
            C['SAT'] += 1
            if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F, m=m))
        else: C['UNSAT'] += 1
        E.S.delete()
print('k', k, 'J', J, 'noic' if NOIC else '', 'vac' if VAC else '', dict(C), 'smallest', best[0] if best else None)
if best and not VAC: json.dump(best[1], open(f'sltight_k{k}_J{J}{"_noic" if NOIC else ""}_min{best[0]}.json', 'w'))
