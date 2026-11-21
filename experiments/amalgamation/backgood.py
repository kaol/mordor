"""BackGood (log §34.3z²⁵⁷): does a later tight stage certify goodness at an earlier stage?
Hypotheses at (j, m): ⊤ ∉ R_{j+m}, R_{j+m} tight (every z ∈ R_{j+m} has h(z) ≤ j+m). 'g good' = g ≤ a(g) or the row-g descent
from ⊤ meets g. Candidates: g ∈ R_j, g ≠ ⊤, h(g) ≥ j (flag ontime: h(g) = j).
  vac — hypotheses only
  bg  — no candidate is good                              (SAT refutes BackGood at (j, m))
Flags: n1 (R_{j+1} non-tight), ontime, off (mutant: drop the tightness of R_{j+m}), offset (mutant: allow height j+m+1 in R_{j+m}).
Each SAT model is replayed in Python; the stage pattern (T = tight, n = not) of R_j … R_{j+m} is reported.
  python3 backgood.py MODE j m (sweep N MAX | closure K M SEED CNT) [flags]"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import lattices
from rstages import stages, a_of
FLG = {'n1', 'ontime', 'off', 'offset'}
MODE = sys.argv[1]; j = int(sys.argv[2]); m = int(sys.argv[3]); FL = {a for a in sys.argv[4:] if a in FLG}
args = [a for a in sys.argv[4:] if a not in FLG]
if MODE not in {'vac', 'bg'} or m < 1: raise SystemExit('usage')
K = j + m; C = collections.Counter(); INFO = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; top = L.top; NO = L.height + 1
    if L.height <= j: continue
    E = Enc(L, K); f = lambda a, b, u: E.v('f', a, b, u); r = lambda i, z: E.v('r', i, z); add = E.S.add_clause
    A = lambda x, g: E.v('A', x, g)
    add([-r(K, top)])
    if 'off' not in FL:
        bound = K + 1 if 'offset' in FL else K
        for z in range(n):
            if h[z] > bound: add([-r(K, z)])
    if 'n1' in FL: add([r(j + 1, z) for z in range(n) if h[z] > j + 1])
    def descvars(p):
        D = lambda i, z: E.v('DD', p, i, z)
        for z in range(n): add([D(0, z)] if z == top else [-D(0, z)])
        for i in range(NO):
            for z in range(n):
                lits = []
                for v in range(n): o = E.v('DDs', p, i, v, z); E.iff_and(o, [D(i, v), f(p, v, z)]); lits.append(o)
                E.iff_or(D(i + 1, z), lits)
        return D
    cand = [g for g in range(n) if g != top and (h[g] == j if 'ontime' in FL else h[g] >= j)]
    if MODE == 'bg':
        for g in cand:
            D = descvars(g)
            for i in range(NO + 1): add([-r(j, g), -D(i, g)])
            for v in range(n):
                if le[g][v]: add([-r(j, g), -A(g, v)])
    if E.S.solve():
        F = E.decode(); st = stages(L, F); inR = lambda x, i: st[x] is not None and st[x] <= i
        def desc(p):
            v = top; seen = []
            while v not in seen: seen.append(v); v = F[p][v]
            return seen
        tight = lambda i: all(h[z] <= i for z in range(n) if inR(z, i))
        ok = not inR(top, K)
        if 'off' not in FL: ok = ok and all(h[z] <= (K + 1 if 'offset' in FL else K) for z in range(n) if inR(z, K))
        if 'n1' in FL: ok = ok and not tight(j + 1)
        if MODE == 'bg': ok = ok and not any(inR(g, j) and (le[g][a_of(L, F, g)] or g in desc(g)) for g in cand)
        assert ok, 'SAT/Python mismatch'
        C['SAT'] += 1; INFO[''.join('T' if tight(i) else 'n' for i in range(j, K + 1))] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else: C['UNSAT'] += 1
    E.S.delete()
print(MODE, 'j', j, 'm', m, ' '.join(sorted(FL)), args, dict(C), 'smallest', best[0] if best else None, dict(INFO))
if best and MODE != 'vac':
    json.dump(best[1], open(f'backgood_{MODE}_j{j}m{m}{"".join("_" + x for x in sorted(FL))}_min{best[0]}.json', 'w'))
