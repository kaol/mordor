"""The column ascent below a pre-fixed column (log §34.3z²⁵³).
Hypotheses: c ∈ R_k with h(c) = k, F(c, c) ≤ c (c pre-fixed in its own column), b(c) ∉ R_{k−1} ('pure A-route'); no tightness
unless 'tK' (R_k tight).  The column-c ascent from ⊥ is e_0 = ⊥, e_{i+1} = F(e_i, c); it rises to b(c) ≤ c.
  asc1 — b(c) ≠ c
  ascS — some ascent element strictly below c lies outside R_{k−1}
  asc2 — the ascent enters c from an x ∉ R_{k−1} or of height ≠ k − 1
  vac  — hypotheses only
  python3 colasc.py MODE k (sweep N MAX | closure K M SEED CNT) [tK]"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import lattices
from rstages import stages, b_of
MODE = sys.argv[1]; k = int(sys.argv[2]); TK = 'tK' in sys.argv; args = [a for a in sys.argv[3:] if a != 'tK']
C = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); NO = L.height + 1
    for c in range(n):
        if h[c] != k: continue
        E = Enc(L, k); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
        add([r(k, c)]); add([f(c, c, v) for v in range(n) if le[v][c]])
        for g in range(n): add([-E.v('B', c, g), -r(k - 1, g)])
        if TK:
            for z in range(n):
                if h[z] > k: add([-r(k, z)])
        Au = lambda i, z: E.v('Asc', i, z)
        for z in range(n): add([Au(0, z)] if z == bot else [-Au(0, z)])
        for i in range(NO):
            for z in range(n):
                ls = []
                for v in range(n): o = E.v('Ascs', i, v, z); E.iff_and(o, [Au(i, v), f(v, c, z)]); ls.append(o)
                E.iff_or(Au(i + 1, z), ls)
        if MODE == 'asc1': add([-E.v('B', c, c)])
        elif MODE in ('ascS', 'asc2'):
            sel = []
            for i in range(NO + 1):
                for x in range(n):
                    if x == c or not le[x][c]: continue
                    o = E.v('sx', i, x); add([-o, Au(i, x)])
                    if MODE == 'ascS': add([-o, -r(k - 1, x)])
                    else:
                        add([-o, f(x, c, c)])
                        if h[x] == k - 1: add([-o, -r(k - 1, x)])
                    sel.append(o)
            add(sel)
        if E.S.solve():
            F = E.decode(); st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j
            bc = b_of(L, F, c); v = bot; seq = [v]
            while F[v][c] != v: v = F[v][c]; seq.append(v)
            ok = inR(c, k) and le[F[c][c]][c] and not inR(bc, k - 1)
            if MODE == 'asc1': ok = ok and bc != c
            elif MODE == 'ascS': ok = ok and any(x != c and not inR(x, k - 1) for x in seq)
            elif MODE == 'asc2': ok = ok and c in seq and not (h[seq[seq.index(c) - 1]] == k - 1 and inR(seq[seq.index(c) - 1], k - 1))
            assert ok, 'SAT/Python mismatch'
            C['SAT'] += 1
            if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F, c=c))
        else: C['UNSAT'] += 1
        E.S.delete()
print(MODE, 'k', k, 'tK' if TK else '', dict(C), 'smallest', best[0] if best else None)
if best and MODE != 'vac': json.dump(best[1], open(f'colasc_{MODE}_k{k}{"_tK" if TK else ""}_min{best[0]}.json', 'w'))
