"""Level-1 base under R_2 tightness only (log §34.3z²⁴⁷).
Hypotheses: R_2 tight, height(L) ≥ 3 [+ 'r3': R_3 tight].
  noatom  — the ⊥-descent from ⊤ passes through no atom (SAT = such a model).
  python3 lv_desc.py MODE (sweep N MAX | closure K M SEED CNT) [r3]
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import lattices
from rstages import stages, a_of
MODE = sys.argv[1]; R3 = 'r3' in sys.argv; args = [a for a in sys.argv[2:] if a != 'r3']
C = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top
    if L.height < 3: continue
    E = Enc(L, 3); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
    A_ = lambda x, g: E.v('A', x, g); NO = L.height + 1
    for z in range(n):
        if h[z] > 2: add([-r(2, z)])
        if R3 and h[z] > 3: add([-r(3, z)])
    def descvars(p, tag):
        D = lambda i, z: E.v(tag, p, i, z)
        for z in range(n): add([D(0, z)] if z == top else [-D(0, z)])
        for i in range(NO):
            for z in range(n):
                lits = []
                for v in range(n): o = E.v(tag + 's', p, i, v, z); E.iff_and(o, [D(i, v), f(p, v, z)]); lits.append(o)
                E.iff_or(D(i + 1, z), lits)
        return D
    D = descvars(bot, 'D')
    atoms = [c for c in range(n) if h[c] == 1]
    if MODE == 'noatom':
        for c in atoms:
            for i in range(NO + 1): add([-D(i, c)])
    else: raise SystemExit('unknown mode')
    if E.S.solve():
        F = E.decode(); st = stages(L, F)
        def desc(p):
            v = top; seen = []
            while v not in seen: seen.append(v); v = F[p][v]
            return seen
        bd = desc(bot); cs = [x for x in bd if h[x] == 1]
        ok = not cs
        assert ok, 'SAT/Python mismatch'
        C['SAT'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else: C['UNSAT'] += 1
    E.S.delete()
print(MODE, 'r3' if R3 else '', dict(C), 'smallest', best[0] if best else None)
if best: json.dump(best[1], open(f'lvdesc_{MODE}{"_r3" if R3 else ""}_min{best[0]}.json', 'w'))
