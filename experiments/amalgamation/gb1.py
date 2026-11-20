"""GoodBase at j = 1 with R_2 tight only (log §34.3z²⁴⁸).
Hypotheses: R_2 tight, h(⊤) ≥ 4, a(⊥) = ⊥; d = the last nonzero element of the ⊥-descent from ⊤ (F(⊥, d) = ⊥, d ∈ R_1).
'good(p)': p ≤ a(p) or the row-p descent from ⊤ meets p.  SAT = a model with the stated failure.
  datom — h(d) = 1 and d is not good.
  dtwo  — h(d) = 2 and no atom p ≤ d is good.
  any   — no atom p ∈ R_1 is good.
  r1 / r3 — h(d) = 2 and some atom p ≤ d with F(p, d) ≤ p (r1) / F(p, d) ≤ d (r3) is not good.
  ex / exp — h(d) = 2 and no atom p ≤ d has F(p, d) ≤ d (ex) / F(p, d) ≤ p (exp).
  python3 gb1.py MODE (sweep N MAX | closure K M SEED CNT) [r1t]     (r1t: also R_1 tight)
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import lattices
from rstages import stages, a_of
MODE = sys.argv[1]; R1T = 'r1t' in sys.argv; args = [a for a in sys.argv[2:] if a != 'r1t']
C = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top
    if L.height < 4: continue
    E = Enc(L, 2); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
    A_ = lambda x, g: E.v('A', x, g); NO = L.height + 1
    for z in range(n):
        if h[z] > 2: add([-r(2, z)])
        if R1T and h[z] > 1: add([-r(1, z)])
    add([A_(bot, bot)])
    def descvars(p):
        D = lambda i, z: E.v('DD', p, i, z)
        for z in range(n): add([D(0, z)] if z == top else [-D(0, z)])
        for i in range(NO):
            for z in range(n):
                lits = []
                for v in range(n): o = E.v('DDs', p, i, v, z); E.iff_and(o, [D(i, v), f(p, v, z)]); lits.append(o)
                E.iff_or(D(i + 1, z), lits)
        return D
    D = descvars(bot)
    isd = {}
    for z in range(n):
        if z == bot: continue
        on = E.v('onB', z); E.iff_or(on, [D(i, z) for i in range(NO + 1)])
        isd[z] = E.v('isd', z); E.iff_and(isd[z], [on, f(bot, z, bot)])
    atoms = [p for p in range(n) if h[p] == 1]
    good = {}
    for p in atoms:
        P = descvars(p)
        good[p] = E.v('good', p); E.iff_or(good[p], [P(i, p) for i in range(NO + 1)] + [A_(p, g) for g in range(n) if le[p][g]])
    if MODE == 'datom':
        add([isd[p] for p in atoms])
        for p in atoms: add([-isd[p], -good[p]])
    elif MODE == 'dtwo':
        add([isd[z] for z in range(n) if h[z] == 2])
        for z in range(n):
            if h[z] == 2:
                for p in atoms:
                    if le[p][z]: add([-isd[z], -good[p]])
    elif MODE in ('pq', 'pq1'):                       # pq: atoms p ≠ q in R_1, q on the row-p descent from ⊤, q not good; pq1: and no atom of R_1 is good
        sel = []
        for p in atoms:
            for q in atoms:
                if p == q: continue
                s_ = E.v('pqs', p, q); sel.append(s_)
                add([-s_, r(1, p)]); add([-s_, r(1, q)]); add([-s_, -good[q]]); add([-s_] + [E.v('DD', p, i, q) for i in range(NO + 1)])
        add(sel)
        if MODE == 'pq1':
            for p in atoms: add([-r(1, p), -good[p]])
    elif MODE in ('L1', 'L2', 'L3', 'L4'):            # h(d) = 2; L1: F(d,d) ≰ d; L2: d not good in its own row; L3: no atom p < d with F(p,d) = p; L4: no atom p < d with d on the row-p descent
        add([isd[z] for z in range(n) if h[z] == 2])
        for z in range(n):
            if h[z] != 2: continue
            if MODE == 'L1':
                for w in range(n):
                    if le[w][z]: add([-isd[z], -f(z, z, w)])
            elif MODE == 'L2':
                Pz = descvars(z)
                for i in range(NO + 1): add([-isd[z], -Pz(i, z)])
                for g in range(n):
                    if le[z][g]: add([-isd[z], -A_(z, g)])
            else:
                for p in atoms:
                    if not le[p][z]: continue
                    if MODE == 'L3': add([-isd[z], -f(p, z, p)])
                    else:
                        for i in range(NO + 1): add([-isd[z], -E.v('DD', p, i, z)])
    elif MODE in ('r1', 'r3', 'ex', 'exp'):          # h(d) = 2; rules on F(p, d) for atoms p ≤ d
        fle = lambda x, y, t: E.v('fle', x, y, t)
        for x in atoms:
            for z in range(n):
                for t in range(n): E.iff_or(fle(x, z, t), [f(x, z, w) for w in range(n) if le[w][t]])
        add([isd[z] for z in range(n) if h[z] == 2])
        sel = []
        for z in range(n):
            if h[z] != 2: continue
            for p in atoms:
                if not le[p][z]: continue
                if MODE in ('r1', 'r3'):
                    s_ = E.v('rs', z, p); sel.append(s_)
                    add([-s_, isd[z]]); add([-s_, -good[p]]); add([-s_, fle(p, z, p if MODE == 'r1' else z)])
                else: add([-isd[z], -fle(p, z, z if MODE == 'ex' else p)])
        if sel: add(sel)
        else: add([])
    else:
        for p in atoms: add([-r(1, p), -good[p]])
    if E.S.solve():
        F = E.decode(); st = stages(L, F)
        def desc(p):
            v = top; seen = []
            while v not in seen: seen.append(v); v = F[p][v]
            return seen
        gd = lambda p: p in desc(p) or le[p][a_of(L, F, p)]
        bd = desc(bot); d = next(x for x in bd if x != bot and F[bot][x] == bot)
        ok = a_of(L, F, bot) == bot and all(h[z] <= 2 for z in range(n) if st[z] is not None and st[z] <= 2)
        if MODE == 'datom': ok = ok and h[d] == 1 and not gd(d)
        elif MODE == 'dtwo': ok = ok and h[d] == 2 and not any(gd(p) for p in atoms if le[p][d])
        elif MODE == 'pq': ok = ok and any(p != q and st[p] is not None and st[p] <= 1 and st[q] is not None and st[q] <= 1 and q in desc(p) and not gd(q) for p in atoms for q in atoms)
        elif MODE == 'pq1': ok = ok and any(p != q and q in desc(p) for p in atoms for q in atoms if st[p] is not None and st[p] <= 1 and st[q] is not None and st[q] <= 1) and not any(gd(p) for p in atoms if st[p] is not None and st[p] <= 1)
        elif MODE == 'L1': ok = ok and h[d] == 2 and not le[F[d][d]][d]
        elif MODE == 'L2': ok = ok and h[d] == 2 and not (d in desc(d) or le[d][a_of(L, F, d)])
        elif MODE == 'L3': ok = ok and h[d] == 2 and not any(le[p][d] and F[p][d] == p for p in atoms)
        elif MODE == 'L4': ok = ok and h[d] == 2 and not any(le[p][d] and d in desc(p) for p in atoms)
        elif MODE == 'r1': ok = ok and h[d] == 2 and any(le[p][d] and le[F[p][d]][p] and not gd(p) for p in atoms)
        elif MODE == 'r3': ok = ok and h[d] == 2 and any(le[p][d] and le[F[p][d]][d] and not gd(p) for p in atoms)
        elif MODE == 'ex': ok = ok and h[d] == 2 and not any(le[p][d] and le[F[p][d]][d] for p in atoms)
        elif MODE == 'exp': ok = ok and h[d] == 2 and not any(le[p][d] and le[F[p][d]][p] for p in atoms)
        else: ok = ok and not any(gd(p) for p in atoms if st[p] is not None and st[p] <= 1)
        assert ok, 'SAT/Python mismatch'
        C['SAT'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else: C['UNSAT'] += 1
    E.S.delete()
print(MODE, 'r1t' if R1T else '', dict(C), 'smallest', best[0] if best else None)
if best: json.dump(best[1], open(f'gb1_{MODE}{"_r1t" if R1T else ""}_min{best[0]}.json', 'w'))
