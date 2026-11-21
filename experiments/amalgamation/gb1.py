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
    if not MODE.endswith('n'): add([A_(bot, bot)])
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
    elif MODE in ('D1', 'D2', 'D3', 'D3all'):                          # h(d) = 2; z = a drop column of the row-d descent (z ≥ d, F(d, z) ≱ d);
        add([isd[z] for z in range(n) if h[z] == 2])     # D1: some atom q < d with q ≤ F(⊥, z) is not good; D2: no atom q < d lies below F(⊥, z)
        sel = []
        for e in range(n):
            if h[e] != 2: continue
            W = descvars(e)
            for z in range(n):
                if not le[e][z]: continue
                for v in range(n):
                    qs = [q for q in atoms if le[q][e] and le[q][v]]
                    if MODE in ('D3', 'D3all'):                  # t = F(d, z) not post-fixed in row q [D3all: drop z need not be ... (same)]
                        for q in qs:
                            for t in range(n):
                                for w in range(n):
                                    if le[t][w]: continue
                                    s_ = E.v('d3', e, z, v, q, t, w); sel.append(s_)
                                    add([-s_, isd[e]]); add([-s_, f(bot, z, v)]); add([-s_, f(e, z, t)]); add([-s_, f(q, t, w)])
                                    add([-s_] + [W(i, z) for i in range(NO + 1)])
                                    for w2 in range(n):
                                        if le[e][w2]: add([-s_, -f(e, z, w2)])
                    elif MODE == 'D1':
                        for q in qs:
                            s_ = E.v('d1', e, z, v, q); sel.append(s_)
                            add([-s_, isd[e]]); add([-s_, f(bot, z, v)]); add([-s_, -good[q]]); add([-s_] + [W(i, z) for i in range(NO + 1)])
                            for w in range(n):
                                if le[e][w]: add([-s_, -f(e, z, w)])
                    else:
                        if qs: continue
                        s_ = E.v('d2', e, z, v); sel.append(s_)
                        add([-s_, isd[e]]); add([-s_, f(bot, z, v)]); add([-s_] + [W(i, z) for i in range(NO + 1)])
                        for w in range(n):
                            if le[e][w]: add([-s_, -f(e, z, w)])
        add(sel)
    elif MODE in ('T1', 'T1n'):                        # some e ∈ R_1 of height 2 with no good atom below it
        sel = []
        for e in range(n):
            if h[e] != 2: continue
            s_ = E.v('t1', e); sel.append(s_); add([-s_, r(1, e)])
            for q in atoms:
                if le[q][e]: add([-s_, -good[q]])
        add(sel)
    elif MODE in ('C12', 'C1', 'C12n', 'C1n'):         # no atom p ∈ R_1 with p ≤ F(p, p), and [C12] the ⊥-descent atom (if any) is not good
        for p in atoms:
            for v in range(n):
                if le[p][v]: add([-r(1, p), -f(p, p, v)])
            if MODE.startswith('C12'):
                for i in range(NO + 1): add([-E.v('DD', bot, i, p), -good[p]])
    elif MODE in ('one', 'one2', 'hard'):                                # exactly one atom of R_1 good, R_1 non-tight (for inspection)
        add([r(1, z) for z in range(n) if h[z] > 1])
        gs = []
        for p in atoms: o = E.v('g1', p); E.iff_and(o, [r(1, p), good[p]]); gs.append(o)
        add(gs)
        for i in range(len(gs)):
            for j in range(i + 1, len(gs)): add([-gs[i], -gs[j]])
        if MODE == 'hard':                                # no self-fixed atom of R_1 (the unique good atom meets its own descent)
            for p in atoms:
                for v in range(n):
                    if le[p][v]: add([-r(1, p), -f(p, p, v)])
        if MODE in ('one2', 'hard'):                                # and the ⊥-descent from ⊤ misses every atom
            for p in atoms:
                for i in range(NO + 1): add([-E.v('DD', bot, i, p)])
    elif MODE in ('Q3', 'Q3n', 'Q4', 'Q4n'):          # an atom p ∈ R_1 with drop column z (z ≥ p on the row-p descent, F(p, z) ≱ p) and no good atom of R_1 below F(⊥, z) [Q3] / below F(p, z) [Q4]
        sel = []
        for p in atoms:
            for z in range(n):
                if not le[p][z]: continue
                s_ = E.v('q3', p, z); sel.append(s_); add([-s_, r(1, p)]); add([-s_] + [E.v('DD', p, i, z) for i in range(NO + 1)])
                for w in range(n):
                    if le[p][w]: add([-s_, -f(p, z, w)])
                add([-s_, -f(bot, z, bot)])                      # F(⊥, z) ≠ ⊥
                for v in range(n):
                    for q in atoms:
                        if le[q][v]: add([-s_, -f(bot if MODE.startswith('Q3') else p, z, v), -r(1, q), -good[q]])
        add(sel)
    elif MODE in ('Q1', 'Q2', 'Q1n', 'Q2n'):          # some z with v = F(⊥, z) ≠ ⊥ (Q2: and v ≤ z) and no good atom q ∈ R_1 below v; 'n': without a(⊥) = ⊥
        sel = []
        for z in range(n):
            for v in range(n):
                if v == bot or (MODE.startswith('Q2') and not le[v][z]): continue
                s_ = E.v('qs', z, v); sel.append(s_); add([-s_, f(bot, z, v)])
                for q in atoms:
                    if le[q][v]: add([-s_, -r(1, q), -good[q]])
        add(sel)
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
        bd = desc(bot); d = next((x for x in bd if x != bot and F[bot][x] == bot), None)
        ok = (MODE.endswith('n') or a_of(L, F, bot) == bot) and all(h[z] <= 2 for z in range(n) if st[z] is not None and st[z] <= 2)
        if MODE == 'datom': ok = ok and h[d] == 1 and not gd(d)
        elif MODE == 'dtwo': ok = ok and h[d] == 2 and not any(gd(p) for p in atoms if le[p][d])
        elif MODE in ('D1', 'D2', 'D3', 'D3all'):
            dd = desc(d); drops = [z for z in dd if le[d][z] and not le[d][F[d][z]]]
            if MODE == 'D1': ok = ok and h[d] == 2 and any(le[q][d] and le[q][F[bot][z]] and not gd(q) for z in drops for q in atoms)
            elif MODE.startswith('D3'): ok = ok and h[d] == 2 and any(le[q][d] and le[q][F[bot][z]] and not le[F[d][z]][F[q][F[d][z]]] for z in drops for q in atoms)
            else: ok = ok and h[d] == 2 and any(not any(le[q][d] and le[q][F[bot][z]] for q in atoms) for z in drops)
        elif MODE.startswith('T1'):
            ok = ok and any(h[e] == 2 and st[e] is not None and st[e] <= 1 and not any(le[q][e] and gd(q) for q in atoms) for e in range(n))
        elif MODE.startswith('C1'):
            inR1 = lambda q: st[q] is not None and st[q] <= 1
            ok = ok and not any(inR1(p) and le[p][F[p][p]] for p in atoms) and (not MODE.startswith('C12') or not any(p in bd and gd(p) for p in atoms))
        elif MODE in ('one', 'one2', 'hard'): ok = ok and (MODE != 'hard' or not any(st[p] is not None and st[p] <= 1 and le[p][F[p][p]] for p in atoms)) and sum(1 for p in atoms if st[p] is not None and st[p] <= 1 and gd(p)) == 1
        elif MODE[:2] in ('Q3', 'Q4'):
            inR1 = lambda q: st[q] is not None and st[q] <= 1
            ok = ok and any(inR1(p) and le[p][z] and z in desc(p) and not le[p][F[p][z]] and F[bot][z] != bot and not any(le[q][F[bot if MODE[1] == '3' else p][z]] and inR1(q) and gd(q) for q in atoms) for p in atoms for z in range(n))
        elif MODE.startswith('Q'):
            inR1 = lambda q: st[q] is not None and st[q] <= 1
            ok = ok and any(F[bot][z] != bot and (MODE[1] == '1' or le[F[bot][z]][z]) and not any(le[q][F[bot][z]] and inR1(q) and gd(q) for q in atoms) for z in range(n))
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
