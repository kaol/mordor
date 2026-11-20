"""Response coverage for the fibre covers of the ⊥-descent atom (log §34.3z²³⁶), rank(m) = 2.

Hypotheses: F monotone, m ∈ R_2 \\ R_1, h(m) = 2, R_1 tight, w = F(m, y*) ∥ m, and R_2 tight unless 'not2'.
V* = {v : c* ⋖ v, h(v) = 2, F(⊥, v) = c*, m ≰ v}, with c* the atom of the ⊥-descent from w.  'Gap' means F(c*, v) ∥ v.
Modes (SAT = a model with the stated property; every model replayed in Python):
  nonempty — V* = ∅ is possible?                 allgap — V* ≠ ∅ and every v ∈ V* a gap?
  rcfail   — V* ≠ ∅, all gaps, and some u ∈ V* lies below no response F(c*, v), v ∈ V*?
  xrcfail  — the same with responses over the multi-atom relation (see out file): u ≤ F(d, v') for a pair (d, v') of any
             atom d ∈ R_1 and v' ⋗ d, F(⊥, v') = d, m ≰ v'.
  python3 rc_test.py MODE (sweep N MAX | closure K M SEED CNT) [not2]
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from rstages import stages, a_of
MODE = sys.argv[1]; NOT2 = 'not2' in sys.argv; ATS = 'acstar' in sys.argv; ATA = 'aatoms' in sys.argv; BT = 'broute' in sys.argv; CLE = 'cle' in sys.argv; CNLE = 'cnle' in sys.argv; START = next((a[6:] for a in sys.argv if a.startswith('start=')), 'w'); NOWPAR = 'nowpar' in sys.argv; NOMEM = 'nomem' in sys.argv; NOMV = 'nomv' in sys.argv   # start=w|ystar|top: start of the ⊥-descent
args = [a for a in sys.argv[2:] if a not in ('not2', 'acstar', 'aatoms', 'broute', 'cle', 'cnle') and not a.startswith('start=') and a not in ('nowpar', 'nomem', 'nomv')]   # nowpar: drop w ∥ m; nomem: drop m ∈ R_2 \\ R_1; nomv: drop m ≰ v in V*   # cle / cnle: restrict to c* ≤ m / c* ≰ m   # acstar: h(a(c*)) ≤ 2 only; aatoms: h(a(d)) ≤ 2 for atoms d ∈ R_1
C = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top; jn = L.join
    for m in range(n):
        if h[m] != 2 or L.height <= 2: continue
        E = Enc(L, 3); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
        if not NOMEM: add([r(2, m)]); add([-r(1, m)])
        for z in range(n):
            if h[z] > 1: add([-r(1, z)])
            if h[z] > 2 and not NOT2: add([-r(2, z)])
        U = lambda i, z: E.v('U', i, z); NO = L.height + 1
        for z in range(n): add([U(0, z)] if z == top else [-U(0, z)])
        for i in range(NO - 1):
            for z in range(n):
                lits = []
                for v in range(n):
                    for g in range(n):
                        if jn[m][g] == z: o = E.v('Ust', i, v, g); E.iff_and(o, [U(i, v), f(m, v, g)]); lits.append(o)
                E.iff_or(U(i + 1, z), lits)
        for z in range(n):
            for g in range(n):
                if (le[g][m] or le[m][g]) and not NOWPAR: add([-U(NO - 1, z), -f(m, z, g)])
        D = lambda i, z: E.v('D', i, z)
        for z in range(n):
            lits = []
            if START == 'w':
                for yv in range(n): o = E.v('D0', yv, z); E.iff_and(o, [U(NO - 1, yv), f(m, yv, z)]); lits.append(o)
                E.iff_or(D(0, z), lits)
            elif START == 'ystar': E.iff_or(D(0, z), [U(NO - 1, z)])
            else: add([D(0, z)] if z == top else [-D(0, z)])
        for i in range(NO):
            for z in range(n):
                lits = []
                for v in range(n): o = E.v('Ds', i, v, z); E.iff_and(o, [D(i, v), f(bot, v, z)]); lits.append(o)
                E.iff_or(D(i + 1, z), lits)
        atoms = [c for c in range(n) if h[c] == 1]
        At = {c: E.v('datom', c) for c in atoms}
        for c in atoms: E.iff_or(At[c], [D(i, c) for i in range(NO + 1)])
        add(list(At.values()))
        cov = {c: [v for v in L.covers_up[c] if h[v] == 2 and (NOMV or not le[m][v])] for c in atoms}
        inV = {}
        for c in atoms:
            for v in cov[c]: o = E.v('inV', c, v); E.iff_and(o, [At[c], f(bot, v, c)]); inV[(c, v)] = o
        ule = lambda d, v, u: E.v('ule', d, v, u)
        def ulit(d, v, u):
            k_ = ('ule', d, v, u)
            if k_ not in E.vars: o = E.v(*k_); E.iff_or(o, [f(d, v, t) for t in range(n) if le[u][t]])
            return E.vars[k_]
        A_ = lambda x, g: E.v('A', x, g)
        for c in atoms:
            for g in range(n):
                if h[g] > 2:
                    if ATS: add([-At[c], -A_(c, g)])
                    if ATA: add([-r(1, c), -A_(c, g)])
        if BT:                                        # b-route tightness: b(g) ∈ R_1 ⟹ h(g) ≤ 2
            for g in range(n):
                if h[g] > 2:
                    for x in range(n): add([-E.v('B', g, x), -r(1, x)])
        for c in atoms:
            if CLE and not le[c][m]: add([-At[c]])
            if CNLE and le[c][m]: add([-At[c]])
        if MODE == 'vley':                             # some v ∈ V* with v ≰ y*
            add([E.v('vsel', c, v) for (c, v) in inV])
            for (c, v), o in inV.items():
                add([-E.v('vsel', c, v), o])
                for z in range(n):
                    if le[v][z]: add([-E.v('vsel', c, v), -U(NO - 1, z)])
        elif MODE in ('acfib', 'abotbot'):                # 'abotbot': a(⊥) = ⊥ and DescPre2 fails; 'acfib': a(⊥) = ⊥ and a(c*) is not a fibre cover of c*
            add([A_(bot, bot)])
            if MODE == 'abotbot':
                for (c, v), o in inV.items(): add([-o, -fle(c, v, v)])
            else:
                for c in atoms:
                    for g in range(n):
                        if le[c][g] and g != c: add([-At[c], -A_(c, g), -f(bot, g, c)])
        elif MODE in ('imgatom', 'imgatom_any'):          # m-free: some atom c ∈ R_1 with c = F(⊥, p) for some p > c ('imgatom'; 'imgatom_any': any atom c ∈ R_1 with V_c ≠ ∅) and no pre-fixed fibre cover
            sel = []
            for c in atoms:
                vs = [v for v in L.covers_up[c] if h[v] == 2]
                s_ = E.v('iasel', c); sel.append(s_); add([-s_, r(1, c)])
                if MODE == 'imgatom': add([-s_] + [f(bot, pv, c) for pv in range(n) if le[c][pv] and pv != c])
                else: add([-s_] + [f(bot, v, c) for v in vs])
                for v in vs: add([-s_, -f(bot, v, c), -fle(c, v, v)])
            add(sel)
        elif MODE == 'peratomw':                         # some atom c ∈ R_1, c ≰ m, c = F(⊥, p) for some p ≤ w with c < p, and no pre-fixed v ∈ V_c
            Ws = {}
            for wv in range(n):
                lits = []
                for yv in range(n): o = E.v('Wsel0', yv, wv); E.iff_and(o, [U(NO - 1, yv), f(m, yv, wv)]); lits.append(o)
                Ws[wv] = E.v('Wsel', wv); E.iff_or(Ws[wv], lits)
            sel = []
            for c in atoms:
                if le[c][m]: continue
                vs = [v for v in L.covers_up[c] if h[v] == 2 and not le[m][v]]
                img = []
                for wv in range(n):
                    for pv in range(n):
                        if le[c][pv] and pv != c and le[pv][wv]: o = E.v('img', c, wv, pv); E.iff_and(o, [Ws[wv], f(bot, pv, c)]); img.append(o)
                if not img: continue
                s_ = E.v('pwsel', c); sel.append(s_); add([-s_, r(1, c)]); add([-s_] + img)
                for v in vs: add([-s_, -f(bot, v, c), -fle(c, v, v)])
            add(sel)
        elif MODE in ('peratom', 'peratom_le'):          # some atom c ∈ R_1 with c ≰ m ('peratom') / c ≤ m ('peratom_le'), V_c ≠ ∅, no pre-fixed v ∈ V_c
            sel = []
            for c in atoms:
                if le[c][m] != (MODE == 'peratom_le'): continue
                vs = [v for v in L.covers_up[c] if h[v] == 2 and not le[m][v]]
                if not vs: continue
                s_ = E.v('pasel', c); sel.append(s_); add([-s_, r(1, c)])
                add([-s_] + [f(bot, v, c) for v in vs])
                for v in vs: add([-s_, -f(bot, v, c), -fle(c, v, v)])
            add(sel)
        elif MODE in ('residual', 'residual_post'):    # no atom c ∈ R_1 with c ≤ m, c < w whose row stays above c on (c, w] ('residual') / with c ≤ F(⊥, c) ('residual_post')
            Ws = {}
            for wv in range(n):
                lits = []
                for yv in range(n): o = E.v('Wsel0', yv, wv); E.iff_and(o, [U(NO - 1, yv), f(m, yv, wv)]); lits.append(o)
                Ws[wv] = E.v('Wsel', wv); E.iff_or(Ws[wv], lits)
            for c in atoms:
                if not le[c][m]: continue
                for wv in range(n):
                    if not (le[c][wv] and c != wv): continue
                    if MODE == 'residual_post': add([-Ws[wv], -r(1, c), -ulit(bot, c, c)]); continue
                    fl = []
                    for u in range(n):
                        if le[c][u] and u != c and le[u][wv]:
                            o = E.v('hfail', c, u); E.iff_and(o, [fle(c, u, u), -ulit(c, u, c)]); fl.append(o)
                    add([-Ws[wv], -r(1, c)] + fl)
        elif MODE == 'descpre2yfail':                  # no v ∈ V* ∩ ↓y* with F(c*, v) ≤ v
            for (c, v), o in inV.items():
                for z in range(n):
                    if le[v][z]: add([-o, -U(NO - 1, z), -fle(c, v, v)])
        elif MODE == 'descpre2fail':                     # no v ∈ V* with F(c*, v) ≤ v (DescPre2 violated)
            for (c, v), o in inV.items(): add([-o, -fle(c, v, v)])
        elif MODE == 'nonempty':
            for o in inV.values(): add([-o])
        else:
            add(list(inV.values()))                                   # V* ≠ ∅
            for (c, v), o in inV.items(): add([-o, -fle(c, v, v)]); add([-o, -yle(c, v)])   # all gaps
            if MODE == 'ercfail':                     # Cl = least set ⊇ V* closed under u ≤ F(c*, v), u a height-2 cover of c*; some u ∈ Cl below no response of Cl
                NC = max(len(L.covers_up[c]) for c in atoms) + 1
                Cl = lambda i, c, u: E.v('Cl', i, c, u)
                for c in atoms:
                    cv2 = [u for u in L.covers_up[c] if h[u] == 2]
                    for u in cv2:
                        E.iff_or(Cl(0, c, u), [inV[(c, u)]] if (c, u) in inV else [])
                        if (c, u) not in inV: add([-Cl(0, c, u)])
                    for i in range(NC):
                        for u in cv2:
                            lits = [Cl(i, c, u)]
                            for v in cv2: o = E.v('Clst', i, c, u, v); E.iff_and(o, [Cl(i, c, v), ulit(c, v, u)]); lits.append(o)
                            E.iff_or(Cl(i + 1, c, u), lits)
                sel = []
                for c in atoms:
                    cv2 = [u for u in L.covers_up[c] if h[u] == 2]
                    for u in cv2:
                        s_ = E.v('esel', c, u); sel.append(s_); add([-s_, At[c]]); add([-s_, Cl(NC, c, u)])
                        for v in cv2: add([-s_, -Cl(NC, c, v), -ulit(c, v, u)])
                add(sel)
            if MODE in ('rcfail', 'xrcfail'):
                sel = []
                for (c, u), o in inV.items():
                    s_ = E.v('rsel', c, u); sel.append(s_); add([-s_, o])
                    if MODE == 'rcfail':
                        for v in cov[c]: add([-s_, -inV[(c, v)], -ulit(c, v, u)])
                    else:
                        for d in atoms:
                            for v2 in cov[d]:
                                o2 = E.v('inW', d, v2)
                                if ('inW', d, v2) not in E.vars or True: E.iff_and(o2, [r(1, d), f(bot, v2, d)])
                                add([-s_, -o2, -ulit(d, v2, u)])
                add(sel)
        if E.S.solve():
            F = E.decode(); st = stages(L, F)
            u_ = top
            while True:
                v_ = jn[m][F[m][u_]]
                if v_ == u_: break
                u_ = v_
            w = F[m][u_]; v_ = {'w': w, 'ystar': u_, 'top': top}[START]; seen = set(); cs = []
            while v_ not in seen:
                seen.add(v_)
                if h[v_] == 1: cs.append(v_)
                v_ = F[bot][v_]
            assert len(cs) == 1, cs
            c = cs[0]; Vs = [v for v in cov[c] if F[bot][v] == c]
            assert NOMEM or (st[m] is not None and st[m] <= 2 and st[m] > 1)
            gap = lambda v: not le[F[c][v]][v] and not le[v][F[c][v]]
            inR1 = lambda x: st[x] is not None and st[x] <= 1
            W = [(d, v2) for d in atoms if inR1(d) for v2 in cov[d] if F[bot][v2] == d]
            cv2 = [u for u in L.covers_up[c] if h[u] == 2]
            Clp = set(Vs); ch = True
            while ch:
                ch = False
                for v in list(Clp):
                    for u in cv2:
                        if u not in Clp and le[u][F[c][v]]: Clp.add(u); ch = True
            above = lambda c: all(le[c][F[c][uu]] for uu in range(n) if le[c][uu] and uu != c and le[uu][w] and le[F[c][uu]][uu])
            cand = [c for c in atoms if le[c][m] and le[c][w] and c != w and inR1(c)]
            def pa(le_flag):
                for c2 in atoms:
                    if le[c2][m] != le_flag or not inR1(c2): continue
                    vs = [v for v in L.covers_up[c2] if h[v] == 2 and not le[m][v] and F[bot][v] == c2]
                    if vs and not any(le[F[c2][v]][v] for v in vs): return True
                return False
            def paw():
                for c2 in atoms:
                    if le[c2][m] or not inR1(c2): continue
                    if not any(le[c2][pv] and pv != c2 and le[pv][w] and F[bot][pv] == c2 for pv in range(n)): continue
                    vs = [v for v in L.covers_up[c2] if h[v] == 2 and not le[m][v] and F[bot][v] == c2]
                    if not any(le[F[c2][v]][v] for v in vs): return True
                return False
            def ia(any_):
                for c2 in atoms:
                    if not inR1(c2): continue
                    vs = [v for v in L.covers_up[c2] if h[v] == 2 and F[bot][v] == c2]
                    if any_ and not vs: continue
                    if not any_ and not any(le[c2][pv] and pv != c2 and F[bot][pv] == c2 for pv in range(n)): continue
                    if not any(le[F[c2][v]][v] for v in vs): return True
                return False
            ac = a_of(L, F, c)
            ok = {'acfib': a_of(L, F, bot) == bot and not (le[c][ac] and ac != c and F[bot][ac] == c), 'abotbot': a_of(L, F, bot) == bot and not any(le[F[c][v]][v] for v in Vs), 'imgatom': ia(False), 'imgatom_any': ia(True), 'peratomw': paw(), 'peratom': pa(False), 'peratom_le': pa(True), 'residual': not any(above(c) for c in cand), 'residual_post': not any(le[c][F[bot][c]] for c in cand), 'descpre2yfail': not any(le[F[c][v]][v] and le[v][u_] for v in Vs), 'vley': any(not le[v][u_] for v in Vs), 'descpre2fail': not any(le[F[c][v]][v] for v in Vs), 'ercfail': bool(Vs) and all(gap(v) for v in Vs) and any(not any(le[u][F[c][v]] for v in Clp) for u in Clp), 'nonempty': not Vs, 'allgap': bool(Vs) and all(gap(v) for v in Vs),
                  'rcfail': bool(Vs) and all(gap(v) for v in Vs) and any(not any(le[u][F[c][v]] for v in Vs) for u in Vs),
                  'xrcfail': bool(Vs) and all(gap(v) for v in Vs) and any(not any(le[u][F[d][v2]] for d, v2 in W) for u in Vs)}[MODE]
            assert ok, 'SAT/Python mismatch'
            C['SAT'] += 1
            if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F, m=m))
        else: C['UNSAT'] += 1
        E.S.delete()
print(MODE, 'not2' if NOT2 else '', 'acstar' if ATS else '', 'aatoms' if ATA else '', 'broute' if BT else '', 'cle' if CLE else '', 'cnle' if CNLE else '', 'start=' + START, 'nowpar' if NOWPAR else '', 'nomem' if NOMEM else '', 'nomv' if NOMV else '', dict(C), 'smallest', best[0] if best else None)
if best: json.dump(best[1], open(f'rc_{MODE}{"_not2" if NOT2 else ""}{"_acstar" if ATS else ""}{"_aatoms" if ATA else ""}{"_broute" if BT else ""}{"_cle" if CLE else ""}{"_cnle" if CNLE else ""}{"" if START == "w" else "_" + START}_min{best[0]}.json', 'w'))
