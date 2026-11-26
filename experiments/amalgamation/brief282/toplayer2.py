"""amr_run14 briefer -- TOP-LAYER probe, second statement set (exact).  World, branches, quantifier and replay exactly as in
toplayer.py (W and Rep of amr_run13/ctlA/w0lean.py).  Every column: SAT iff the named statement FAILS for some F on this lattice
and branch; vac: SAT iff the branch has a model.  Every SAT model is replayed from the definitions before it is counted.
  TopCell, NMGood, M:TopCellAll   as in toplayer.py
  TopCert       some m in M2 exits with c(m) <= m                                   [run-13 A's TopCert; fails on g by design]
  GoodFix       every good atom of Z is a fixed point of mu (row q exits to q)       [ladder: then GoodAtom1 <=> Cert1]
  M:GoodA       MUTANT of GoodFix: every good atom q of Z has q <= a(q)
  OneGood       at most one atom of Z is good
  M:OneExitAtom MUTANT of OneGood: at most one atom of Z exits
  MaxIdx2       some m in M2 of maximal landing index (among M2) exits with c(m) <= m
  M:MinIdx2     MUTANT of MaxIdx2: the same with minimal landing index
  python3 toplayer2.py (file PATH... | tall K M SEED CNT | closure K M SEED CNT)"""
import sys, collections, time, json, os
sys.path.insert(0, '/home/user/mordor/experiments/separation'); sys.path.insert(0, '/home/user/mordor/experiments/amalgamation')
sys.path.insert(0, '/tmp/claude-0/-home-user/3b6fdd2c-c95c-5c07-b47c-6ae28c687a4c/scratchpad/amr_run13/ctlA')
from w0lean import W, Rep, BR
from tight_probe import lattices
from rstages import a_of
OUT = os.path.dirname(os.path.abspath(__file__))

def queries(s):
    L = s.L; le = L.le; bot = L.bot; R = s.R; add = s.S.add_clause; Q = {}
    tc = {}
    for m in s.h2:
        ls = []
        for p in s.h2:
            q = L.meet[m][p]
            if p == m or L.rank[q] != 1: continue
            cell = s.OR(('cell', q, p), [s.f(q, p, w) for w in range(L.n) if le[q][w]])
            ls.append(s.AND(('tcp', m, p), [s.land[m, p], cell]))
        tc[m] = s.AND(('tc', m), [s.Z(m), s.OR(('tc1', m), ls)])
    a = s.v('act', 'TopCell'); Q['TopCell'] = a
    for m in s.h2: add([-a, -tc[m]])
    a = s.v('act', 'NMGood'); Q['NMGood'] = a
    for q in s.atoms:
        for m in s.h2:
            if le[q][m]: add([-a, -s.Z(m), -s.good[q]])
    a = s.v('act', 'TopCert'); Q['TopCert'] = a
    for m in s.h2:
        for c in s.atoms:
            if le[c][m]: add([-a, -s.Z(m), -s.ext[m, c]])
    a = s.v('act', 'M:TopCellAll'); Q['M:TopCellAll'] = a; sel = []
    for m in s.h2:
        o = s.v('tca', m); sel.append(o); add([-o, s.Z(m)]); add([-o, -tc[m]])
    add([-a] + sel)
    # GoodFix: every good atom of Z is a fixed point of mu (exits to itself).  SAT = some good atom of Z is not mu-fixed.
    # M:GoodA (mutant): every good atom of Z has q <= a(q).                    SAT = some good atom of Z has q not<= a(q).
    NO = s.NO
    aq = {q: s.OR(('aq', q), [s.it(q, NO, v) for v in range(L.n) if le[q][v]]) for q in s.atoms}
    for name, prop in (('GoodFix', lambda q: s.ext[q, q]), ('M:GoodA', lambda q: aq[q])):
        a = s.v('act', name); Q[name] = a; sel = []
        for q in s.atoms:
            o = s.v('sel', name, q); sel.append(o); add([-o, s.Z(q)]); add([-o, s.good[q]]); add([-o, -prop(q)])
        add([-a] + sel)
    # OneGood: at most one good atom in Z.  SAT = two distinct good atoms of Z.
    # M:OneExitAtom (mutant): at most one atom of Z exits.  SAT = two distinct atoms of Z exit.
    exq = {q: s.OR(('exq', q), [s.ext[q, c] for c in s.atoms]) for q in s.atoms}
    for name, prop in (('OneGood', lambda q: s.good[q]), ('M:OneExitAtom', lambda q: exq[q])):
        a = s.v('act', name); Q[name] = a; sel = []
        for i, q in enumerate(s.atoms):
            for q2 in s.atoms[i + 1:]:
                o = s.v('sel', name, q, q2); sel.append(o)
                for lit in (s.Z(q), s.Z(q2), prop(q), prop(q2)): add([-o, lit])
        add([-a] + sel)
    # MaxIdx2: some m in M2 of MAXIMAL landing index among M2 exits with c(m) <= m.  SAT = none does.
    # M:MinIdx2 (mutant): some m in M2 of MINIMAL landing index among M2 exits with c(m) <= m.  SAT = none does.
    lj2 = {j: s.OR(('lj2', j), [s.AND(('zli2', m, j), [s.Z(m), s.li[m, j]]) for m in s.h2]) for j in range(NO + 1)}
    for name, ext in (('MaxIdx2', lambda j: [-lj2[j2] for j2 in range(j + 1, NO + 1)]), ('M:MinIdx2', lambda j: [-lj2[j2] for j2 in range(j)])):
        I = {j: s.AND(('I2', name, j), [lj2[j]] + ext(j)) for j in lj2}
        a = s.v('act', name); Q[name] = a
        for m in s.h2:
            X = s.AND(('X2', name, m), [s.Z(m), s.OR(('X2o', name, m), [s.AND(('X2j', name, m, j), [I[j], s.li[m, j]]) for j in I])])
            add([-a, -X, -s.C[m]])
    return Q

def check(r, name):
    L = r.L; le = L.le; h = L.rank
    top2 = [m for m in r.Zs if h[m] == 2]
    def tcell(m):
        p = r.lam(m); q = L.meet[m][p]
        return h[p] == 2 and p != m and h[q] == 1 and le[q][r.F[q][p]]
    G = [q for q in r.atoms if r.good(q)]
    if name == 'TopCell': return not any(tcell(m) for m in top2)
    if name == 'NMGood': return not any(q in G for q in r.atoms if any(le[q][m] and m != q for m in top2))
    if name == 'TopCert': return not any(r.cert(m) for m in top2)
    if name == 'M:TopCellAll': return any(not tcell(m) for m in top2)
    if name == 'GoodFix': return any(not (r.exits(q) and r.c(q) == q) for q in G)
    if name == 'M:GoodA': return any(not le[q][a_of(L, r.F, q)] for q in G)
    if name == 'OneGood': return len(G) >= 2
    if name == 'M:OneExitAtom': return len([q for q in r.atoms if r.exits(q)]) >= 2
    if name in ('MaxIdx2', 'M:MinIdx2'):
        I = {m: r.li(m) for m in top2}; t = max(I.values()) if name == 'MaxIdx2' else min(I.values())
        return not any(r.cert(m) for m in top2 if I[m] == t)
    raise ValueError(name)

if __name__ == '__main__':
    args = sys.argv[1:]
    print(f'toplayer2 | corpus {args} | per lattice (height >= 3) and branch, over ALL F in W0+n1: vac = SAT iff the branch has a'
          f' model; every other column = SAT iff the named statement FAILS for some F (see docstring)', flush=True)
    T = collections.defaultdict(collections.Counter); best = {}; t0 = time.time(); tag = '_'.join(a.split('/')[-1] for a in args)
    for idx, L in enumerate(lattices(args)):
        if L.height < 3: continue
        t1 = time.time(); w = W(L); Q = queries(w); row = []
        for b in BR:
            if not w.S.solve(assumptions=w.brl[b]): row.append(f'{b}:-'); continue
            rep = Rep(L, w.decode()); assert rep.world and rep.br == b, ('vac replay', b)
            T[(b, 'vac')][f'h{L.height}'] += 1; cells = []
            for name, a in Q.items():
                if w.S.solve(assumptions=w.brl[b] + [a]):
                    rep = Rep(L, w.decode()); assert rep.world and rep.br == b and check(rep, name), ('replay', b, name)
                    T[(b, name)][f'h{L.height}'] += 1; cells.append(f'{name}=SAT')
                    if (b, name) not in best or L.n < best[b, name][0]: best[b, name] = (L.n, idx, dict(sets=L.S, F=rep.F))
                else: cells.append(f'{name}=uns')
            row.append(f'{b}:[' + ' '.join(cells) + ']')
        print(f'lattice {idx} n={L.n} h={L.height} {time.time() - t1:.0f}s | ' + ' '.join(row), flush=True)
        w.S.delete()
    print(f'== totals: lattices with a SAT, by height ({time.time() - t0:.0f}s)')
    for (b, name), c in sorted(T.items()): print(f'  {b:7s} {name:13s} {dict(c)}')
    for (b, name), (nn, idx, mdl) in sorted(best.items()):
        if name == 'vac': continue
        print(f'  smallest SAT {b} {name}: |L| = {nn} (lattice {idx})')
        json.dump(mdl, open(os.path.join(OUT, f'm2_{tag}_{name.replace(":", "")}_{b}_min{nn}.json'), 'w'))
