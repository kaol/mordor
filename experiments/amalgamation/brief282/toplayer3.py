"""amr_run14 briefer -- TOP-LAYER probe, third statement set (exact): the lead NMGood and its decisive step TopCert = ExitM2 +
choice of exit, each with a paired mutant.  World, branches, quantifier and replay exactly as in toplayer.py (W and Rep of
amr_run13/ctlA/w0lean.py).  Every column: SAT iff the named statement FAILS for some F on this lattice and branch; vac: SAT
iff the branch has a model.  Every SAT model is replayed from the definitions before it is counted.
  NMGood        some atom of Z strictly below an element of M2 is good                      (lead; fails on g by design)
  TopCert       some m in M2 exits with c(m) <= m                                           (decisive step; fails on g by design)
  ExitM2        some m in M2 exits                                                          (first half of TopCert)
  M:AllExitM2   MUTANT of ExitM2: every m in M2 exits
  M:AllDomM2    MUTANT of TopCert: every exiting m in M2 has c(m) <= m
  M:TopCellAll  MUTANT of NMGood: every m in M2 has the TopCell cell
  python3 toplayer3.py (file PATH... | tall K M SEED CNT | closure K M SEED CNT)"""
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
    a = s.v('act', 'NMGood'); Q['NMGood'] = a
    for q in s.atoms:
        for m in s.h2:
            if le[q][m]: add([-a, -s.Z(m), -s.good[q]])
    a = s.v('act', 'TopCert'); Q['TopCert'] = a
    for m in s.h2:
        for c in s.atoms:
            if le[c][m]: add([-a, -s.Z(m), -s.ext[m, c]])
    a = s.v('act', 'ExitM2'); Q['ExitM2'] = a
    for m in s.h2:
        for c in s.atoms: add([-a, -s.Z(m), -s.ext[m, c]])
    a = s.v('act', 'M:AllExitM2'); Q['M:AllExitM2'] = a; sel = []
    for m in s.h2:
        o = s.v('aem', m); sel.append(o); add([-o, s.Z(m)])
        for c in s.atoms: add([-o, -s.ext[m, c]])
    add([-a] + sel)
    a = s.v('act', 'M:AllDomM2'); Q['M:AllDomM2'] = a; sel = []
    for m in s.h2:
        for c in s.atoms:
            if le[c][m]: continue
            o = s.v('sel', 'ad', m, c); sel.append(o); add([-o, s.Z(m)]); add([-o, s.ext[m, c]])
    add([-a] + sel)
    a = s.v('act', 'M:TopCellAll'); Q['M:TopCellAll'] = a; sel = []
    for m in s.h2:
        o = s.v('tca', m); sel.append(o); add([-o, s.Z(m)]); add([-o, -tc[m]])
    add([-a] + sel)
    return Q

def check(r, name):
    L = r.L; le = L.le; h = L.rank
    top2 = [m for m in r.Zs if h[m] == 2]
    def tcell(m):
        p = r.lam(m); q = L.meet[m][p]
        return h[p] == 2 and p != m and h[q] == 1 and le[q][r.F[q][p]]
    if name == 'NMGood': return not any(r.good(q) for q in r.atoms if any(le[q][m] and m != q for m in top2))
    if name == 'TopCert': return not any(r.cert(m) for m in top2)
    if name == 'ExitM2': return not any(r.exits(m) for m in top2)
    if name == 'M:AllExitM2': return any(not r.exits(m) for m in top2)
    if name == 'M:AllDomM2': return any(r.exits(m) and not le[r.c(m)][m] for m in top2)
    if name == 'M:TopCellAll': return any(not tcell(m) for m in top2)
    raise ValueError(name)

if __name__ == '__main__':
    args = sys.argv[1:]
    print(f'toplayer3 | corpus {args} | per lattice (height >= 3) and branch, over ALL F in W0+n1: vac = SAT iff the branch has a'
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
        json.dump(mdl, open(os.path.join(OUT, f'm3_{tag}_{name.replace(":", "")}_{b}_min{nn}.json'), 'w'))
