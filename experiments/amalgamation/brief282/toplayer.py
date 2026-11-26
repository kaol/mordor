"""amr_run14 briefer -- TOP-LAYER probe (exact).  Run from this directory; writes only here.
World: W0 + n1 at level 1 with h(top) >= 3, encoded by the run-13 control-A class W (amr_run13/ctlA/w0lean.py, independent of
muorbit_sat.py): rows F(x, .) for low x (h <= 2) one-hot, monotone in x and y; a(bot) = bot; (T) at every row of Z
(includes ZT via x = bot); n1.  Rows of high x are irrelevant (top in the replay).  Branches as in w0lean: exit-a / in-a
(h(d) = 2, d exits / in-steps), exit-b / in-b (d a bad atom), g (d a good atom).
Notation: Z = {y : F(bot, y) = bot}; M2 = elements of Z of height 2 (the TOP LAYER of Z); lambda(x) = first element of height
<= 2 on row x's descent from top; x EXITS iff lambda(x) not in Z, then c(x) = F(bot, lambda(x)) (an atom of Z).
QUANTIFIER: for each lattice and branch, over ALL monotone F in the world.  Every column is 'SAT = the named statement FAILS
for some F on this lattice and branch'; 'vac' = 'SAT = the branch has a model'.  Every SAT model is decoded, replayed from
the definitions (stages of R recomputed by rstages.stages) and the failure re-checked in Python before it is counted.
Statements:
  TopCell     some m in M2 has q = m meet lambda(m) an atom with q <= F(q, lambda(m))          [worker's rung; fails on g by design]
  NMGood      some atom q of Z lying strictly below an element of M2 is good                    [briefer: normal form of TopCell]
  ExitM2      some m in M2 exits
  TopAbsorb   every m in M2 that exits has an exiting m' in M2 with c(m') = c(m) <= m'          [briefer's LEAD, with ExitM2]
  M:ExitDom   MUTANT of TopAbsorb (layer restriction dropped; refuted |L| = 12 in §34.3z²⁷⁵): every exiting x in Z* has an
              exiting x2 in Z* with c(x2) = c(x) <= x2
  M:AllDomM2  MUTANT of TopAbsorb (absorption by m itself): every exiting m in M2 has c(m) <= m
  M:TopCellAll MUTANT of TopCell/NMGood: every m in M2 has the TopCell cell
  python3 toplayer.py (file PATH... | tall K M SEED CNT | closure K M SEED CNT)"""
import sys, collections, time, json, os
sys.path.insert(0, '/home/user/mordor/experiments/separation'); sys.path.insert(0, '/home/user/mordor/experiments/amalgamation')
sys.path.insert(0, '/tmp/claude-0/-home-user/3b6fdd2c-c95c-5c07-b47c-6ae28c687a4c/scratchpad/amr_run13/ctlA')
from w0lean import W, Rep, BR
from tight_probe import lattices
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
    a = s.v('act', 'ExitM2'); Q['ExitM2'] = a
    for m in s.h2:
        for c in s.atoms: add([-a, -s.Z(m), -s.ext[m, c]])
    for name, rows, absorb in (('TopAbsorb', s.h2, s.h2), ('M:ExitDom', [x for x in R if x != bot], [x for x in R if x != bot])):
        a = s.v('act', name); Q[name] = a; sel = []
        for m in rows:
            for c in s.atoms:
                o = s.v('sel', name, m, c); sel.append(o); add([-o, s.Z(m)]); add([-o, s.ext[m, c]])
                for m2 in absorb:
                    if le[c][m2]: add([-o, -s.Z(m2), -s.ext[m2, c]])
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
    ex = lambda x: r.exits(x)
    absorbed = lambda x, pool: any(ex(y) and r.c(y) == r.c(x) and le[r.c(x)][y] for y in pool)
    if name == 'TopCell': return not any(tcell(m) for m in top2)
    if name == 'NMGood': return not any(r.good(q) for q in r.atoms if any(le[q][m] and m != q for m in top2))
    if name == 'ExitM2': return not any(ex(m) for m in top2)
    if name == 'TopAbsorb': return any(ex(m) and not absorbed(m, top2) for m in top2)
    if name == 'M:ExitDom': return any(ex(x) and not absorbed(x, r.Zs) for x in r.Zs)
    if name == 'M:AllDomM2': return any(ex(m) and not le[r.c(m)][m] for m in top2)
    if name == 'M:TopCellAll': return any(not tcell(m) for m in top2)
    raise ValueError(name)

if __name__ == '__main__':
    args = sys.argv[1:]
    print(f'toplayer | corpus {args} | per lattice (height >= 3) and branch, over ALL F in W0+n1: vac = SAT iff the branch has a'
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
        json.dump(mdl, open(os.path.join(OUT, f'm_{tag}_{name.replace(":", "")}_{b}_min{nn}.json'), 'w'))
