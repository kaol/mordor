"""Shadow chains down the B-sources (log §34.3z¹⁷⁹; `dropChain_exit`).

From every drop node (p, c) = (feeder m′, drop column q ∈ (m′, w]) of each remaining-case configuration (multi,
nopostlayer, rank ≥ R): follow p ↦ b(p), c ↦ F(b(p), c) while the new row drops; record the exit (depth i, type
L = lower cell, U = stays above, D = diagonal fixed row that drops), the stage/height status of the exit row and
column, and the relation of the exit to the original-level UpCell witnesses.
  python3 chain_probe.py [rmin=R] (sweep … | closure …)
"""
import sys, collections
sys.argv += ['multi', 'nopostlayer']
sys.path.insert(0, '../separation')
from rstages import stages, a_of, b_of
from gfp_top import ystar
from tight_probe import lattices
import single_claims as sc

C = collections.Counter()
for L in lattices([a for a in sys.argv[1:] if a not in ('multi', 'nopostlayer') and not a.startswith('rmin=')]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'noic_fi', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        rel = lambda x, y: '=' if x == y else '<' if le[x][y] else '>' if le[y][x] else '∥'
        B = lambda y: b_of(L, F, y)
        mp = B(m); w = F[m][ystar(L, F, m)]
        ups = lambda y: [z for z in range(n) if le[y][z] and z != y and not le[m][z] and (le[F[y][z]][y] or le[z][F[y][z]])]
        Tk = [y for y in range(n) if inR(y, k) and h[y] == k and not inR(y, k - 1)]
        wit = [y for y in Tk if inR(B(y), k - 1) and le[B(y)][y] and B(y) != y and ups(y)]   # CoverUpCell witnesses
        drops = [q for q in range(n) if le[mp][q] and q != mp and le[q][w] and le[F[mp][q]][q] and not le[mp][F[mp][q]]]
        if not drops: break
        C['drop models'] += 1
        for q0 in drops:
            p, c, i = mp, q0, 0
            assert le[F[p][p]][p]
            while True:                                  # dropChain_exit, replayed
                if B(p) == p: typ = 'D'; r, e = p, c; break
                qq = B(p); e = F[qq][c]
                if le[e][qq]: typ = 'L'; r, e = qq, c; i += 1; break
                fe = F[qq][e]
                if le[fe][qq]: typ = 'L'; r = qq; i += 1; break
                if le[qq][fe]: typ = 'U'; r = qq; i += 1; break
                p, c, i = qq, e, i + 1
            assert le[r][e] and r != e and le[F[r][e]][e]
            s = st[r]
            C[('exit', 'depth', i, 'type', typ)] += 1
            C[('exit row', 'h(r) = k − depth', h[r] == k - i, 'new at its stage', s is not None and not inR(r, s - 1) if s else True)] += 1
            if typ == 'L': C[('L-exit column e', 'e ∈ R_{stage(r)+1}', inR(e, s + 1), 'h(e) − h(r)', h[e] - h[r])] += 1
            if typ == 'U': C[('U-exit', 'cell (e ≤ F(r,e))', le[e][F[r][e]])] += 1
            C[('exit column e vs m', rel(e, m))] += 1
            pairs = [(y, z) for y in wit for z in ups(y)]
            if not any(le[e][z] for y, z in pairs):
                import json; json.dump(dict(sets=L.S, F=F, m=m, q0=q0, r=r, e=e, depth=i, type=typ), open(f'chain_rescue_fail_min{n}.json', 'w'))
            C[('witness pair (y, z)', 'r ≤ y', any(le[r][y] for y, z in pairs), 'e ≤ z', any(le[e][z] for y, z in pairs),
               'e ≤ z ≤ q0', any(le[e][z] and le[z][q0] for y, z in pairs), 'r ≤ y and e ≤ z', any(le[r][y] and le[e][z] for y, z in pairs))] += 1
            C[('witness pair', 'y ≤ e', any(le[y][e] for y, z in pairs), 'z = e', any(z == e for y, z in pairs))] += 1
            C[('witness vs exit', 'some witness y ≥ r', any(le[r][y] for y in wit), 'some witness y with a cell column ≥ e', any(any(le[e][z] for z in ups(y)) for y in wit))] += 1
        break
for k_, v in sorted(C.items(), key=str): print(k_, v)
