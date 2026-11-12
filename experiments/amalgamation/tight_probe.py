"""Tight-stage entry routes and the maximal-b-fibre conjecture, exactly (log §34.3z¹⁵²).

Built on amalg_sat.Enc (F one-hot monotone, A = a as gfp, B = b as lfp, r[k][z] = z ∈ R_k). A tight stage k:
every z ∈ R_k has height ≤ k and ⊤ ∉ R_{k+1}. T_k = elements of R_k of height k. IC(m): some y > m has
F(m, y) ≤ m or y ≤ F(m, y).
  aentry : does some m ∈ T_k first enter by an a-entry m = a(x), x ∥ m, with m non-diagonal (m ≰ F(m, m))?
           (with 'noic': and no element of T_k has an interval cell — a TightIC counterexample in that branch)
  fibre  : counterexample to Maximal-fibre TightIC: every m ∈ T_k with b(m) maximal in B_k = {b(m') : m' ∈ T_k}
           lacks an interval cell ('bonly': additionally every element of T_k first enters by a b-entry).
Models are decoded and re-simulated with rstages.stages.
  'minfibre': the same with b(m) minimal in B_k.
  gfp    : counterexample to Tight-GFP (§34.3z¹⁵³): no m ∈ T_k satisfies GFP(m), i.e. for every m ∈ T_k the greatest
           fixed point y* of y ↦ m ⊔ F(m, y) has y* ≠ m and F(m, y*) ≠ y* ('single': |T_k| = 1; 'noic': and no
           element of T_k has an interval cell; 'some': sanity control, only some m ∈ T_k fails GFP).
  old    : a tight stage all of whose top elements are old (T_k ⊆ R_{k−1}) ('single': |T_k| = 1; 'some': control, some top old) (§34.3z¹⁵⁴).
  transfer: consecutive tight stages k − 1, k (k ≥ 2) where no cell target t ∈ T_k of a top m' ∈ T_{k−1}
           (m' < t, F(m', t) ≤ m' or t ≤ F(m', t)) has an interval cell (§34.3z¹⁵⁴; 'noic': no top of T_k has one; 'some': control, some target lacks a cell).
  python3 tight_probe.py transfer [noic] (sweep P NMAX | closure K M SEED COUNT)
  python3 tight_probe.py old [single] (sweep P NMAX | closure K M SEED COUNT)
  python3 tight_probe.py gfp [single] [noic] (sweep P NMAX | closure K M SEED COUNT)
  python3 tight_probe.py (aentry [noic] | fibre [bonly] [minfibre]) (sweep P NMAX | closure K M SEED COUNT)
"""
import sys, itertools, random, collections, json
sys.path.insert(0, '../separation')
import separator_stages as ss
from amalg_sat import Enc
from rstages import stages, a_of, b_of
from gfp_top import ystar, gfp_ok, ic as ic_py

def helpers(E, L):
    n = L.n; le = L.le
    def fle(x, y, t):
        k = ('fle', x, y, t)
        if k not in E.vars: o = E.v(*k); E.iff_or(o, [E.v('f', x, y, w) for w in range(n) if le[w][t]])
        return E.vars[k]
    def yle(x, y):
        k = ('yle', x, y)
        if k not in E.vars: o = E.v(*k); E.iff_or(o, [E.v('f', x, y, w) for w in range(n) if le[y][w]])
        return E.vars[k]
    def ic(m):
        k = ('ic', m)
        if k not in E.vars:
            o = E.v(*k); lits = []
            for y in range(n):
                if y != m and le[m][y]: lits += [fle(m, y, m), yle(m, y)]
            E.iff_or(o, lits)
        return E.vars[k]
    return fle, yle, ic

def query(L, k, mode, opt):
    E = Enc(L, k + 1); n = L.n; le = L.le; rk = L.rank; r = lambda j, z: E.v('r', j, z)
    fle, yle, ic = helpers(E, L)
    E.S.add_clause([-r(k + 1, L.top)])
    for z in range(n):
        if rk[z] > k: E.S.add_clause([-r(k, z)])
    T = [m for m in range(n) if rk[m] == k]
    if not T: return None
    def aent(m):              # m first enters by an a-entry with x ∥ m (some stage j < k)
        lits = []
        for j in range(k):
            for x in range(n):
                if le[x][m] or le[m][x]: continue
                o = E.v('ae', m, j, x); E.iff_and(o, [-r(j, m), r(j + 1, m), r(j, x), E.v('A', x, m)]); lits.append(o)
        o = E.v('aent', m); E.iff_or(o, lits); return o
    def bent(m):              # m first enters by a b-entry
        lits = []
        for j in range(k):
            for g in range(n):
                o = E.v('be', m, j, g); E.iff_and(o, [-r(j, m), r(j + 1, m), E.v('B', m, g), r(j, g)]); lits.append(o)
        o = E.v('bent', m); E.iff_or(o, lits); return o
    if mode == 'transfer':
        if k < 2: return None
        P = [z for z in range(n) if rk[z] == k - 1]
        for z in range(n):
            if rk[z] > k - 1: E.S.add_clause([-r(k - 1, z)])
        E.S.add_clause([r(k - 1, z) for z in P])
        for t in T:
            lits = []
            for mp in P:
                if not le[mp][t]: continue
                c = E.v('cellor', mp, t); E.iff_or(c, [fle(mp, t, mp), yle(mp, t)])
                o = E.v('tgt', mp, t); E.iff_and(o, [r(k - 1, mp), c]); lits.append(o)
            if 'some' in opt:                  # control: some target lacks a cell
                tg = E.v('tg', t); E.iff_or(tg, lits); pk = E.v('pick', t); E.iff_and(pk, [tg, -ic(t)])
            else:
                for o in lits: E.S.add_clause([-o, -ic(t)])
            if 'noic' in opt: E.S.add_clause([-r(k, t), -ic(t)])
        E.S.add_clause([r(k, t) for t in T])
        if 'some' in opt: E.S.add_clause([E.v('pick', t) for t in T])
    elif mode == 'old':
        if 'some' in opt:                      # control: some top old
            for m in T: E.v('pick', m); E.iff_and(E.vars[('pick', m)], [r(k, m), r(k - 1, m)])
            E.S.add_clause([E.vars[('pick', m)] for m in T])
        else:
            for m in T: E.S.add_clause([-r(k, m), r(k - 1, m)])
            E.S.add_clause([r(k, m) for m in T])
        if 'single' in opt:
            for m, m2 in itertools.combinations(T, 2): E.S.add_clause([-r(k, m), -r(k, m2)])
    elif mode == 'gfp':
        jn = L.join
        for m in T:
            ys = [E.v('ys', m, y) for y in range(n) if le[m][y]]
            E.S.add_clause(ys)
            for p, q in itertools.combinations(ys, 2): E.S.add_clause([-p, -q])
            for y in range(n):
                if not le[m][y]: continue
                Y = E.v('ys', m, y)
                E.S.add_clause([-Y] + [E.v('f', m, y, w) for w in range(n) if jn[m][w] == y])   # fixed point
                for z in range(n):                                                             # post-fixed z ≤ y*
                    if le[z][y]: continue
                    for w in range(n):
                        if le[z][jn[m][w]]: E.S.add_clause([-Y, -E.v('f', m, z, w)])
                fail = [-r(k, m)] if 'some' not in opt else [-E.v('pick', m)]
                E.S.add_clause(fail + [-Y] + ([] if y == m else [-E.v('f', m, y, y)]))   # ¬GFP(m)
            if 'some' in opt: E.S.add_clause([-E.v('pick', m), r(k, m)])
            if 'noic' in opt: E.S.add_clause([-r(k, m), -ic(m)])
        E.S.add_clause([r(k, m) for m in T] if 'some' not in opt else [E.v('pick', m) for m in T])
        if 'single' in opt:
            for m, m2 in itertools.combinations(T, 2): E.S.add_clause([-r(k, m), -r(k, m2)])
    elif mode == 'aentry':
        sel = []
        for m in T:
            o = E.v('pick', m); E.iff_and(o, [r(k, m), aent(m), -yle(m, m)]); sel.append(o)
        E.S.add_clause(sel)
        if 'noic' in opt:
            for m in T: E.S.add_clause([-r(k, m), -ic(m)])
    else:
        for m in T:
            if 'bonly' in opt: E.S.add_clause([-r(k, m), bent(m)])
            big = []                                      # some m' ∈ T_k has b(m') > b(m)  ('minfibre': <)
            for m2 in T:
                for g in range(n):
                    for g2 in range(n):
                        if g2 != g and (le[g2][g] if 'minfibre' in opt else le[g][g2]):
                            o = E.v('big', m, m2, g, g2); E.iff_and(o, [r(k, m2), E.v('B', m, g), E.v('B', m2, g2)]); big.append(o)
            E.S.add_clause([-r(k, m), -ic(m)] + big)
        E.S.add_clause([r(k, m) for m in T])
    if not E.S.solve(): E.S.delete(); return False
    F = E.decode(); E.S.delete(); return F

def lattices(args):
    if args[0] == 'sweep':
        sys.path.insert(0, '../separation'); import nodesc_sweep as ns
        for fam in ns.moore_families(int(args[1])):
            if len(fam) <= int(args[2]): yield ss.Lat(fam)
    else:
        k, m, sd, cnt = (int(x) for x in args[1:5]); rng = random.Random(sd)
        for _ in range(cnt): yield ss.Lat(ss.closure_system(k, m, rng))

if __name__ == '__main__':
    mode = sys.argv[1]; opt = [a for a in sys.argv[2:] if a in ('noic', 'bonly', 'minfibre', 'single', 'some')]
    args = [a for a in sys.argv[2:] if a not in ('noic', 'bonly', 'minfibre', 'single', 'some')]
    T = collections.Counter(); best = None
    for L in lattices(args):
        if L.height < 2: continue
        hit = None
        for k in range(1, L.height):
            res = query(L, k, mode, opt)
            if res:
                st = stages(L, res); hit = (k, res, st)
                if mode == 'transfer':                # re-simulate: consecutive tight stages, no target has IC
                    for j in (k - 1, k):
                        assert (st[L.top] is None or st[L.top] > j + 1) and max(L.rank[z] for z in range(L.n) if st[z] is not None and st[z] <= j) == j
                    P = [z for z in range(L.n) if st[z] is not None and st[z] <= k - 1 and L.rank[z] == k - 1]
                    for t in range(L.n):
                        if any(L.le[mp][t] and mp != t and (L.le[res[mp][t]][mp] or L.le[t][res[mp][t]]) for mp in P):
                            assert st[t] <= k and L.rank[t] == k and ('some' in opt or not ic_py(L, res, t))
                if mode == 'old':                     # re-simulate: tight stage, every top old
                    Tk = [m for m in range(L.n) if st[m] is not None and st[m] <= k and L.rank[m] == k]
                    assert (st[L.top] is None or st[L.top] > k + 1) and all(L.rank[z] <= k for z in range(L.n) if st[z] is not None and st[z] <= k)
                    assert Tk and (any if 'some' in opt else all)(st[m] < k for m in Tk)
                if mode == 'gfp':                     # re-simulate: tight stage, no top satisfies GFP
                    Tk = [m for m in range(L.n) if st[m] is not None and st[m] <= k and L.rank[m] == k]
                    assert (st[L.top] is None or st[L.top] > k + 1) and all(L.rank[z] <= k for z in range(L.n) if st[z] is not None and st[z] <= k) and Tk
                    G = [gfp_ok(L, res, m) for m in Tk]; assert not all(G) if 'some' in opt else not any(G)
                    if 'noic' in opt: assert not any(ic_py(L, res, m) for m in Tk)
                    if 'single' in opt: assert len(Tk) == 1
                break
        T['SAT' if hit else 'UNSAT'] += 1
        if hit and (best is None or L.n < best[0].n): best = (L, hit)
    print(f"{mode} {' '.join(opt)}: lattices with a model: {dict(T)}", flush=True)
    if best:
        L, (k, F, st) = best; w_ = max(x.bit_length() for x in L.S)
        nm = lambda i: '{' + ''.join(str(j) for j in range(w_) if L.S[i] >> j & 1) + '}'
        Tk = [m for m in range(L.n) if st[m] is not None and st[m] <= k and L.rank[m] == k]
        info = [(nm(m), 'stage', st[m], 'a', nm(a_of(L, F, m)), 'b', nm(b_of(L, F, m)), 'diag', L.le[m][F[m][m]], 'y*', nm(ystar(L, F, m)), 'F(m,y*)', nm(F[m][ystar(L, F, m)])) for m in Tk]
        print(f"smallest: |L| = {L.n}, height {L.height}, tight stage k = {k}, T_k = {info}", flush=True)
        json.dump(dict(sets=L.S, F=F, k=k), open(f"tight_{mode}{'_' + '_'.join(opt) if opt else ''}_min{L.n}.json", 'w'))
