"""Good tops at tight stages (log §34.3z²⁵⁶): TopGood / RestartGood, MixedBase, EntryCert. Stage k: R_k tight, ⊤ ∉ R_{k+1},
h(⊤) > k. 'p good' = p ≤ a(p) or the row-p descent from ⊤ meets p. T_k = elements of R_k of height k.
  vac      — hypotheses only
  topgood  — every p ∈ T_k is bad                                    (SAT refutes TopGood(k))
  mixedchk — some (r, p): p ∈ T_k, r ∈ R_{k−1}, h(r)=k−1, r<p, r ≤ F(r,p), DL(r,p), p bad   (SAT refutes the DL lemma)
  mixed    — no DL pair and no A-entry from below (p = a(x), x ∈ R_{k−1}, x ≤ p)            (SAT refutes MixedBase)
  gbr      — no good element of R_{k−1} of height k−1 (GoodBase at the restart; §34.3z²⁵⁷)
  bdl      — no B-source DL pair (q = b(p) ∈ R_{k−1}, h(q)=k−1, DL(q,p)) and no A-entry from below (SAT refutes EntryCert)
DL(r,p): ∀ y ≰ p, ¬(y ≤ F(r, p ⊔ y)).
Flags: rkm1nt (R_{k−1} non-tight: restart world), notight (drop R_k tightness).
  python3 topgood.py MODE k (sweep N MAX | closure K M SEED CNT) [flags]"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import lattices
from rstages import stages, a_of, b_of
FLG = {'rkm1nt', 'notight'}
MODE = sys.argv[1]; k = int(sys.argv[2]); FL = {a for a in sys.argv[3:] if a in FLG}; args = [a for a in sys.argv[3:] if a not in FLG]
if MODE not in {'vac', 'topgood', 'mixedchk', 'mixed', 'bdl', 'gbr'}: raise SystemExit('unknown mode')
C = collections.Counter(); INFO = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; top = L.top; NO = L.height + 1; jn = L.join
    if L.height <= k: continue
    last = (L.height == k + 1)
    E = Enc(L, k + 1); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
    A = lambda x, g: E.v('A', x, g); B = lambda y, g: E.v('B', y, g)
    if 'notight' not in FL:
        for z in range(n):
            if h[z] > k: add([-r(k, z)])
    add([-r(k + 1, top)])
    if 'rkm1nt' in FL: add([r(k - 1, z) for z in range(n) if h[z] > k - 1])
    def descvars(p):
        D = lambda i, z: E.v('DD', p, i, z)
        if ('DD', p, 0, top) in E.vars: return D
        for z in range(n): add([D(0, z)] if z == top else [-D(0, z)])
        for i in range(NO):
            for z in range(n):
                lits = []
                for v in range(n): o = E.v('DDs', p, i, v, z); E.iff_and(o, [D(i, v), f(p, v, z)]); lits.append(o)
                E.iff_or(D(i + 1, z), lits)
        return D
    def bad(p):                                   # literal set: p bad (all clauses guarded by the returned var)
        o = E.v('bad', p)
        if ('badset', p) not in E.vars:
            E.v('badset', p); D = descvars(p)
            for i in range(NO + 1): add([-o, -D(i, p)])
            for g in range(n):
                if le[p][g]: add([-o, -A(p, g)])
        return o
    def DL(rr, p):
        o = E.v('DL', rr, p)
        if ('DLset', rr, p) not in E.vars:
            E.v('DLset', rr, p); ts = []
            for y in range(n):
                if le[y][p]: continue
                t = E.v('DLt', rr, p, y); E.iff_or(t, [f(rr, jn[p][y], g) for g in range(n) if le[y][g]]); ts.append(-t)
            E.iff_and(o, ts) if ts else add([o])
        return o
    def pge(rr, p):
        o = E.v('pge', rr, p); E.iff_or(o, [f(rr, p, v) for v in range(n) if le[rr][v]]); return o
    T = [p for p in range(n) if h[p] == k]
    if MODE == 'topgood':
        for p in T: add([-r(k, p), bad(p)])
    elif MODE == 'gbr':
        for z in range(n):
            if h[z] == k - 1 and z != top: add([-r(k - 1, z), bad(z)])
    elif MODE == 'mixedchk':
        sel = []
        for p in T:
            for rr in range(n):
                if h[rr] != k - 1 or not le[rr][p]: continue
                o = E.v('mc', rr, p); sel.append(o)
                for lit in (r(k, p), r(k - 1, rr), pge(rr, p), DL(rr, p), bad(p)): add([-o, lit])
        add(sel)
    elif MODE in ('mixed', 'bdl'):
        for p in T:
            for rr in range(n):
                if h[rr] != k - 1 or not le[rr][p]: continue
                if MODE == 'mixed': add([-r(k, p), -r(k - 1, rr), -pge(rr, p), -DL(rr, p)])
                else: add([-r(k, p), -r(k - 1, rr), -B(p, rr), -DL(rr, p)])
            for x in range(n):
                if le[x][p]: add([-r(k, p), -r(k - 1, x), -A(x, p)])
    if E.S.solve():
        F = E.decode(); st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j
        def desc(p):
            v = top; seen = []
            while v not in seen: seen.append(v); v = F[p][v]
            return seen
        good = lambda p: le[p][a_of(L, F, p)] or p in desc(p)
        dl = lambda rr, p: not any(not le[y][p] and le[y][F[rr][jn[p][y]]] for y in range(n))
        Tk = [p for p in T if inR(p, k)]
        ok = not inR(top, k + 1) and ('notight' in FL or all(h[z] <= k for z in range(n) if inR(z, k)))
        if 'rkm1nt' in FL: ok = ok and any(h[z] > k - 1 for z in range(n) if inR(z, k - 1))
        aent = lambda p: any(le[x][p] and inR(x, k - 1) and a_of(L, F, x) == p for x in range(n))
        if MODE == 'topgood': ok = ok and not any(good(p) for p in Tk)
        elif MODE == 'gbr':
            ok = ok and not any(h[z] == k - 1 and inR(z, k - 1) and good(z) for z in range(n))
            gt = [p for p in Tk if good(p)]
            INFO['goodtop_Aentry_low' if any(aent(p) for p in gt) else ('goodtop_other' if gt else 'no_goodtop')] += 1
        elif MODE == 'mixedchk': ok = ok and any(h[rr] == k - 1 and le[rr][p] and inR(rr, k - 1) and le[rr][F[rr][p]] and dl(rr, p) and not good(p) for p in Tk for rr in range(n))
        elif MODE == 'mixed': ok = ok and not any(aent(p) or any(h[rr] == k - 1 and le[rr][p] and inR(rr, k - 1) and le[rr][F[rr][p]] and dl(rr, p) for rr in range(n)) for p in Tk)
        elif MODE == 'bdl':
            ok = ok and not any(aent(p) or (h[b_of(L, F, p)] == k - 1 and inR(b_of(L, F, p), k - 1) and le[b_of(L, F, p)][p] and dl(b_of(L, F, p), p)) for p in Tk)
            for p in Tk:
                q = b_of(L, F, p); INFO[f'b(p):h{h[q]}{"inR" if inR(q, k - 1) else "out"}{"_DL" if dl(q, p) else ""}'] += 1
        assert ok, 'SAT/Python mismatch'
        C['SAT'] += 1; INFO['SAT_last' if last else 'SAT_notlast'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else: C['UNSAT'] += 1; INFO['UNSAT_last' if last else 'UNSAT_notlast'] += 1
    E.S.delete()
print(MODE, 'k', k, ' '.join(sorted(FL)), dict(C), 'smallest', best[0] if best else None, dict(INFO))
if best and MODE != 'vac':
    json.dump(best[1], open(f'topgood_{MODE}_k{k}{"".join("_" + x for x in sorted(FL))}_min{best[0]}.json', 'w'))
