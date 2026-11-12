"""Which hypotheses does feeder identity use? (log §34.3z¹⁵⁷)

Feeder identity: m' ∈ R_k of height k, t ⋗ m', t ∉ R_k, F(m', t) ≤ m'  ⇒  b(t) = m'.
True orbit (amalg_sat.Enc). Base hypotheses: R_k ranks ≤ k (index bound at k). Optional hypothesis groups:
  next  : R_{k+1} ranks ≤ k + 1           top : ⊤ ∉ R_{k+2}
  nobound: drop the index bound at k      (then only t ∉ R_k, m' ∈ R_k of rank k)
  base   : the orbit starts from an arbitrary down-set S₀ ∋ ⊥ instead of {⊥} (R_j = step^j(S₀)); index-free form
  off=d  : use stage k = h(m') + d instead of h(m')
  nocover: t any element above m' (not only covers)
  nolow  : replace the lower cell F(m', t) ≤ m' by b(t) < m' (goal then: t ∈ R_k, i.e. b(t) ∈ R_{k−1})
  ctl    : control, drop the goal b(t) ≠ m' (should be SAT)
  bound=j: replace the index bound at k by: R_j ranks ≤ j for this j only (j < k)
Query: a configuration with b(t) ≠ m' (SAT = counterexample, re-checked in Python).
  python3 feeder.py [next] [top] [nobound] [bound=j] (sweep P NMAX | closure K M SEED COUNT)
"""
import sys, collections, json
sys.path.insert(0, '../separation')
import separator_stages as ss
from amalg_sat import Enc
from rstages import stages, b_of
from tight_probe import helpers, lattices

def base_stages(E, L, K):
    n = L.n; le = L.le; h = lambda i, z: E.v('h', i, z)
    for z in range(n):
        for w in L.covers_dn[z]: E.S.add_clause([-h(0, z), h(0, w)])
    E.S.add_clause([h(0, L.bot)])
    for i in range(K):
        gen = {}
        for g in range(n):
            lits = [h(i, g)]
            for x in range(n):
                w = E.v('ha', i, x, g); E.iff_and(w, [h(i, x), E.v('A', x, g)]); lits.append(w)
            for y in range(n):
                w = E.v('hb', i, g, y); E.iff_and(w, [E.v('B', g, y), h(i, y)]); lits.append(w)
            gv = E.v('hgen', i, g); E.iff_or(gv, lits); gen[g] = gv
        for z in range(n): E.iff_or(h(i + 1, z), [gen[g] for g in range(n) if le[z][g]])
    return h

def query(L, mp, t, opt):
    n = L.n; le = L.le; rk = L.rank; k = rk[mp] + next((int(o[4:]) for o in opt if o.startswith('off=')), 0)
    if k < 0: return None
    if 'base' in opt:
        E = Enc(L, 0); fle, yle, ic = helpers(E, L); r = base_stages(E, L, k + 2)
    else:
        E = Enc(L, k + 2); fle, yle, ic = helpers(E, L); r = lambda j, z: E.v('r', j, z)
    E.S.add_clause([r(k, mp)]); E.S.add_clause([-r(k, t)])
    if 'nolow' in opt: E.S.add_clause([E.v('B', t, c) for c in range(n) if le[c][mp] and c != mp])
    else:
        E.S.add_clause([fle(mp, t, mp)])
        if 'ctl' not in opt: E.S.add_clause([-E.v('B', t, mp)])
    bj = next((int(o[6:]) for o in opt if o.startswith('bound=')), None)
    for z in range(n):
        if 'nobound' not in opt and bj is None and rk[z] > k: E.S.add_clause([-r(k, z)])
        if bj is not None and rk[z] > bj: E.S.add_clause([-r(bj, z)])
        if 'next' in opt and rk[z] > k + 1: E.S.add_clause([-r(k + 1, z)])
    if 'top' in opt: E.S.add_clause([-r(k + 2, L.top)])
    if not E.S.solve(): E.S.delete(); return False
    if 'base' in opt:
        mod = set(x for x in E.S.get_model() if x > 0); F = E.decode(); E.S.delete()
        import single_local as sl
        S0 = [E.vars[('h', 0, z)] in mod for z in range(n)]; Rs = [S0]
        for i in range(k + 2): Rs.append(sl.step_py(L, F, Rs[-1]))
        inR = lambda z, j: Rs[j][z]
    else:
        F = E.decode(); E.S.delete(); st = stages(L, F); inR = lambda z, j: st[z] is not None and st[z] <= j
    if 'nolow' in opt: assert inR(mp, k) and not inR(t, k) and le[b_of(L, F, t)][mp] and b_of(L, F, t) != mp
    else: assert inR(mp, k) and not inR(t, k) and le[F[mp][t]][mp] and ('ctl' in opt or b_of(L, F, t) != mp)
    if 'nobound' not in opt and bj is None: assert all(rk[z] <= k for z in range(n) if inR(z, k))
    if bj is not None: assert all(rk[z] <= bj for z in range(n) if inR(z, bj))
    if 'next' in opt: assert all(rk[z] <= k + 1 for z in range(n) if inR(z, k + 1))
    if 'top' in opt: assert not inR(L.top, k + 2)
    return F

if __name__ == '__main__':
    opt = [a for a in sys.argv[1:] if a in ('next', 'top', 'nobound', 'ctl', 'base', 'nocover', 'nolow') or a.startswith('bound=') or a.startswith('off=')]
    args = [a for a in sys.argv[1:] if a not in opt]
    C = collections.Counter(); best = None
    for L in lattices(args):
        hit = None
        for mp in range(L.n):
            if L.rank[mp] < 1: continue
            for t in ([u for u in range(L.n) if L.le[mp][u] and u != mp] if 'nocover' in opt else L.covers_up[mp]):
                if t == L.top and 'top' in opt: continue
                res = query(L, mp, t, opt)
                if res: hit = (mp, t, res); break
            if hit: break
        C['counterexample' if hit else 'none'] += 1
        if hit and (best is None or L.n < best[0].n): best = (L, hit)
    print(f"feeder {' '.join(opt)}: {dict(C)}" + (f"; smallest |L| = {best[0].n}, k = {best[0].rank[best[1][0]]}" if best else ''), flush=True)
    if best:
        L, (mp, t, F) = best
        json.dump(dict(sets=L.S, F=F, mp=mp, t=t), open(f"feeder{'_' + '_'.join(opt) if opt else ''}_min{L.n}.json", 'w'))
