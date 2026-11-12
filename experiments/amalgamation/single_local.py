"""Which hypotheses does singleton-new-top TightIC need? (log §34.3z¹⁵⁵)

Abstract one-step model on a fixed finite lattice L, built on amalg_sat.Enc (F one-hot monotone, A = a, B = b):
  S  : a down-set with ⊥ ∈ S                         (stands for R_{k−1}; arbitrary unless 'orbit')
  S' = step(S) = ↓(S ∪ a(S) ∪ b⁻¹(S)) exactly          (stands for R_k)
  tight : every z ∈ S' has rank ≤ k, and m (rank k) is the only rank-k element of S'; m ∉ S (m new)
  top   : ⊤ ∉ step(S'), i.e. a(x) ≠ ⊤ for x ∈ S' and b(⊤) ∉ S'
  noic  : m has no interval cell (no y > m with F(m, y) ≤ m or y ≤ F(m, y))
Options:
  orbit    : S = R_{k−1} exactly (the true orbit; must be UNSAT if singleton TightIC holds)
  depth=d  : S = step^d(S₀) for an arbitrary down-set S₀ ∋ ⊥ (abstract history of length d; d = 0 is 'plain')
  lower    : some m' ∈ S, m' ⋖ m, with F(m', m) ≤ m' (the lower-transfer hypothesis)
  notop    : drop the 'top' constraint
  tighthist: the abstract history is index-tight: step^i(S₀) has ranks ≤ k − 1 − d + i (S₀ ≤ k − 1 − d)
  nonoic   : control, drop the 'noic' constraint (should be SAT)
  multi    : allow several rank-k elements in S' (none of them may have a cell; m is one of them, still new)
  S-tight  : every element of S has rank ≤ k − 1 (automatic from tight + m ∉ S; kept explicit)
Reports SAT/UNSAT per lattice; SAT models are re-checked in Python and the smallest is saved.
  python3 single_local.py [orbit] [lower] [notop] (sweep P NMAX | closure K M SEED COUNT)
"""
import sys, collections, json
sys.path.insert(0, '../separation')
import separator_stages as ss
from amalg_sat import Enc
from rstages import stages, a_of, b_of
from tight_probe import helpers, lattices
from gfp_top import ic as ic_py

def step_py(L, F, S):
    n = L.n; A = [a_of(L, F, x) for x in range(n)]; B = [b_of(L, F, y) for y in range(n)]
    gen = {g for g in range(n) if S[g]} | {A[x] for x in range(n) if S[x]} | {y for y in range(n) if S[B[y]]}
    return [any(L.le[z][g] for g in gen) for z in range(n)]

def query(L, m, opt):
    n = L.n; le = L.le; rk = L.rank; k = rk[m]
    E = Enc(L, k if 'orbit' in opt else 0)
    fle, yle, ic = helpers(E, L)
    s = lambda z: E.v('s', z); t = lambda z: E.v('t', z)
    def stepc(src, dst, tag):                       # dst = step(src) exactly
        gen = {}
        for g in range(n):
            lits = [src(g)]
            for x in range(n):
                w = E.v(tag + 'a', x, g); E.iff_and(w, [src(x), E.v('A', x, g)]); lits.append(w)
            for h in range(n):
                w = E.v(tag + 'b', g, h); E.iff_and(w, [E.v('B', g, h), src(h)]); lits.append(w)
            gv = E.v(tag + 'gen', g); E.iff_or(gv, lits); gen[g] = gv
        for z in range(n): E.iff_or(dst(z), [gen[g] for g in range(n) if le[z][g]])
    if 'orbit' in opt:
        for z in range(n): E.iff_or(s(z), [E.v('r', k - 1, z)])
    d = next((int(o[6:]) for o in opt if o.startswith('depth=')), 0)
    h = lambda i: (lambda z: E.v('h', i, z)) if i < d else s
    for z in range(n):
        for w in L.covers_dn[z]: E.S.add_clause([-h(0)(z), h(0)(w)])
    E.S.add_clause([h(0)(L.bot)])
    for i in range(d): stepc(h(i), h(i + 1), f'h{i}')
    if 'tighthist' in opt:
        for i in range(d + 1):
            for z in range(n):
                if rk[z] > k - 1 - d + i: E.S.add_clause([-h(i)(z)])
    for z in range(n):
        for w in L.covers_dn[z]: E.S.add_clause([-s(z), s(w)])
    E.S.add_clause([s(L.bot)])
    stepc(s, t, 's')
    for z in range(n):                              # tight, singleton, new
        if rk[z] > k or (rk[z] == k and z != m and 'multi' not in opt): E.S.add_clause([-t(z)])
        if 'multi' in opt and rk[z] == k and z != m: E.S.add_clause([-t(z), -ic(z)])
    E.S.add_clause([t(m)]); E.S.add_clause([-s(m)])
    if 'notop' not in opt:                          # ⊤ ∉ step(t)
        for x in range(n): E.S.add_clause([-t(x), -E.v('A', x, L.top)])
        for h in range(n): E.S.add_clause([-E.v('B', L.top, h), -t(h)])
    if 'nonoic' not in opt: E.S.add_clause([-ic(m)])
    if 'lower' in opt:
        E.S.add_clause([E.v('low', mp) for mp in L.covers_dn[m]])
        for mp in L.covers_dn[m]:
            E.S.add_clause([-E.v('low', mp), s(mp)]); E.S.add_clause([-E.v('low', mp), fle(mp, m, mp)])
    if not E.S.solve(): E.S.delete(); return None
    mod = set(x for x in E.S.get_model() if x > 0)
    S = [E.vars[('s', z)] in mod for z in range(n)]; F = E.decode(); E.S.delete()
    S0 = [E.vars[('h', 0, z)] in mod for z in range(n)] if d else S
    T = step_py(L, F, S)                            # re-check in Python
    assert S[L.bot] and all(not S[z] or all(S[w] for w in range(n) if le[w][z]) for z in range(n))
    assert T[m] and not S[m] and all(rk[z] <= k for z in range(n) if T[z])
    assert all(not T[z] or rk[z] < k or z == m for z in range(n)) if 'multi' not in opt else all(not ic_py(L, F, z) for z in range(n) if T[z] and rk[z] == k)
    if 'notop' not in opt: assert not step_py(L, F, T)[L.top]
    assert 'nonoic' in opt or not ic_py(L, F, m)
    if 'orbit' in opt:
        st = stages(L, F); assert all(S[z] == (st[z] is not None and st[z] <= k - 1) for z in range(n))
    if d:
        X = S0
        for i in range(d):
            if 'tighthist' in opt: assert all(rk[z] <= k - 1 - d + i for z in range(n) if X[z])
            X = step_py(L, F, X)
        assert X == S
    return S, F

if __name__ == '__main__':
    opt = [a for a in sys.argv[1:] if a in ('orbit', 'lower', 'notop', 'nonoic', 'multi', 'tighthist') or a.startswith('depth=')]
    args = [a for a in sys.argv[1:] if a not in opt]
    C = collections.Counter(); best = None
    for L in lattices(args):
        if L.height < 3: continue
        hit = None
        for m in range(L.n):
            if 1 <= L.rank[m] < L.height:
                res = query(L, m, opt)
                if res: hit = (m, res); break
        C['SAT' if hit else 'UNSAT'] += 1
        if hit and (best is None or L.n < best[0].n): best = (L, hit)
    print(f"single_local {' '.join(opt)}: {dict(C)}", flush=True)
    if best:
        L, (m, (S, F)) = best; w_ = max(x.bit_length() for x in L.S)
        nm = lambda i: '{' + ''.join(str(j) for j in range(w_) if L.S[i] >> j & 1) + '}'
        print(f"smallest: |L| = {L.n}, height {L.height}, m = {nm(m)}, S = {[nm(z) for z in range(L.n) if S[z]]}, "
              f"step S = {[nm(z) for z in range(L.n) if step_py(L, F, S)[z]]}", flush=True)
        json.dump(dict(sets=L.S, F=F, m=m, S=S), open(f"single_local{'_' + '_'.join(opt) if opt else ''}_min{L.n}.json", 'w'))
