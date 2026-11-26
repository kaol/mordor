"""§34.3z²⁸⁷ (side check from an outside pointer): the companion of the ν-layer map as a weakening of semi-commutation.
Thin model: L a finite lattice, F : L × L → L monotone, a(x) = gfp F(x, ·), b(y) = lfp F(·, y), m = lfp a, n = gfp b.
m = n iff a and b have exactly one common fixed point (`m_eq_n_iff`).
Semi-commutation b∘a ≤ a∘b says b is a-compatible (Pous). Compatible maps are closed under pointwise joins, so b ≤ t_a
(the companion of a, the largest a-compatible monotone map) iff some monotone f with f∘a ≤ a∘f satisfies b ≤ f.
Modes (each an exact SAT search over all monotone F on each lattice; SAT models replayed in Python):
  semi   SAT = b∘a ≤ a∘b and a, b have two common fixed points                (Semi-CL fails; control)
  comp   SAT = some monotone f with f∘a ≤ a∘f and b ≤ f, and two common fixed points   (CompCL fails)
  compd  SAT = some monotone g with b∘g ≤ g∘b and g ≤ a, and two common fixed points   (dual CompCL fails)
  gap    SAT = some monotone f with f∘a ≤ a∘f and b ≤ f, and NOT b∘a ≤ a∘b    (the companion hypothesis is strictly weaker)
  gapd   SAT = some monotone g with b∘g ≤ g∘b and g ≤ a, and NOT b∘a ≤ a∘b
  python3 companion_probe.py MODE (sweep N MAX | closure K M SEED CNT | tall K M SEED CNT)"""
import sys, itertools, collections
sys.path.insert(0, '../separation'); sys.path.insert(0, '.')
from amalg_sat import Enc
from tight_probe import lattices
from rstages import a_of, b_of
MODE = sys.argv[1]; args = sys.argv[2:]
MEAN = {'semi': 'b∘a ≤ a∘b and two common fixed points (Semi-CL fails)',
        'comp': 'some monotone f, f∘a ≤ a∘f, b ≤ f, and two common fixed points (CompCL fails)',
        'compd': 'some monotone g, b∘g ≤ g∘b, g ≤ a, and two common fixed points (dual CompCL fails)',
        'gap': 'some monotone f, f∘a ≤ a∘f, b ≤ f, and not b∘a ≤ a∘b (companion hypothesis strictly weaker)',
        'gapd': 'some monotone g, b∘g ≤ g∘b, g ≤ a, and not b∘a ≤ a∘b'}[MODE]
print(f'companion_probe {MODE} | per lattice, exists monotone F | SAT = {MEAN} | corpus {args}', flush=True)
C = collections.Counter(); best = None; nl = 0
for L in lattices(args):
    n = L.n; le = L.le
    if n < 3: continue
    nl += 1
    E = Enc(L, 0); S = E.S; add = S.add_clause; v = E.v
    A = lambda x, g: v('A', x, g); B = lambda y, g: v('B', y, g)
    def mono_map(name):                                   # a monotone map L -> L, one-hot
        g = lambda x, u: v(name, x, u)
        for x in range(n):
            ls = [g(x, u) for u in range(n)]; add(ls)
            for p, q in itertools.combinations(ls, 2): add([-p, -q])
        for x in range(n):
            for x2 in L.covers_up[x]:
                for u in range(n): add([-g(x, u)] + [g(x2, w) for w in range(n) if le[u][w]])
        return g
    def comp_le(P, Q, Rn, Sn):                            # (P∘Q)(x) ≤ (R∘S)(x) for all x; P,Q,R,S are (x, u) -> literal
        for x in range(n):
            for u in range(n):
                for w in range(n):
                    for u2 in range(n):
                        for w2 in range(n):
                            if not le[w][w2]:
                                add([-Q(x, u), -P(u, w), -Sn(x, u2), -Rn(u2, w2)])
    def comp_le_lit(P, Q, Rn, Sn, o):                     # o -> NOT (P∘Q ≤ R∘S): some x violates
        ls = []
        for x in range(n):
            for u in range(n):
                for w in range(n):
                    for u2 in range(n):
                        for w2 in range(n):
                            if not le[w][w2]:
                                t = v('viol', x, u, w, u2, w2); ls.append(t)
                                for lit in (Q(x, u), P(u, w), Sn(x, u2), Rn(u2, w2)): add([-t, lit])
        add([-o] + ls)
    def two_common():                                     # a, b have two distinct common fixed points
        ls = []
        for z1, z2 in itertools.combinations(range(n), 2):
            t = v('two', z1, z2); ls.append(t)
            for lit in (A(z1, z1), B(z1, z1), A(z2, z2), B(z2, z2)): add([-t, lit])
        add(ls)
    if MODE == 'semi':
        comp_le(B, A, A, B); two_common()
    elif MODE in ('comp', 'gap'):
        f = mono_map('f'); comp_le(f, A, A, f)
        for y in range(n):
            for u in range(n):
                for w in range(n):
                    if not le[u][w]: add([-B(y, u), -f(y, w)])          # b ≤ f
        if MODE == 'comp': two_common()
        else: o = v('gapo'); add([o]); comp_le_lit(B, A, A, B, o)
    elif MODE in ('compd', 'gapd'):
        g = mono_map('g'); comp_le(B, g, g, B)
        for y in range(n):
            for u in range(n):
                for w in range(n):
                    if not le[u][w]: add([-g(y, u), -A(y, w)])          # g ≤ a
        if MODE == 'compd': two_common()
        else: o = v('gapo'); add([o]); comp_le_lit(B, A, A, B, o)
    if S.solve():
        m_ = set(l for l in S.get_model() if l > 0)
        F = [[next(u for u in range(n) if E.vars[('f', x, y, u)] in m_) for y in range(n)] for x in range(n)]
        a = [a_of(L, F, x) for x in range(n)]; b = [b_of(L, F, y) for y in range(n)]
        ok = all(le[F[x][y]][F[x2][y2]] for x in range(n) for y in range(n) for x2 in range(n) for y2 in range(n) if le[x][x2] and le[y][y2])
        semi = all(le[b[a[x]]][a[b[x]]] for x in range(n)); common = [z for z in range(n) if a[z] == z and b[z] == z]
        if MODE in ('comp', 'gap'):
            fm = [next(u for u in range(n) if E.vars[('f', x, u)] in m_) for x in range(n)]
            ok = ok and all(le[fm[a[x]]][a[fm[x]]] for x in range(n)) and all(le[b[y]][fm[y]] for y in range(n))
            ok = ok and all(le[fm[x]][fm[x2]] for x in range(n) for x2 in range(n) if le[x][x2])
        if MODE in ('compd', 'gapd'):
            gm = [next(u for u in range(n) if E.vars[('g', x, u)] in m_) for x in range(n)]
            ok = ok and all(le[b[gm[x]]][gm[b[x]]] for x in range(n)) and all(le[gm[y]][a[y]] for y in range(n))
            ok = ok and all(le[gm[x]][gm[x2]] for x in range(n) for x2 in range(n) if le[x][x2])
        if MODE == 'semi': ok = ok and semi and len(common) >= 2
        if MODE in ('comp', 'compd'): ok = ok and len(common) >= 2
        if MODE in ('gap', 'gapd'): ok = ok and not semi
        assert ok, 'SAT/Python mismatch'
        C['SAT'] += 1
        print(f'  lattice n={n} h={L.height}: SAT  (common fixed points {common}, semi-commutes {semi})', flush=True)
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else:
        C['UNSAT'] += 1; print(f'  lattice n={n} h={L.height}: UNSAT', flush=True)
    S.delete()
print(MODE, args, dict(C), 'lattices', nl, 'smallest', best[0] if best else None)
if best:
    import json; json.dump(best[1], open(f'companion_{MODE}_min{best[0]}.json', 'w'))
