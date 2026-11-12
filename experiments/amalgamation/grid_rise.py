"""BoundaryGridRise, exactly (log §34.3z¹⁵⁹; brief "Rise at height four via two-sided boundary orbits").

Rigid F (a(⊥) = ⊥, b(⊤) = ⊤, diagonal fixing only ⊥, ⊤). Boundary orbits u₀ = ⊥, u_{i+1} = F(u_i, ⊤) (↑ b(⊤) = ⊤) and
d₀ = ⊤, d_{j+1} = F(⊥, d_j) (↓ a(⊥) = ⊥); grid z_ij = F(u_i, d_j). Candidate sets:
  grid0 : {u_i, d_j, z_ij}
  grid  : {u_i, d_j, z_ij, a(u_i), b(d_j)}            (the brief's S_H)
  grid+ : grid ∪ {a(z_ij), b(z_ij)}
  beta  : grid+ ∪ {β^k(⊥)}, β(c) = ⋁{y : b(y) ≤ c} (the b-part of kstep)
  ideal : grid+ ∪ {r_k}, r_{k+1} = r_k ⊔ a(r_k) ⊔ β(r_k) (the ideal orbit `rk`)
  betaonly / idealonly : only those chains
Query: a rigid F such that no element of the set is a good riser (good: x ∈ R_{h(x)}; riser: x < a(x)).
SAT = counterexample to BoundaryGridRise for that set (re-checked in Python).
  python3 grid_rise.py SET [hmax=h] (sweep P NMAX | closure K M SEED COUNT | h3 K M SEED COUNT)
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from rstages import stages, a_of, b_of
from rise_sat import lattices

def terms_py(L, F):
    n = L.n; bot, top = L.bot, L.top
    u = [bot]
    while u[-1] != top: u.append(F[u[-1]][top])
    d = [top]
    while d[-1] != bot: d.append(F[bot][d[-1]])
    return u, d

def query(L, kind):
    n = L.n; le = L.le; rk = L.rank; H = L.height; bot, top = L.bot, L.top
    E = Enc(L, H); r = lambda j, z: E.v('r', j, z); f = lambda x, y, v: E.v('f', x, y, v)
    A = lambda x, g: E.v('A', x, g); B = lambda y, g: E.v('B', y, g)
    E.S.add_clause([A(bot, bot)]); E.S.add_clause([B(top, top)])
    for c in range(n):
        if c not in (bot, top): E.S.add_clause([-f(c, c, c)])
    U = lambda i, z: E.v('U', i, z); D = lambda j, z: E.v('D', j, z)
    for z in range(n):
        E.S.add_clause([U(0, z)] if z == bot else [-U(0, z)]); E.S.add_clause([D(0, z)] if z == top else [-D(0, z)])
    for i in range(H):
        for w in range(n):
            lu, ld = [], []
            for z in range(n):
                o = E.v('Us', i, z, w); E.iff_and(o, [U(i, z), f(z, top, w)]); lu.append(o)
                o = E.v('Ds', i, z, w); E.iff_and(o, [D(i, z), f(bot, z, w)]); ld.append(o)
            E.iff_or(U(i + 1, w), lu); E.iff_or(D(i + 1, w), ld)
    def forbid(lits_of_z):                      # term = z  ⇒  z is not a good riser
        for z in range(n):
            for g in range(n):
                if g != z and le[z][g]:
                    for lit in lits_of_z(z): E.S.add_clause([-lit, -r(rk[z], z), -A(z, g)])
    I = range(H + 1)
    only = kind in ('betaonly', 'idealonly')
    if not only: forbid(lambda z: [U(i, z) for i in I] + [D(j, z) for j in I])
    Z = lambda i, j, w: E.v('Z', i, j, w)
    for i in I:
        for j in I:
            for w in range(n):
                lits = []
                for x in range(n):
                    for y in range(n):
                        o = E.v('Zs', i, j, x, y, w); E.iff_and(o, [U(i, x), D(j, y), f(x, y, w)]); lits.append(o)
                E.iff_or(Z(i, j, w), lits)
    if not only: forbid(lambda z: [Z(i, j, z) for i in I for j in I])
    if kind in ('grid', 'grid+', 'beta', 'ideal'):
        for i in I:
            for z in range(n):
                for g in range(n):
                    o = E.v('aU', i, g); E.S.add_clause([-U(i, z), -A(z, g), o])
        for j in I:
            for z in range(n):
                for g in range(n):
                    o = E.v('bD', j, g); E.S.add_clause([-D(j, z), -B(z, g), o])
        forbid(lambda g: [E.v('aU', i, g) for i in I] + [E.v('bD', j, g) for j in I])
    if kind in ('grid+', 'beta', 'ideal'):
        for i in I:
            for j in I:
                for z in range(n):
                    for g in range(n):
                        E.S.add_clause([-Z(i, j, z), -A(z, g), E.v('aZ', g)]); E.S.add_clause([-Z(i, j, z), -B(z, g), E.v('bZ', g)])
        forbid(lambda g: [E.v('aZ', g), E.v('bZ', g)])
    if kind in ('beta', 'ideal', 'betaonly', 'idealonly'):
        jn = L.join
        sB = lambda c, y: E.v('sB', c, y)                     # b(y) ≤ c
        for c in range(n):
            for y in range(n): E.iff_or(sB(c, y), [B(y, g) for g in range(n) if le[g][c]])
        J = lambda c, w: E.v('beta', c, w)                    # β(c) = w
        for c in range(n):
            E.S.add_clause([J(c, w) for w in range(n)])
            for w in range(n):
                for y in range(n):
                    if not le[y][w]: E.S.add_clause([-J(c, w), -sB(c, y)])
                for w2 in range(n):
                    if not le[w][w2]: E.S.add_clause([-J(c, w)] + [sB(c, y) for y in range(n) if not le[y][w2]])
        C = lambda k, z: E.v('C', k, z)
        for z in range(n): E.S.add_clause([C(0, z)] if z == bot else [-C(0, z)])
        for k in range(H):
            for w in range(n):
                lits = []
                for c in range(n):
                    if kind.startswith('beta'):
                        for b2 in range(n):
                            if b2 == w: o = E.v('Cs', k, c, b2); E.iff_and(o, [C(k, c), J(c, b2)]); lits.append(o)
                    else:
                        for g in range(n):
                            for b2 in range(n):
                                if jn[jn[c][g]][b2] == w:
                                    o = E.v('Cs', k, c, g, b2); E.iff_and(o, [C(k, c), A(c, g), J(c, b2)]); lits.append(o)
                E.iff_or(C(k + 1, w), lits)
        forbid(lambda z: [C(k, z) for k in range(H + 1)])
    if not E.S.solve(): E.S.delete(); return False
    F = E.decode(); E.S.delete(); st = stages(L, F)
    A_ = [a_of(L, F, x) for x in range(n)]; B_ = [b_of(L, F, y) for y in range(n)]
    good_riser = lambda z: st[z] is not None and st[z] <= rk[z] and le[z][A_[z]] and A_[z] != z
    u, d = terms_py(L, F)
    S = set(u) | set(d) | {F[x][y] for x in u for y in d}
    if kind in ('grid', 'grid+'): S |= {A_[x] for x in u} | {B_[y] for y in d}
    if kind in ('grid+', 'beta', 'ideal'): S |= {A_[F[x][y]] for x in u for y in d} | {B_[F[x][y]] for x in u for y in d}
    if kind in ('beta', 'ideal', 'betaonly', 'idealonly'):
        beta = lambda c: next(w for w in range(n) if all(le[y][w] for y in range(n) if le[B_[y]][c]) and all(le[w][w2] for w2 in range(n) if all(le[y][w2] for y in range(n) if le[B_[y]][c])))
        c = bot; ch = [c]
        for _ in range(H):
            c = beta(c) if kind.startswith('beta') else L.join[L.join[c][A_[c]]][beta(c)]; ch.append(c)
        S = (S | set(ch)) if kind in ('beta', 'ideal') else set(ch)
    assert A_[bot] == bot and B_[top] == top and not any(good_riser(z) for z in S)
    return F

if __name__ == '__main__':
    kind = sys.argv[1]; hmax = next((int(a[5:]) for a in sys.argv if a.startswith('hmax=')), None)
    args = [a for a in sys.argv[2:] if not a.startswith('hmax=')]
    C = collections.Counter(); best = None
    for L in lattices(args):
        if L.height < 1 or (hmax is not None and L.height > hmax): continue
        F = query(L, kind)
        C[('counterexample' if F else 'none', L.height)] += 1
        if F and (best is None or L.n < best[0].n): best = (L, F)
    print(f"{kind}: {dict(sorted(C.items()))}" + (f"; smallest |L| = {best[0].n}, height {best[0].height}" if best else ''), flush=True)
    if best: json.dump(dict(sets=best[0].S, F=best[1]), open(f'gridrise_{kind}_min{best[0].n}.json', 'w'))
