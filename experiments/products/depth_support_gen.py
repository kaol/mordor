"""Depth-2 closure test with the downset D as a solver variable (M_S × M_S × C_n).

Levels: level-0 coordinates ⊥,⊤; L1 = atoms occurring in values at cells over level-0 points; L2 = atoms occurring in
values at cells over points of level ≤ 1.  For a real witness-free (F, D) on M_ω²×C_n both L1 and L2 are finite
(finitely many cells over finitely many coordinates), and the restriction to cells over L1 ∪ L2, with value atoms
outside L1 ∪ L2 sent to one value-only atom o, is a model of instance (|L1|, |L2|) below: o ≠ every coordinate, so
neither ≤ x nor ≥ y can become true, and atom-to-atom maps are monotone on M_ω.  Hence:

    UNSAT for every (k, m)  ⟹  Cut on M_ω² × C_n.

Instance (k, m) (depth d = 2; pools=[k] gives the depth-1 analogue, which is NOT closed).  pools of length d give
depth d.  Options (all sound unless noted):
  dim        number of M_ω factors;  h  chain height of each pool element (h ≥ 2: horizontal sum of h-chains);
  closed     closure predicate replacing "closed below depth d" — sound ONLY with level semantics intact, i.e. when
             every level-0 cell is closed (an open level-0 cell would need L2 atoms in its domain);
  flat       ignore levels in the value domains (needed whenever L1/L2 are not generation levels);
  maxl2      drop constraints on pairs with more than maxl2 distinct level-≥2 atoms (relaxation: UNSAT stays sound);
  shiftT     eventually shift-equivariant window (a search ansatz, not a relaxation);
  wit, o_from, core, closesel   sanity checks and core extraction."""
import itertools, sys
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

def run(pools, nl, label="", extra=None, quiet=False, wit="both", core=False, o_from=None, dim=2, h=1, shiftT=None, closed=None, closesel=None, maxl2=None, flat=False):
    d = len(pools)
    # each pool element is a chain of height h (h = 1: atoms of M_ω; h ≥ 2: finite chains of a horizontal sum à la Ω)
    atoms = [(lv, i, j) for lv, m in enumerate(pools, start=1) for i in range(m) for j in range(h)]
    B, T = 'b', 't'
    Os = [('o', 0, j) for j in range(h)]
    lvl = lambda a: 0 if a in (B, T) else a[0]
    coords = [B, T] + atoms
    cle = lambda u, v: u == v or u == B or v == T or (u not in (B, T) and v not in (B, T) and u[:2] == v[:2] and u[2] <= v[2])
    P = [c + (l,) for c in itertools.product(coords, repeat=dim) for l in range(nl)]
    Ple = lambda p, q: all(cle(p[i], q[i]) for i in range(dim)) and p[-1] <= q[-1]
    var = {}; n = [0]
    def V(*k):
        if k not in var: n[0] += 1; var[k] = n[0]
        return var[k]
    S = Cadical153()
    dm = lambda p: V('D', p)
    covers = {p: [] for p in P}
    for p in P:
        for i in range(dim):
            for c in coords:
                if c != p[i] and cle(p[i], c) and not any(e not in (p[i], c) and cle(p[i], e) and cle(e, c) for e in coords):
                    q = list(p); q[i] = c; covers[p].append(tuple(q))
        if p[-1] + 1 < nl: covers[p].append(p[:-1] + (p[-1] + 1,))
    for p in P:
        for q in covers[p]: S.add_clause([-dm(q), dm(p)])          # downset
    bot, top = (B,) * dim + (0,), (T,) * dim + (nl - 1,)
    S.add_clause([dm(bot)]); S.add_clause([-dm(top)])
    if extra: extra(S, dm, B, T, V)
    m_ = lambda x, y: max(lvl(t) for p in (x, y) for t in p[:-1]) + 1
    def vdom(x, y):
        m = max(lvl(t) for p in (x, y) for t in p[:-1]) + 1
        free = m > (d if o_from is None else o_from) or (closed is not None and not closed(x, y, lvl)) or (closesel is not None and closesel(x, y, lvl))
        if flat: m = d                     # flat mode: levels carry no meaning, every cell may use every pool atom
        return [B, T] + [a for a in atoms if a[0] <= m] + (Os if free else [])
    hi_atoms = lambda *ps: {t[:2] for p in ps for t in p[:-1] if t not in (B, T) and t[0] >= 2}
    keep = (lambda *ps: True) if maxl2 is None else (lambda *ps: len(hi_atoms(*ps)) <= maxl2)
    if maxl2 is not None:
        P = [p for p in P if keep(p)]; Pset = set(P)
        covers = {p: [q for q in covers[p] if q in Pset] for p in P}
    for x in P:
        for y in P:
            if Ple(y, x) or not keep(x, y): continue                 # never a cell (x ∈ D, y ∉ D, y ≤ x impossible)
            g = [-dm(x), dm(y)]                                       # guard: cell iff x ∈ D ∧ y ∉ D
            vd = vdom(x, y)
            if closesel is not None and closesel(x, y, lvl) and not (m_(x, y) > d):
                for coord in range(dim):
                    for oo in Os: S.add_clause([-V('csel', x, y), -V(x, y, coord, oo)])
            for coord in range(dim):
                lits = [V(x, y, coord, a) for a in vd]
                S.add_clause(lits)
                for p_, q_ in itertools.combinations(lits, 2): S.add_clause([-p_, -q_])
            lits = [V(x, y, dim, l) for l in range(nl)]
            S.add_clause(lits)
            for p_, q_ in itertools.combinations(lits, 2): S.add_clause([-p_, -q_])
            # ¬(F ≤ x): some coordinate escapes; ¬(y ≤ F): likewise — encoded with auxiliary 'escape' literals
            sl = [-V('sel', x, y)] if core else []
            if wit != "hi":
                esc = [V(x, y, i, a) for i in range(dim) for a in vd if not cle(a, x[i])] + [V(x, y, dim, l) for l in range(nl) if l > x[-1]]
                S.add_clause(g + esc + sl)
            if wit != "lo":
                esc = [V(x, y, i, a) for i in range(dim) for a in vd if not cle(y[i], a)] + [V(x, y, dim, l) for l in range(nl) if l < y[-1]]
                S.add_clause(g + esc + sl)
            nbrs = [((x2, y), [-dm(x2), dm(y)]) for x2 in covers[x]] + [((x, y2), [-dm(x), dm(y)]) for y2 in covers[y]]
            for (x2, y2), gg in nbrs:
                if Ple(y2, x2) or not keep(x2, y2): continue
                vd2 = vdom(x2, y2)
                for coord in range(dim):
                    for a in vd:
                        if a == B: continue
                        S.add_clause(gg + [-V(x, y, coord, a), V(x2, y2, coord, T)] + ([V(x2, y2, coord, a)] if a in vd2 and a != T else []))
                for l in range(nl):
                    for l2 in range(l): S.add_clause(gg + [-V(x, y, dim, l), -V(x2, y2, dim, l2)])
    if shiftT is not None:
        # eventually shift-equivariant window (pools all 1, h = 1): σ a_l = a_{l+1} for l ≥ T, fixes lower atoms;
        # F(σc) = σF(c) and (σp ∈ D ⟺ p ∈ D) whenever c (resp. p) has an atom of level ≥ T and σc stays in range.
        assert all(m == 1 for m in pools) and h == 1
        sg = lambda a: a if a in (B, T) or a[0] < shiftT else ((a[0] + 1, 0, 0) if a[0] < d else Os[0])
        high = lambda p: any(t not in (B, T) and t[0] >= shiftT for t in p[:-1])
        inr = lambda p: all(t in (B, T) or t[0] < d for t in p[:-1])
        sp = lambda p: tuple(sg(t) for t in p[:-1]) + (p[-1],)
        for p in P:
            if high(p) and inr(p):
                S.add_clause([-dm(p), dm(sp(p))]); S.add_clause([dm(p), -dm(sp(p))])
        for x in P:
            for y in P:
                if Ple(y, x) or not (high(x) or high(y)) or not (inr(x) and inr(y)): continue
                x2, y2 = sp(x), sp(y)
                for coord in range(dim):
                    for a in vdom(x, y):
                        S.add_clause([-dm(x), dm(y), -V(x, y, coord, a), V(x2, y2, coord, sg(a))])
                        S.add_clause([-dm(x), dm(y), V(x, y, coord, a), -V(x2, y2, coord, sg(a))])
                for l in range(nl):
                    S.add_clause([-dm(x), dm(y), -V(x, y, dim, l), V(x2, y2, dim, l)])
    if closesel is not None:
        cs = {V('csel', x, y): (x, y) for x in P for y in P if ('csel', x, y) in var}
        cur = list(cs)
        if S.solve(assumptions=cur): return None
        cur = list(S.get_core()); i = 0
        while i < len(cur):
            trial = cur[:i] + cur[i + 1:]
            if not S.solve(assumptions=trial):
                c = set(S.get_core()); cur = [l for l in trial if l in c]
            else: i += 1
        return [cs[l] for l in cur]
    if core:
        sels = {V('sel', x, y): (x, y) for x in P for y in P if ('sel', x, y) in var}
        cur = list(sels)
        assert not S.solve(assumptions=cur)
        cur = [l for l in S.get_core()]
        i = 0
        while i < len(cur):
            trial = cur[:i] + cur[i + 1:]
            if not S.solve(assumptions=trial):
                c = set(S.get_core()); cur = [l for l in trial if l in c]
            else: i += 1
        return [sels[l] for l in cur]
    r = S.solve()
    if not quiet: print(f"{label} pools={pools} nl={nl}: {'SAT' if r else 'UNSAT'} [{len(P)} points, {n[0]} vars]", flush=True)
    model = set(l for l in S.get_model() if l > 0) if r else None
    return r, model, var, P

if __name__ == "__main__":
    for pools in ([1], [2], [1, 1], [2, 1], [1, 2], [2, 2]):
        run(pools, 1, "plane")
