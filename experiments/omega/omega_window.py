"""Window abstraction of whole-chain closure on Ω^dim × C_n, uniform in chain length (§34.3z¹⁰).

Chains are token lists, bottom to top:
  ('gen', 1)  generated L1 element (a level-0 value), coordinate of level 1
  ('nb', 1)   chain neighbour kept as a coordinate: an S1 element (its whole chain is S1) but not a level-0 value
  ('gap', 1)  the elements of an L1 chain between kept coordinates (possibly none): value-only, allowed at level ≥ 1
  ('gen', 2)  L2 element, coordinate of level 2 (L2 = new elements at level-1 cells; never on an L1 chain)
  ('gap', 2)  elements of an L2 chain between kept coordinates: value-only, frontier (level-2 cells) only
Other chains: o (frontier only).  Soundness: in a real witness-free (F, D), keep the generated elements and their
chosen neighbours; every other element of a represented chain goes to its gap symbol (monotone; exact against every
kept coordinate).  Values at level-1 cells over kept coordinates lie in whole L1 chains (kept or gap) ∪ L2 by the
definition of L2.  Gaps may be empty in reality, which only relaxes.  So UNSAT of a window configuration excludes
every counterexample whose generated elements sit in chains of that local shape, for all chain lengths."""
import itertools, sys
from pysat.solvers import Cadical153

B, T, O = 'b', 't', 'o'

def run(config, dim=2, nl=1, label="", verbose=True, core=False, possible=None, witsel=None, span=None, dfix=None):
    # config: tuple of chains; chain: tuple of (kind, level)
    toks = [(c, r, kind, lv) for c, ch in enumerate(config) for r, (kind, lv) in enumerate(ch)]
    coords = [B, T] + [(c, r) for c, r, kind, lv in toks if kind != 'gap']
    info = {(c, r): (kind, lv) for c, r, kind, lv in toks}
    vals_all = [B, T] + [(c, r) for c, r, _, _ in toks] + [O]
    def le(u, v):
        if u == v or u == B or v == T: return True
        if u == T or v == B or u == O or v == O: return False
        return u[0] == v[0] and u[1] <= v[1]
    clv = lambda t: 0 if t in (B, T) else info[t][1]
    P = [c + (l,) for c in itertools.product(coords, repeat=dim) for l in range(nl)]
    def spanof(*ps):
        q = [t[1] for p in ps for t in p[:-1] if t not in (B, T) and info[t][1] == 2]
        return max(q) - min(q) if q else 0
    if span is not None: P = [p for p in P if spanof(p) <= span]
    Ple = lambda p, q: all(le(p[i], q[i]) for i in range(dim)) and p[-1] <= q[-1]
    covers = {}
    Pset_ = set(P)
    for p in P:
        cs = []
        for i in range(dim):
            for c in coords:
                if c != p[i] and le(p[i], c) and not any(e not in (p[i], c) and le(p[i], e) and le(e, c) for e in coords):
                    q = list(p); q[i] = c; cs.append(tuple(q))
        if p[-1] + 1 < nl: cs.append(p[:-1] + (p[-1] + 1,))
        covers[p] = [q for q in cs if q in Pset_]
    def vdom(x, y):
        m = max(clv(t) for p in (x, y) for t in p[:-1])
        if m == 0: return [B, T] + [t for t in vals_all if t not in (B, T, O) and info[t] == ('gen', 1)]
        if m == 1: return [B, T] + [t for t in vals_all if t not in (B, T, O) and (info[t][1] == 1 or info[t] == ('gen', 2))]
        return vals_all
    var = {}; cnt = [0]
    def V(*k):
        if k not in var: cnt[0] += 1; var[k] = cnt[0]
        return var[k]
    S = Cadical153()
    dm = lambda p: V('D', p)
    for p in P:
        for q in covers[p]: S.add_clause([-dm(q), dm(p)])
    S.add_clause([dm((B,) * dim + (0,))]); S.add_clause([-dm((T,) * dim + (nl - 1,))])
    if dfix:
        for p, v in dfix.items():
            if p in Pset_: S.add_clause([dm(p) if v else -dm(p)])
    pairs = [(x, y) for x in P for y in P if not Ple(y, x) and (span is None or spanof(x, y) <= span)]
    pset = set(pairs)
    for x, y in pairs:
        vd = vdom(x, y); g = [-dm(x), dm(y)]
        for i in range(dim):
            lits = [V(x, y, i, a) for a in vd]; S.add_clause(lits)
            for a, b in itertools.combinations(lits, 2): S.add_clause([-a, -b])
        lits = [V(x, y, dim, l) for l in range(nl)]; S.add_clause(lits)
        for a, b in itertools.combinations(lits, 2): S.add_clause([-a, -b])
        if witsel is not None and not witsel(x, y): continue_wit = True
        else: continue_wit = False
        sl = [-V('sel', x, y)] if core else []
        if not continue_wit:
            S.add_clause(g + sl + [V(x, y, i, a) for i in range(dim) for a in vd if not le(a, x[i])] + [V(x, y, dim, l) for l in range(nl) if l > x[-1]])
            S.add_clause(g + sl + [V(x, y, i, a) for i in range(dim) for a in vd if not le(y[i], a)] + [V(x, y, dim, l) for l in range(nl) if l < y[-1]])
        nb = [((x2, y), [-dm(x2), dm(y)]) for x2 in covers[x]] + [((x, y2), [-dm(x), dm(y)]) for y2 in covers[y]]
        for c2, gg in nb:
            if c2 not in pset: continue
            vd2 = vdom(*c2)
            for i in range(dim):
                for a in vd:
                    for b in vd2:
                        if not le(a, b): S.add_clause(gg + [-V(x, y, i, a), -V(*c2, i, b)])
            for l in range(nl):
                for l2 in range(l): S.add_clause(gg + [-V(x, y, dim, l), -V(*c2, dim, l2)])
    if possible is not None:
        # possible values at the selected pairs, over all models (cell condition assumed)
        out = {}
        for x, y in pairs:
            if not possible(x, y): continue
            for i in range(dim + 1):
                dom_i = vdom(x, y) if i < dim else list(range(nl))
                out[(x, y, i)] = [a for a in dom_i if S.solve(assumptions=[dm(x), -dm(y), V(x, y, i, a)])]
        return out
    if core:
        sels = {V('sel', x, y): (x, y) for x, y in pairs}
        cur = list(sels)
        if S.solve(assumptions=cur): return None
        cur = list(S.get_core()); i = 0
        while i < len(cur):
            trial = cur[:i] + cur[i + 1:]
            if not S.solve(assumptions=trial): c = set(S.get_core() or []); cur = [l for l in trial if l in c]
            else: i += 1
        return [sels[l] for l in cur]
    r = S.solve()
    if verbose: print(f"{label} {fmt(config)} nl={nl}: {'SAT' if r else 'UNSAT'} [{len(P)} points]", flush=True)
    return r

def fmt(config):
    sym = {('gen', 1): 'E', ('nb', 1): 'n', ('gap', 1): '~', ('gen', 2): 'B', ('gap', 2): '-', ('nb', 2): 'm'}
    return ' | '.join(''.join(sym[t] for t in ch) for ch in config)

G1, N1, Z1, G2, Z2 = ('gen', 1), ('nb', 1), ('gap', 1), ('gen', 2), ('gap', 2)

def side_options(k):
    """what lies on one side of a generated element within window k: chain end, or j ≤ k neighbours then end/gap"""
    opts = [()]
    for j in range(1, k + 1):
        opts.append((N1,) * j)                # j neighbours, then the chain ends
    opts.append((N1,) * k + (Z1,))         # k neighbours, then more (gap), read outward from the element
    return opts

def l1_chain_single(k):
    out = []
    for lo in side_options(k):
        for hi in side_options(k):
            out.append(tuple(reversed(lo)) + (G1,) + hi)
    return out

if __name__ == "__main__":
    k = int(sys.argv[1]); nl = int(sys.argv[2])
    l2 = (Z2, G2, Z2)
    for ch in l1_chain_single(k):
        run((ch, l2), nl=nl, label=f"window k={k}")
