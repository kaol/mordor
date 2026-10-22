"""DC2 on Ω^dim × C_n (Ω = horizontal sum of finite chains of every length), direct encoding per chain configuration.

A configuration places the generated elements into chains: each chain is a tuple of levels, bottom to top
(level 1 = L1, level 2 = L2).  For a witness-free (F, D), S = {⊥, ⊤} ∪ L1 ∪ L2 is a sublattice of Ω (incomparable
elements of Ω meet at ⊥ and join at ⊤).  Retract Ω → values: elements of S are fixed; an element on a chain meeting S
goes to the gap symbol between its S-neighbours; any other element goes to o.  This is monotone, and for every
coordinate s ∈ S and element v, v ≤ s ⟺ π(v) ≤ s and s ≤ v ⟺ s ≤ π(v), so witness-freeness transfers exactly.
Closure: values at cells over {⊥,⊤} lie in {⊥,⊤} ∪ L1; at cells of level ≤ 1 in {⊥,⊤} ∪ L1 ∪ L2; at level-2 cells
anywhere (gaps, o).  UNSAT for every configuration (with every L1/L2 count) ⟹ Cut on Ω^dim × C_n.  Here: small counts."""
import itertools, sys
from pysat.solvers import Cadical153

B, T, O = 'b', 't', 'o'

def build(config, dim, nl, gaps_on=True):
    elems = [('e', c, r) for c, ch in enumerate(config) for r in range(len(ch))]
    lvl = {('e', c, r): config[c][r] for c, ch in enumerate(config) for r in range(len(ch))}
    gaps = [('g', c, j) for c, ch in enumerate(config) for j in range(len(ch) + 1)] if gaps_on else []
    coords = [B, T] + elems
    vals = coords + gaps + [O]
    def le(u, v):
        if u == v or u == B or v == T: return True
        if u == T or v == B or u == O or v == O: return False
        if u[1] != v[1]: return False
        # same chain: element rank r sits between gap r and gap r+1
        ku = 2 * u[2] + (1 if u[0] == 'e' else 0)
        kv = 2 * v[2] + (1 if v[0] == 'e' else 0)
        return ku <= kv
    return elems, lvl, coords, vals, le

def run(config, dim=2, nl=1, label="", gaps_on=True, depth=2):
    elems, lvl, coords, vals, le = build(config, dim, nl, gaps_on)
    L = lambda t: lvl.get(t, 0)
    P = [c + (l,) for c in itertools.product(coords, repeat=dim) for l in range(nl)]
    Ple = lambda p, q: all(le(p[i], q[i]) for i in range(dim)) and p[-1] <= q[-1]
    covers = {}
    for p in P:
        cs = []
        for i in range(dim):
            for c in coords:
                if c != p[i] and le(p[i], c) and not any(e not in (p[i], c) and le(p[i], e) and le(e, c) for e in coords):
                    q = list(p); q[i] = c; cs.append(tuple(q))
        if p[-1] + 1 < nl: cs.append(p[:-1] + (p[-1] + 1,))
        covers[p] = cs
    var = {}; cnt = [0]
    def V(*k):
        if k not in var: cnt[0] += 1; var[k] = cnt[0]
        return var[k]
    S = Cadical153()
    dm = lambda p: V('D', p)
    for p in P:
        for q in covers[p]: S.add_clause([-dm(q), dm(p)])
    S.add_clause([dm((B,) * dim + (0,))]); S.add_clause([-dm((T,) * dim + (nl - 1,))])
    def vdom(x, y):
        m = max(L(t) for p in (x, y) for t in p[:-1])
        if m < depth: return [B, T] + [e for e in elems if lvl[e] <= m + 1]
        return vals
    pairs = [(x, y) for x in P for y in P if not Ple(y, x)]
    pset = set(pairs)
    for x, y in pairs:
        vd = vdom(x, y); g = [-dm(x), dm(y)]
        for i in range(dim):
            lits = [V(x, y, i, a) for a in vd]; S.add_clause(lits)
            for a, b in itertools.combinations(lits, 2): S.add_clause([-a, -b])
        lits = [V(x, y, dim, l) for l in range(nl)]; S.add_clause(lits)
        for a, b in itertools.combinations(lits, 2): S.add_clause([-a, -b])
        S.add_clause(g + [V(x, y, i, a) for i in range(dim) for a in vd if not le(a, x[i])] + [V(x, y, dim, l) for l in range(nl) if l > x[-1]])
        S.add_clause(g + [V(x, y, i, a) for i in range(dim) for a in vd if not le(y[i], a)] + [V(x, y, dim, l) for l in range(nl) if l < y[-1]])
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
    r = S.solve()
    print(f"{label} config={config} dim={dim} nl={nl}: {'SAT' if r else 'UNSAT'} [{len(P)} points]", flush=True)
    return r

def configs(k, m, extra=()):
    """chain configurations with k level-1, m level-2 (and extra[i] level-(3+i)) elements, up to permuting chains"""
    seen = set()
    items = [1] * k + [2] * m + [lv for i, c in enumerate(extra) for lv in [3 + i] * c]
    # ordered set partitions of the multiset into chains (sequences); canonical = sorted tuple of chains
    def rec(rest, chains):
        if not rest:
            key = tuple(sorted(chains))
            if key not in seen: seen.add(key); out.append(key)
            return
        x = rest[0]
        for idx in range(len(chains)):
            ch = chains[idx]
            for pos in range(len(ch) + 1):
                nc = ch[:pos] + (x,) + ch[pos:]
                rec(rest[1:], chains[:idx] + [nc] + chains[idx + 1:])
        rec(rest[1:], chains + [(x,)])
    out = []
    rec(items, [])
    return out

if __name__ == "__main__":
    dim = int(sys.argv[1]); nl = int(sys.argv[2]); k = int(sys.argv[3]); m = int(sys.argv[4])
    cs = configs(k, m)
    print(f"{len(cs)} configurations", flush=True)
    for c in cs: run(c, dim, nl)
