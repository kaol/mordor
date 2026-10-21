"""Minimal UNSAT core for the eventually shift-equivariant thick instance (which cells force a witness)."""
import itertools, sys
from pysat.solvers import Cadical153
BOT, TOP, A0 = 'b', 't', 'z'

def build(W, nl, Dfun, OFF, T):
    coords = [BOT, TOP, A0] + list(range(1, W + 1))
    cle = lambda u, v: u == v or u == BOT or v == TOP
    P = [(u, v, l) for u in coords for v in coords for l in range(nl)]
    Ple = lambda p, q: cle(p[0], q[0]) and cle(p[1], q[1]) and p[2] <= q[2]
    D = [p for p in P if Dfun(p)]; Dset = set(D); U = [p for p in P if p not in Dset]
    idxs = lambda c: [t for p in c for t in p[:2] if isinstance(t, int)]
    def canon(c):
        I = idxs(c)
        if not I or min(I) < T: return c, 0
        s = min(I) - T
        sh = lambda t: t - s if isinstance(t, int) else t
        return tuple(tuple(sh(t) if i < 2 else t for i, t in enumerate(p)) for p in c), s
    def vdom(cc):
        I = idxs(cc)
        if not I or min(I) < T: return [BOT, TOP, A0] + list(range(1, W + 1 + OFF))
        return [BOT, TOP, A0] + sorted({i + d for i in I for d in range(-OFF, OFF + 1) if i + d >= 1})
    cells = [(x, y) for x in D for y in U]
    var = {}; n = [0]
    def V(*k):
        if k not in var: n[0] += 1; var[k] = n[0]
        return var[k]
    hard, groups = [], {}
    canons = {c: canon(c) for c in cells}
    for cc in set(v[0] for v in canons.values()):
        for coord in (0, 1):
            lits = [V(cc, coord, a) for a in vdom(cc)]
            hard.append(lits); hard += [[-p, -q] for p, q in itertools.combinations(lits, 2)]
        lits = [V(cc, 2, l) for l in range(nl)]
        hard.append(lits); hard += [[-p, -q] for p, q in itertools.combinations(lits, 2)]
    shf = lambda a, s: a + s if isinstance(a, int) else a
    is_cover = lambda p, q: p != q and Ple(p, q) and not any(r not in (p, q) and Ple(p, r) and Ple(r, q) for r in P)
    cov = {p: [q for q in P if is_cover(p, q)] for p in P}
    for c in cells:
        x, y = c; cc, s = canons[c]
        for d in [(x2, y) for x2 in cov[x] if x2 in Dset] + [(x, y2) for y2 in cov[y] if y2 not in Dset]:
            dd, s2 = canons[d]
            g = ('mono', c, d); cl = []
            for coord in (0, 1):
                for a in vdom(cc):
                    for b in vdom(dd):
                        if not cle(shf(a, s), shf(b, s2)):
                            cl.append([-V(cc, coord, a), -V(dd, coord, b)])
            for l in range(nl):
                for l2 in range(l):
                    cl.append([-V(cc, 2, l), -V(dd, 2, l2)])
            groups[g] = cl
    for c in cells:
        x, y = c; cc, s = canons[c]; cl = []
        for a in vdom(cc):
            for b in vdom(cc):
                for l in range(nl):
                    z = (shf(a, s), shf(b, s), l)
                    if (cle(z[0], x[0]) and cle(z[1], x[1]) and l <= x[2]) or \
                       (cle(y[0], z[0]) and cle(y[1], z[1]) and y[2] <= l):
                        cl.append([-V(cc, 0, a), -V(cc, 1, b), -V(cc, 2, l)])
        groups[('nw', c)] = cl
    return hard, groups, n

def core(W, nl, Dfun, OFF=1, T=2):
    hard, groups, n = build(W, nl, Dfun, OFF, T)
    sel = {}
    S = Cadical153()
    for c in hard: S.add_clause(c)
    for g, cls in groups.items():
        n[0] += 1; sel[g] = n[0]
        for c in cls: S.add_clause(c + [-sel[g]])
    assert not S.solve(assumptions=list(sel.values()))
    cur = [g for g in groups if sel[g] in set(S.get_core())]
    # deletion-based minimization
    i = 0
    while i < len(cur):
        trial = cur[:i] + cur[i + 1:]
        if not S.solve(assumptions=[sel[g] for g in trial]):
            cc = set(S.get_core()); cur = [g for g in trial if sel[g] in cc]
        else:
            i += 1
    return cur

if __name__ == "__main__":
    thick = lambda p: p[0] != TOP and p[1] != TOP and (p[2] == 0 or (p[0] == BOT and p[1] == BOT))
    plane = lambda p: p[0] != TOP and p[1] != TOP
    for name, Df, nl in (("plane", plane, 1), ("thick", thick, 2)):
        cur = core(3, nl, Df)
        nwc = [g[1] for g in cur if g[0] == 'nw']
        mono = [g for g in cur if g[0] == 'mono']
        print(f"{name}: core has {len(nwc)} no-witness cells and {len(mono)} monotonicity links")
        for c in nwc: print("   nw", c)
