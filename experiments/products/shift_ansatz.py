"""Shift-equivariant ansatz on M_Z × M_Z × C_n.

M_Z: bot, top, atoms a_i (i ∈ Z); the shift a_i -> a_{i+1} is an automorphism.  We look for F with
F(shift c) = shift F(c), values using atoms within distance OFF of the cell's atom indices, monotone and
witness-free on all cells whose atom indices span fewer than W positions.  UNSAT => no such equivariant F
(with that offset bound) exists at all.  SAT proves nothing by itself."""
import itertools, sys
from pysat.solvers import Cadical153

BOT, TOP = 'b', 't'

def run(W, nl, Dfun, OFF=1, label=""):
    coords = [BOT, TOP] + list(range(W))
    def cle(u, v):
        return u == v or u == BOT or v == TOP
    P = [(u, v, l) for u in coords for v in coords for l in range(nl)]
    Ple = lambda p, q: cle(p[0], q[0]) and cle(p[1], q[1]) and p[2] <= q[2]
    D = [p for p in P if Dfun(p, nl)]
    Dset = set(D); U = [p for p in P if p not in Dset]
    def idxs(c):
        return [t for p in c for t in p[:2] if isinstance(t, int)]
    def canon(c):
        I = idxs(c)
        s = min(I) if I else 0
        sh = lambda t: t - s if isinstance(t, int) else t
        return tuple(tuple(sh(t) if i < 2 else t for i, t in enumerate(p)) for p in c), s
    cells = [(x, y) for x in D for y in U]
    # value domain in the canonical frame
    def vdom(cc):
        I = idxs(cc)
        atoms = sorted({i + d for i in I for d in range(-OFF, OFF + 1)}) if I else []
        return [BOT, TOP] + atoms
    var = {}; n = [0]
    def V(*k):
        if k not in var: n[0] += 1; var[k] = n[0]
        return var[k]
    S = Cadical153()
    canons = {}
    for c in cells:
        cc, s = canon(c)
        canons[c] = (cc, s)
    for cc in set(v[0] for v in canons.values()):
        dom = vdom(cc)
        for coord in (0, 1):
            lits = [V(cc, coord, a) for a in dom]
            S.add_clause(lits)
            for p, q in itertools.combinations(lits, 2): S.add_clause([-p, -q])
        lits = [V(cc, 2, l) for l in range(nl)]
        S.add_clause(lits)
        for p, q in itertools.combinations(lits, 2): S.add_clause([-p, -q])
    def shifted(a, s):
        return a + s if isinstance(a, int) else a
    # covers
    def is_cover(p, q):
        return p != q and Ple(p, q) and not any(r not in (p, q) and Ple(p, r) and Ple(r, q) for r in P)
    cov = {p: [q for q in P if is_cover(p, q)] for p in P}
    for c in cells:
        x, y = c
        nb = [(x2, y) for x2 in cov[x] if x2 in Dset] + [(x, y2) for y2 in cov[y] if y2 not in Dset]
        cc, s = canons[c]
        for d in nb:
            dd, s2 = canons[d]
            for coord in (0, 1):
                for a in vdom(cc):
                    for b in vdom(dd):
                        if not cle(shifted(a, s), shifted(b, s2)):
                            S.add_clause([-V(cc, coord, a), -V(dd, coord, b)])
            for l in range(nl):
                for l2 in range(nl):
                    if l > l2: S.add_clause([-V(cc, 2, l), -V(dd, 2, l2)])
    for c in cells:
        x, y = c
        cc, s = canons[c]
        dom = vdom(cc)
        for a in dom:
            for b in dom:
                for l in range(nl):
                    z = (shifted(a, s), shifted(b, s), l)
                    zx = cle(z[0], x[0]) and cle(z[1], x[1]) and l <= x[2]
                    yz = cle(y[0], z[0]) and cle(y[1], z[1]) and y[2] <= l
                    if zx or yz:
                        S.add_clause([-V(cc, 0, a), -V(cc, 1, b), -V(cc, 2, l)])
    r = S.solve()
    print(f"{label} W={W} OFF={OFF}: {'SAT' if r else 'UNSAT'}  [{len(cells)} cells, {n[0]} vars]", flush=True)
    return r

if __name__ == "__main__":
    plane = lambda p, nl: p[0] != TOP and p[1] != TOP
    thick = lambda p, nl: p[0] != TOP and p[1] != TOP and (p[2] == 0 or (p[0] == BOT and p[1] == BOT))
    for W in range(1, 6):
        run(W, 1, plane, 1, "plane")
    for W in range(1, 5):
        run(W, 2, thick, 1, "thick")
