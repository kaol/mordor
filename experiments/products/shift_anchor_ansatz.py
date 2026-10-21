"""Shift ansatz with a distinguished anchor branch.

M: bot, top, atom a0 (fixed, free for anchor values), atoms a_i (i >= 1) shifted by s: a_i -> a_{i+1}.
F commutes with s on all cells (s fixes bot, top, a0), values use a0 or atoms within OFF of the cell's
shifted atom indices.  Cells: atoms among a0 and a_1..a_W.  UNSAT => no such F at all."""
import itertools, sys
from pysat.solvers import Cadical153
BOT, TOP, A0 = 'b', 't', 'z'

def run(W, nl, Dfun, OFF=1, label="", T=None):
    coords = [BOT, TOP, A0] + list(range(1, W + 1))
    cle = lambda u, v: u == v or u == BOT or v == TOP
    P = [(u, v, l) for u in coords for v in coords for l in range(nl)]
    Ple = lambda p, q: cle(p[0], q[0]) and cle(p[1], q[1]) and p[2] <= q[2]
    D = [p for p in P if Dfun(p)]; Dset = set(D); U = [p for p in P if p not in Dset]
    idxs = lambda c: [t for p in c for t in p[:2] if isinstance(t, int)]
    def canon(c):
        I = idxs(c)
        if T is not None and (not I or min(I) < T):
            return c, 0
        s = (min(I) - (T if T is not None else 1)) if I else 0
        sh = lambda t: t - s if isinstance(t, int) else t
        return tuple(tuple(sh(t) if i < 2 else t for i, t in enumerate(p)) for p in c), s
    def vdom(cc):
        I = idxs(cc)
        if T is not None and (not I or min(I) < T):
            return [BOT, TOP, A0] + list(range(1, W + 1 + OFF))
        atoms = sorted({i + d for i in I for d in range(-OFF, OFF + 1) if i + d >= 1})
        return [BOT, TOP, A0] + atoms
    cells = [(x, y) for x in D for y in U]
    var = {}; n = [0]
    def V(*k):
        if k not in var: n[0] += 1; var[k] = n[0]
        return var[k]
    S = Cadical153()
    canons = {c: canon(c) for c in cells}
    for cc in set(v[0] for v in canons.values()):
        for coord in (0, 1):
            lits = [V(cc, coord, a) for a in vdom(cc)]
            S.add_clause(lits)
            for p, q in itertools.combinations(lits, 2): S.add_clause([-p, -q])
        lits = [V(cc, 2, l) for l in range(nl)]
        S.add_clause(lits)
        for p, q in itertools.combinations(lits, 2): S.add_clause([-p, -q])
    shf = lambda a, s: a + s if isinstance(a, int) else a
    is_cover = lambda p, q: p != q and Ple(p, q) and not any(r not in (p, q) and Ple(p, r) and Ple(r, q) for r in P)
    cov = {p: [q for q in P if is_cover(p, q)] for p in P}
    for c in cells:
        x, y = c; cc, s = canons[c]
        for d in [(x2, y) for x2 in cov[x] if x2 in Dset] + [(x, y2) for y2 in cov[y] if y2 not in Dset]:
            dd, s2 = canons[d]
            for coord in (0, 1):
                for a in vdom(cc):
                    for b in vdom(dd):
                        if not cle(shf(a, s), shf(b, s2)):
                            S.add_clause([-V(cc, coord, a), -V(dd, coord, b)])
            for l in range(nl):
                for l2 in range(l):
                    S.add_clause([-V(cc, 2, l), -V(dd, 2, l2)])
    for c in cells:
        x, y = c; cc, s = canons[c]
        for a in vdom(cc):
            for b in vdom(cc):
                for l in range(nl):
                    z = (shf(a, s), shf(b, s), l)
                    if (cle(z[0], x[0]) and cle(z[1], x[1]) and l <= x[2]) or \
                       (cle(y[0], z[0]) and cle(y[1], z[1]) and y[2] <= l):
                        S.add_clause([-V(cc, 0, a), -V(cc, 1, b), -V(cc, 2, l)])
    r = S.solve()
    print(f"{label} W={W}: {'SAT' if r else 'UNSAT'} [{len(cells)} cells]", flush=True)
    return r

if __name__ == "__main__":
    plane = lambda p: p[0] != TOP and p[1] != TOP
    thick = lambda p: p[0] != TOP and p[1] != TOP and (p[2] == 0 or (p[0] == BOT and p[1] == BOT))
    for W in range(2, 6): run(W, 1, plane, 1, "plane T=2", T=2)
    for W in range(2, 5): run(W, 2, thick, 1, "thick T=2", T=2)


def thick_variants(W=4, T=2, OFF=1):
    Qp = lambda p: p[0] != TOP and p[1] != TOP
    V = {
        "D0=no-top, D1={bot}": lambda p: Qp(p) and (p[2] == 0 or (p[0] == BOT and p[1] == BOT)),
        "D0=no-top+(bot,top), D1={bot}": lambda p: (Qp(p) or (p[0] == BOT)) and (p[2] == 0 or (p[0] == BOT and p[1] == BOT)),
        "D0=no-top, D1=first-bot": lambda p: Qp(p) and (p[2] == 0 or p[0] == BOT),
        "D0=first-not-top, D1=no-top": lambda p: p[0] != TOP and (p[2] == 0 or Qp(p)),
        "D0=no-top, D1={bot,a0}^2": lambda p: Qp(p) and (p[2] == 0 or (p[0] in (BOT, A0) and p[1] in (BOT, A0))),
        "D0=first-not-top, D1=first-bot,no-top": lambda p: p[0] != TOP and (p[2] == 0 or (p[0] == BOT and p[1] != TOP)),
    }
    for name, Df in V.items():
        run(W, 2, Df, OFF, f"{name} T={T}", T=T)
