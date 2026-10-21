"""Sound finite test for Cut on M_ω × M_ω × K (K = C_1 or C_2), and variants.

M_ω: bot, top, atoms a_0, a_1, ...  Rows and columns use only atoms a_0..a_{N-1}; values may also use one
extra atom `o` standing for every atom a_j with j >= N (the map a_j -> o is monotone and preserves all
comparisons with the truncated coordinates).  So if no bifunction on the truncated cells is monotone and
witness-free, every F on M_ω × M_ω × K with the given cut has a witness: Cut holds for that cut.
A satisfying assignment proves nothing (a witness may sit beyond the truncation)."""
import itertools, sys
from pysat.solvers import Cadical153

def solve(N, nl, Dfun, label):
    # coordinate lattice: 0 = bot, 1..N atoms, N+1 = top, N+2 = o (values only)
    BOT, TOP, O = 0, N + 1, N + 2
    def le(u, v):
        return u == v or u == BOT or v == TOP
    cvals = list(range(N + 2))
    vvals = list(range(N + 3))
    P = [(u, v, l) for u in cvals for v in cvals for l in range(nl)]
    Ple = lambda p, q: le(p[0], q[0]) and le(p[1], q[1]) and p[2] <= q[2]
    D = [p for p in P if Dfun(p, N, nl)]
    Dset = set(D)
    for p in D:
        for q in P:
            assert not (Ple(q, p) and q not in Dset), "D not a down-set"
    U = [p for p in P if p not in Dset]
    # covers in P
    def covers(p):
        out = []
        for q in P:
            if p != q and Ple(p, q) and not any(r != p and r != q and Ple(p, r) and Ple(r, q) for r in P):
                out.append(q)
        return out
    cov = {p: covers(p) for p in P}
    cells = [(x, y) for x in D for y in U]
    idx = {}
    cnt = [0]
    def var(*k):
        if k not in idx:
            cnt[0] += 1; idx[k] = cnt[0]
        return idx[k]
    S = Cadical153()
    for c in cells:
        for coord, dom in ((0, vvals), (1, vvals), (2, range(nl))):
            lits = [var(c, coord, v) for v in dom]
            S.add_clause(lits)
            for a, b in itertools.combinations(lits, 2): S.add_clause([-a, -b])
    def vle(coord, u, v):
        return u <= v if coord == 2 else (u == v or u == BOT or v == TOP)
    for (x, y) in cells:
        nbrs = [(x2, y) for x2 in cov[x] if x2 in Dset] + [(x, y2) for y2 in cov[y] if y2 not in Dset]
        for d in nbrs:
            for coord, dom in ((0, vvals), (1, vvals), (2, range(nl))):
                for u in dom:
                    for v in dom:
                        if not vle(coord, u, v):
                            S.add_clause([-var((x, y), coord, u), -var(d, coord, v)])
    # no witness: not (z <= x), not (y <= z)
    for (x, y) in cells:
        c = (x, y)
        for u in vvals:
            for v in vvals:
                for l in range(nl):
                    z = (u, v, l)
                    zle_x = vle(0, u, x[0]) and vle(1, v, x[1]) and l <= x[2]
                    yle_z = vle(0, y[0], u) and vle(1, y[1], v) and y[2] <= l
                    if zle_x or yle_z:
                        S.add_clause([-var(c, 0, u), -var(c, 1, v), -var(c, 2, l)])
    r = S.solve()
    print(f"{label} N={N}: {'SAT (no conclusion)' if r else 'UNSAT -> Cut holds for this cut'}  "
          f"[{len(cells)} cells, {cnt[0]} vars]")
    return r

if __name__ == "__main__":
    # plane cut: rows avoid top coordinates (D = M'×M')
    plane = lambda p, N, nl: p[0] != N + 1 and p[1] != N + 1
    # residue-1 thick cut on 2 layers: layer 0 rows avoid top coordinates, layer 1 rows only (bot,bot)
    thick = lambda p, N, nl: p[0] != N + 1 and p[1] != N + 1 and (p[2] == 0 or (p[0] == 0 and p[1] == 0))
    for N in range(1, 5):
        solve(N, 1, plane, "M×M, rows avoid ⊤")
    for N in range(1, 5):
        solve(N, 2, thick, "M×M×C2 thick (residue 1)")
