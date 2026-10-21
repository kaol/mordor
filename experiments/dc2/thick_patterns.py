"""Per thick level-0 pattern of D on M_ω² × C₂: minimal set of level-0 cells that must be closed (selector core, eager
encoding, fibre closure at level 1), and the resulting |L1| width bound (2 · width of the closed cells)."""
import itertools, sys
import networkx as nx
from networkx.algorithms import bipartite
import dc2_lazy as d, dc2_eager as e, plane_full as P
B, T = d.B, d.T
cle = d.cle
ple = lambda p, q: cle(p[0], q[0]) and cle(p[1], q[1]) and p[2] <= q[2]

def width(C):
    le = lambda c, c2: ple(c[0], c2[0]) and ple(c[1], c2[1])
    H = nx.Graph(); top = [('L', i) for i in range(len(C))]
    H.add_nodes_from(top + [('R', i) for i in range(len(C))])
    for i, c in enumerate(C):
        for j, c2 in enumerate(C):
            if i != j and le(c, c2): H.add_edge(('L', i), ('R', j))
    return len(C) - len(bipartite.maximum_matching(H, top_nodes=top)) // 2

def patterns():
    for pp in ((0, 0), (1, 0), (1, 1)):
        for qq in ((0, 0), (1, 0), (1, 1)):
            yield {(B, B, 0): True, (B, B, 1): True, (T, T, 0): False, (T, T, 1): False,
                   (B, T, 0): bool(pp[0]), (B, T, 1): bool(pp[1]), (T, B, 0): bool(qq[0]), (T, B, 1): bool(qq[1])}

if __name__ == "__main__":
    d.CLOSED1 = P.fibre; d.SEL0 = True
    sizes = [tuple(map(int, a.split(','))) for a in sys.argv[1:]] or [(2, 2), (2, 3)]
    for pat in patterns():
        d.DPAT = pat
        Dset = {p for p, v in pat.items() if v}
        cells = [(x, y) for x in pat for y in pat if x in Dset and y not in Dset]
        union = set()
        for k, m in sizes:
            r = e.run(k, m, 2, verbose=False)
            if not isinstance(r, list): union = None; break
            union |= set(r)
        tag = ''.join('1' if pat[p] else '0' for p in [(B, T, 0), (B, T, 1), (T, B, 0), (T, B, 1)])
        if union is None: print(tag, 'SAT even with all closed?!', flush=True); continue
        print(tag, f"cells={len(cells)} closed-needed={len(union)} |L1| ≤ {2*width(sorted(union))} (all cells: {2*width(cells)})",
              sorted(((x[2], y[2]) for x, y in union)), flush=True)
