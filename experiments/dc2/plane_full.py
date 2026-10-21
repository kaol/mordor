"""Exhaustive DC2 check on M_ω² × C_n for small n via dc2_eager, using sound bounds:
|L1| ≤ bounds.l1_bound(n) (depth-0 relaxation), |L2| ≤ 2·width(level-1 pairs over {⊥, ⊤} ∪ L1) (monotone chains meet
at most one atom per coordinate).  UNSAT for every k ≤ |L1| bound at m = its |L2| bound ⟹ DC2 (hence Cut) on M_ω² × C_n."""
import sys, time, networkx as nx
from networkx.algorithms import bipartite
import dc2_lazy as d, dc2_eager as e, bounds

def l2_width_bound(k, n):
    d.LAYERS = list(range(n))
    I = d.Inst(k, 0, n)
    lev0 = lambda p: p[0] in (d.B, d.T) and p[1] in (d.B, d.T)
    C = [(x, y) for x in I.P1 for y in I.P1 if not I.ple(y, x) and not (lev0(x) and lev0(y))
         and (d.CLOSED1 is None or d.CLOSED1(x, y))]
    le = lambda c, c2: I.ple(c[0], c2[0]) and I.ple(c[1], c2[1])
    G = nx.DiGraph()
    top = [('L', i) for i in range(len(C))]
    H = nx.Graph(); H.add_nodes_from(top + [('R', i) for i in range(len(C))])
    for i, c in enumerate(C):
        for j, c2 in enumerate(C):
            if i != j and le(c, c2): H.add_edge(('L', i), ('R', j))
    M = bipartite.maximum_matching(H, top_nodes=top)
    return 2 * (len(C) - len(M) // 2)

def fibre(x, y):
    """level-1 fibre cells: at most one atom in total, or one atom on each side, the same atom at the same index"""
    ax = [(i, t) for i, t in enumerate(x[:2]) if t not in (d.B, d.T)]
    ay = [(i, t) for i, t in enumerate(y[:2]) if t not in (d.B, d.T)]
    if len(ax) + len(ay) <= 1: return True
    return len(ax) == 1 and len(ay) == 1 and ax == ay

if __name__ == "__main__":
    n = int(sys.argv[1])
    if len(sys.argv) > 2 and sys.argv[2] == 'fibre': d.CLOSED1 = fibre
    K = bounds.l1_bound(n)
    print(f"n={n}: |L1| ≤ {K}", flush=True)
    for k in range(0, K + 1):
        m = l2_width_bound(k, n) if k else 0
        print(f"  k={k}: |L2| ≤ {m}", flush=True)
        r = e.run(k, m, n)
        if r: print("  SAT — DC2 check fails at this (k, m)", flush=True)
