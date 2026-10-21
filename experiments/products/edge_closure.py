"""Edge-closure test on M_ω² × C_n (§34.3z⁶) — NEGATIVE: SAT for every m ≥ 1, already on the plane.

A first version gave UNSAT throughout; it was unsound (level-0 cells could not use L2 atoms, but in this setting the
L2 atoms are arbitrary).  With every non-closed cell allowed all of {⊥, ⊤, a} ∪ L2 ∪ {o} (flat=True) the instances are
SAT, so no single-atom local certificate of this shape exists.  Kept as the record of that test.

Fix any atom a.  K = 'edge cells over a': pairs (x, y) of points over {⊥, a, ⊤}² × C_n with x < y, x and y differing in
exactly one Q-coordinate, the other Q-coordinate common, at least one of x, y containing a, and x layer ≤ y layer —
precisely the closed positions in the minimal selector core.  L2(a) = atoms ≠ a occurring in F-values at K-cells.

For a real witness-free (F, D) restrict to cells over {⊥, ⊤, a} ∪ L2(a) and send every other value atom to one
value-only atom o.  Values on K lie in {⊥, ⊤, a} ∪ L2(a) by definition; all other cells may use o.  So
    UNSAT for every m ≤ |L2| bound  ⟹  Cut on M_ω² × C_n.
The |L2| bound: in M_ω a monotone chain of values meets at most one atom per coordinate, so per coordinate the
number of atoms on K is at most the width of K (as a subposet of cells, over all D at once)."""
import itertools, sys
import networkx as nx
from networkx.algorithms import bipartite
from depth_support_gen import run

L = lambda t: 0 if t in ('b', 't') else t[0]

def is_edge(x, y, a1=lambda t: L(t) == 1):
    Q = range(len(x) - 1)
    diff = [i for i in Q if x[i] != y[i]]
    if len(diff) != 1: return False
    if not any(a1(t) for p in (x, y) for t in p[:-1]): return False
    if any(L(t) > 1 for p in (x, y) for t in p[:-1]): return False
    i = diff[0]
    cle = lambda u, v: u == v or u == 'b' or v == 't'
    return cle(x[i], y[i]) and x[-1] <= y[-1]

def width(n, dim=2):
    A = (1, 0, 0)
    cs = ['b', 't', A]
    P = [c + (l,) for c in itertools.product(cs, repeat=dim) for l in range(n)]
    cle = lambda u, v: u == v or u == 'b' or v == 't'
    Ple = lambda p, q: all(cle(p[i], q[i]) for i in range(dim)) and p[-1] <= q[-1]
    C = [(x, y) for x in P for y in P if is_edge(x, y) and not Ple(y, x)]
    le = lambda c, d: Ple(c[0], d[0]) and Ple(c[1], d[1])
    G = nx.Graph(); top = [('L', i) for i in range(len(C))]
    G.add_nodes_from(top + [('R', i) for i in range(len(C))])
    for i, c in enumerate(C):
        for j, d in enumerate(C):
            if i != j and le(c, d): G.add_edge(('L', i), ('R', j))
    M = bipartite.maximum_matching(G, top_nodes=top)
    return len(C), len(C) - len(M) // 2

if __name__ == "__main__":
    n = int(sys.argv[1]); dim = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    k, w = width(n, dim)
    bound = dim * w
    print(f"n={n} dim={dim}: |K|={k}, width={w}, |L2| ≤ {bound}", flush=True)
    for m in range(0, bound + 1):
        # pools [1, m]: depth d = 2, so a cell is closed iff it is in K (level-0 cells are never in K)
        r, *_ = run([1, m], n, f"edge-closure n={n} m={m}", dim=dim, closed=lambda x, y, lvl: is_edge(x, y), flat=True)
        if r: print("  SAT: edge closure does not suffice at this size", flush=True)
