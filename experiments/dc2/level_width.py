"""A pool-size bound for DC2 (log §34.3z⁵⁸). In a real witness-free (F, D) on M_ω^dim × C_n, F is monotone on the cross
cells D × Dᶜ (product order). Two cross cells whose values carry *different* atoms in the same M_ω-coordinate are
incomparable (an atom is comparable only to ⊥, itself, ⊤). So the atoms of one coordinate occurring at the cross cells
over a point set Q number at most the width of the cell poset (D ∩ Q) × (Q ∖ D), and
    |L₁| ≤ dim · max_D width((D ∩ Q₀) × (Q₀ ∖ D)),   Q₀ = {⊥, ⊤}^dim × C_n  (level-0 points).
Prints that bound (maximum over all down-sets D of Q₀ containing ⊥ and missing ⊤), by Dilworth (bipartite matching)."""
import itertools, sys
dim = int(sys.argv[1]) if len(sys.argv) > 1 else 2
n = int(sys.argv[2]) if len(sys.argv) > 2 else 3
Q = [p + (l,) for p in itertools.product((0, 1), repeat=dim) for l in range(n)]
le = lambda p, q: all(a <= b for a, b in zip(p, q))
def downsets():
    for bits in itertools.product((0, 1), repeat=len(Q)):
        D = {Q[i] for i in range(len(Q)) if bits[i]}
        if Q[0] in D and Q[-1] not in D and all(p in D for q in D for p in Q if le(p, q)): yield D
def width(P, leq):
    # Dilworth: width = |P| - maximum matching in the strict comparability bipartite graph
    adj = {i: [j for j in range(len(P)) if i != j and leq(P[i], P[j])] for i in range(len(P))}
    match = {}
    def aug(i, seen):
        for j in adj[i]:
            if j in seen: continue
            seen.add(j)
            if j not in match or aug(match[j], seen): match[j] = i; return True
        return False
    return len(P) - sum(aug(i, set()) for i in range(len(P)))
best = (0, None)
for D in downsets():
    cells = [(x, y) for x in D for y in Q if y not in D]
    w = width(cells, lambda c, d: le(c[0], d[0]) and le(c[1], d[1]))
    if w > best[0]: best = (w, (len(D), len(Q) - len(D)))
print(f"M_ω^{dim} × C_{n}: level-0 points {len(Q)}; max width of the cross-cell poset {best[0]} (|D₀|, |U₀| = {best[1]});"
      f"  |L₁| ≤ {dim * best[0]}")
