"""Does the thick-slice system force a contradiction by itself?

Q a small finite lattice (it satisfies Cut).  Unknowns: four monotone G_ij : Q×Q→Q with
G00 <= G01 <= G11, G00 <= G10 <= G11, and nested down-sets ⊥ ∈ R1 ⊊ R0 ⊊ Q such that
  a_{G00}(R0) ⊆ R0,  b_{G11}^{-1}(R1) ⊆ R1,  a_{G10}(R1) ⊆ R0,  b_{G10}^{-1}(R1) ⊆ R0,
where a_G(p) = gfp of q ↦ G(p,q), b_G(q) = lfp of p ↦ G(p,q).
Level 2 adds layer bits: G_ij are projections of one monotone F on Q×C2 (layers ℓ_ij), and R = R0×{0} ∪ R1×{1}
must be closed under a_F, b_F^{-1}.  Level 2 is impossible (Cut on the finite lattice Q×C2); level 1 tells us
whether the four inclusions carry the contradiction."""
import itertools, random
from z3 import *

def chain(n):
    return list(range(n)), (lambda a, b: a <= b), (lambda a, b: max(a, b)), (lambda a, b: min(a, b))

def search(n, level):
    Q, le, jn, mt = chain(n)
    top = n - 1
    G = {ij: {(p, q): Int(f"G{ij}_{p}_{q}") for p in Q for q in Q} for ij in ("00", "01", "10", "11")}
    s = Solver()
    for ij in G:
        for p in Q:
            for q in Q:
                s.add(G[ij][(p, q)] >= 0, G[ij][(p, q)] < n)
                if p + 1 < n: s.add(G[ij][(p, q)] <= G[ij][(p + 1, q)])
                if q + 1 < n: s.add(G[ij][(p, q)] <= G[ij][(p, q + 1)])
    for p in Q:
        for q in Q:
            s.add(G["00"][(p, q)] <= G["01"][(p, q)], G["00"][(p, q)] <= G["10"][(p, q)],
                  G["01"][(p, q)] <= G["11"][(p, q)], G["10"][(p, q)] <= G["11"][(p, q)])
    # down-sets on a chain: R0 = [0, r0), R1 = [0, r1), 1 <= r1 < r0 < n
    r0, r1 = Int("r0"), Int("r1")
    s.add(1 <= r1, r1 < r0, r0 < n)
    inR = lambda r, v: v < r
    # gfp/lfp on a chain: a_G(p) = max{q : q <= G(p,q)} ; b_G(q) = min{p : G(p,q) <= p}
    def a_le_cond(ij, p, r):  # a_G(p) ∈ R(r)  <=>  every q with q <= G(p,q) has q < r
        return And([Implies(q <= G[ij][(p, q)], q < r) for q in Q])
    def b_in(ij, q, r):       # b_G(q) ∈ R(r)  <=>  some p < r with G(p,q) <= p
        return Or([And(p < r, G[ij][(p, q)] <= p) for p in Q])
    for p in Q:
        s.add(Implies(inR(r0, p), a_le_cond("00", p, r0)))
        s.add(Implies(inR(r1, p), a_le_cond("10", p, r0)))
    for q in Q:
        s.add(Implies(b_in("11", q, r1), q < r1))
        s.add(Implies(b_in("10", q, r1), q < r0))
    r = s.check()
    if r == sat:
        m = s.model()
        print(f"n={n}: level-1 system SAT: r0={m[r0]}, r1={m[r1]}")
        for ij in G:
            print("  G" + ij, [[m.eval(G[ij][(p, q)]).as_long() for q in Q] for p in Q])
    else:
        print(f"n={n}: level-1 system UNSAT")

for n in (3, 4):
    search(n, 1)
