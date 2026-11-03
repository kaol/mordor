"""Minimal support of the envelope on a depth-1 frontier tree (log §34.3z⁹⁷), z3.

Uses branching.run (root frontier pair, both children split and re-terminalized). Envelope ends:
lᵥ = xᵥ ⊓ aᵥ (aᵥ = yᵥ ⊓ zᵥ), uᵥ = yᵥ ⊔ bᵥ, named as glb/lub elements (branching.run). Test whether the minimal supports can be a single leaf:
supp(d) = {root} (l_root ≤ l_child for both children) and supp(u) = {root} (u_child ≤ u_root), and the variants
"single child supports both ends" and "different children support d and u" (divergence at the root)."""
import sys, itertools
from z3 import *
import branching
def lv(le, n, node): x, y, z, a, b = node(n); return (x, a)
def make(kind):
    def extra(s, le, inD, cell, node, N):
        L = lambda v, w: le[f"l{v}", f"l{w}"]
        U = lambda v, w: le[f"u{v}", f"u{w}"]
        if kind == 'root-both':        # d = l_root, u = u_root
            s.add(L(0, 1), L(0, 2), U(1, 0), U(2, 0))
        elif kind == 'child-both':     # d = l_1, u = u_1 (one child supports both ends)
            s.add(L(1, 0), L(1, 2), U(0, 1), U(2, 1))
        elif kind == 'diverge':        # d = l_1, u = u_2 (supports diverge at the root)
            s.add(L(1, 0), L(1, 2), U(0, 2), U(1, 2))
        elif kind == 'two-needed':     # neither end has a single-node support among the three
            s.add(*[Or(Not(L(v, 0)), Not(L(v, 1)), Not(L(v, 2))) for v in range(3)])
    return extra
for K in [1, 2]:
    for pat in (["BBB"] if K == 1 else ["BBB", "AAA", "ABB"]):
        for kind in ['root-both', 'child-both', 'diverge', 'two-needed']:
            r = branching.run(K, pat, 1, notransfer=False, extra=make(kind))
            print(f"k={K} cases {pat}: single-support pattern '{kind}': {r}", flush=True)
