"""How often a grid-capture instance is satisfied only by an off-axis column (log §34.3z¹¹⁶).
For each SAT model of grid_ground at H, and each instance (g1, g2, N1, N2) whose rows are in D: is some axis column
u1(a) or u2(b) (a single orbit point) in D and below neither row? If so, the instance holds without any meet term.
  python3 grid_bite.py H rounds P"""
import sys
import numpy as np
import grid_ground as gg

H, R, P = (int(x) for x in sys.argv[1:4])
G = gg.GGround(H, True, False, False, None, 'front', False, None); G.lat_keys = set(); G.grid_keys = set(); G.grids = 0
cc = G.add_term((0, 1), 1); G.S.add_clause([-G.d(cc)])
inst = []
orig = G.add_grid
def rec(g1, g2, N1, N2):
    orig(g1, g2, N1, N2); inst.append((g1, g2, G.orbit(g1, N1), G.orbit(g2, N2)))
G.add_grid = rec
tot = axis = live = 0
for r in range(R):
    M = G.solve()
    if M is None: print(f"UNSAT at round {r}"); break
    n = len(G.terms); L = G.L; D = np.array([G.d(i) in M for i in range(n)])
    for g1, g2, u1, u2 in inst:
        if not (D[g1] and D[g2] and D[u1[-1]] and D[u2[-1]]): continue
        live += 1
        ok = any(D[w] and not L[w, g1] and not L[w, g2] for w in u1[1:] + u2[1:])
        axis += ok
    tot += 1
    G.expand(M, 1); G.expand_lat(M, 1); G.expand_grid(M, P)
print(f"H={H}: {tot} models, {live} live (model, instance) pairs, {axis} satisfied by an axis column "
      f"({100 * axis / max(live, 1):.1f}%)")
