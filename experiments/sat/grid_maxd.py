"""Class statistics of the lattice ground search's partial models: |Max D| and |Min Dᶜ| per round (log §34.3z¹¹⁶).
  python3 grid_maxd.py H rounds"""
import sys, numpy as np
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import grid_ground as gg
H, R = int(sys.argv[1]), int(sys.argv[2])
G = gg.GGround(H, True, False, False, None, 'front', False, None); G.lat_keys = set(); G.grid_keys = set(); G.grids = 0
cc = G.add_term((0, 1), 1); G.S.add_clause([-G.d(cc)])
for r in range(R):
    M = G.solve()
    if M is None: print("UNSAT", r); break
    n = len(G.terms); L = G.L; D = np.array([G.d(i) in M for i in range(n)])
    rep = np.argmax(L & L.T, axis=1); cls = sorted({int(x) for x in rep})
    Dc = [c for c in cls if D[c]]; Cc = [c for c in cls if not D[c]]
    maxD = [c for c in Dc if not any(L[c, e] and not L[e, c] for e in Dc)]
    minC = [c for c in Cc if not any(L[e, c] and not L[c, e] for e in Cc)]
    if r % 5 == 0 or r == R - 1: print(f"round {r}: {n} terms, {len(Dc)} D-classes, {len(Cc)} out-classes, |Max D| = {len(maxD)}, |Min Dᶜ| = {len(minC)}", flush=True)
    G.expand(M, 1); G.expand_lat(M, 1)
