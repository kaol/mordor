"""Ground refutation at edge-height H seeded with a recursive guess (§34.3h, fifteenth brief, Strategy A/C):
seed terms = the core terms of the height-(H-1) certificate T and their relativization σT below c0 = F(⊥,⊤)
(σ: ⊤ ↦ c0).  Then the usual tightness loop.  Compare rounds/terms with the unseeded run.

  python3 seeded_height.py H seedfile.pkl [maxterms] [mode]   mode: none | T | TsT (default TsT)"""
import sys, time, pickle
import cut_ground as c

def sub(t, b, tp):
    if t == '⊥': return b
    if t == '⊤': return tp
    return (sub(t[0], b, tp), sub(t[1], b, tp))

def run(H, seeds, cap, per_round=1):
    G = c.Ground(H, True, False, False, None, 'fit', False); c0 = G.add_term((0, 1), 1); G.S.add_clause([-G.d(c0)])
    idx = {'⊥': 0, '⊤': 1, ('⊥', '⊤'): c0}
    def add(t):
        if t in idx: return idx[t]
        s, u = add(t[0]), add(t[1])
        if (s, u) in G.F: idx[t] = G.F[(s, u)]
        else: idx[t] = G.add_term((s, u), max(G.depth[s], G.depth[u]) + 1)
        return idx[t]
    for t in seeds: add(t)
    print(f"H={H}: seeded with {len(G.terms)} terms", flush=True)
    t0 = time.time(); rnd = 0
    while True:
        rnd += 1; M = G.solve()
        if M is None:
            print(f"H={H}: UNSAT with {len(G.terms)} terms after {rnd} rounds, {time.time()-t0:.1f}s", flush=True); return True
        if len(G.terms) >= cap:
            print(f"H={H}: still SAT at {len(G.terms)} terms after {rnd} rounds, {time.time()-t0:.0f}s", flush=True); return False
        if not G.expand(M, per_round): print("closed model", flush=True); return False
        if rnd % 25 == 0: print(f"  round {rnd}: {len(G.terms)} terms, {time.time()-t0:.0f}s", flush=True)

if __name__ == '__main__':
    H = int(sys.argv[1]); T = pickle.load(open(sys.argv[2], 'rb'))
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 3000; mode = sys.argv[4] if len(sys.argv) > 4 else 'TsT'
    c0 = ('⊥', '⊤')
    seeds = [] if mode == 'none' else list(T) + ([sub(t, '⊥', c0) for t in T] if mode == 'TsT' else [])
    run(H, seeds, cap)
