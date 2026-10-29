"""Ground refutation of the reduced k-generator cut theory at edge-height H (poset of columns, rows = the meets m_A only).
UNSAT ⇒ the reduced statement holds at height ≤ H.  A model closed under the term rule ⇒ a finite reduced countermodel.
  python3 crossground.py K H maxterms [crossing|strict|laminar|bouquet] [out.cnf]
Shapes: crossing = no relation among the meets beyond glb (they may coincide); strict = the pairwise meets pairwise
incomparable; laminar = m13 = m23 = m123; bouquet = all meets equal.  Rows are the meets only, so the theory is weaker
than the full cut theory: UNSAT means a proof using only the rows F(m_A, ·) exists at that height (§34.3z¹⁸)."""
import sys, os, itertools, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'sat'))
import numpy as np
import cut_ground as c

K, H, CAP = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); SHAPE = sys.argv[4] if len(sys.argv) > 4 else 'crossing'
CNF = sys.argv[5] if len(sys.argv) > 5 else None     # on UNSAT, the full clause set in DIMACS (for sat/drat_certify.py)
subsets = [frozenset(A) for n in range(1, K + 1) for A in itertools.combinations(range(K), n)]

def equal_meets():                 # which meets coincide, by shape (K = 3)
    if SHAPE == 'laminar': return [{frozenset({0, 2}), frozenset({1, 2}), frozenset({0, 1, 2})}]
    if SHAPE == 'bouquet': return [{A for A in subsets if len(A) >= 2}]
    return []

G = c.Ground(H, True, False, False, None, 'fit', False)
S = G.S
rep = {}
for A in subsets:
    cls = next((e for e in equal_meets() if A in e), None)
    key = min(cls, key=sorted) if cls else A
    if key not in rep: rep[key] = G.add_term(None, 0)
    rep[A] = rep[key]
rows = sorted(set(rep[A] for A in subsets)); P = [rep[frozenset([i])] for i in range(K)]
for A in subsets:
    for B in subsets:
        a, b = rep[A], rep[B]
        if a == b: continue
        if A >= B: S.add_clause([G.le(a, b)])
        elif not (A > B):
            # meets are glbs: m_A ≤ m_B iff m_A ≤ p_i for all i ∈ B; generators pairwise incomparable; otherwise free
            if len(B) == 1 and len(A) == 1: S.add_clause([-G.le(a, b)])
for i in range(K): S.add_clause([-G.le(1, P[i])])
if SHAPE == 'strict':              # pairwise meets pairwise incomparable (strict crossing)
    pairs = [A for A in subsets if len(A) == 2]
    for A in pairs:
        for B in pairs:
            if A != B: S.add_clause([-G.le(rep[A], rep[B])])
done = set()
def axioms():                      # D(x) ⟺ ∃i x ≤ p_i, and glb instances for every term
    for x in range(len(G.terms)):
        if x in done: continue
        done.add(x)
        S.add_clause([-G.d(x)] + [G.le(x, p) for p in P])
        for p in P: S.add_clause([G.d(x), -G.le(x, p)])
        for A in subsets:
            if len(A) >= 2: S.add_clause([-G.le(x, P[i]) for i in A] + [G.le(x, rep[A])])
axioms()
orig_add = G.add_term
def add_term(st, dep):
    i = orig_add(st, dep); axioms(); return i
G.add_term = add_term
def expand(M, cap):
    n = len(G.terms); D = [G.d(i) in M for i in range(n)]
    cand = [(0, x, y) for x in rows for y in range(n) if D[x] and not D[y] and (x, y) not in G.F]
    if not cand: return 0
    fs = G.fit(M, cand)
    best = sorted((int(fs[i]), G.depth[y], x, y) for i, (_, x, y) in enumerate(cand))[:cap]
    for _, _, x, y in best: G.add_term((x, y), G.depth[y] + 1)
    return len(best)
G.add_term((rep[frozenset(range(K))], 1), 1)
t0 = time.time(); rnd = 0
while True:
    rnd += 1; M = G.solve()
    if M is None:
        print(f"K={K} H={H} {SHAPE}: UNSAT with {len(G.terms)} terms, {rnd} rounds, {time.time()-t0:.1f}s", flush=True)
        if CNF: c.write_dimacs(G, CNF); print(f"wrote {CNF} ({len(G.clauses)} clauses, {G.nv} variables)", flush=True)
        break
    if len(G.terms) >= CAP: print(f"K={K} H={H} {SHAPE}: still SAT at {len(G.terms)} terms", flush=True); break
    if not expand(M, 1):
        print(f"K={K} H={H} {SHAPE}: CLOSED model with {len(G.terms)} terms", flush=True)
        import pickle; pickle.dump((G.terms, G.L, M, [G.d(i) in M for i in range(len(G.terms))]), open(f'closed_{K}_{H}_{SHAPE}.pkl', 'wb')); break
    if rnd % 50 == 0: print(f"  round {rnd}: {len(G.terms)} terms, {time.time()-t0:.0f}s", flush=True)
