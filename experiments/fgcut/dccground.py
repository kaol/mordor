"""Reduced 3-generator theory with NO height bound and Skolemized DCC: for every antichain R of meet rows, a constant m_R
minimal in X_R = {y ∉ D : F(m_A, y) ≤ y for all A ∈ R} (nonempty: ⊤).  Ground minimality instances for every term.
UNSAT ⇒ a contradiction valid in every DCC lattice (height-independent).   python3 dccground.py shape maxterms"""
import sys, os, itertools, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'sat'))
import numpy as np
import cut_ground as c
SHAPE = sys.argv[1]; CAP = int(sys.argv[2]); MODE = sys.argv[3] if len(sys.argv) > 3 else 'all'
K = 3
subsets = [frozenset(A) for n in range(1, K + 1) for A in itertools.combinations(range(K), n)]
G = c.Ground(10**6, True, False, True, None, 'fit', False)   # lazy_rank with a huge bound: no height constraint
S = G.S
def equal_meets():
    if SHAPE == 'laminar': return [{frozenset({0, 2}), frozenset({1, 2}), frozenset({0, 1, 2})}]
    if SHAPE == 'bouquet': return [{A for A in subsets if len(A) >= 2}]
    return []
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
        if a != b and A >= B: S.add_clause([G.le(a, b)])
for i in range(K):
    for j in range(K):
        if i != j: S.add_clause([-G.le(P[i], P[j])])
    S.add_clause([-G.le(1, P[i])])
if SHAPE == 'strict':
    pairs = [A for A in subsets if len(A) == 2]
    for A in pairs:
        for B in pairs:
            if A != B: S.add_clause([-G.le(rep[A], rep[B])])
# antichains R of distinct row terms (by containment of the index sets)
rowsets = sorted({min((A for A in subsets if rep[A] == r), key=len) for r in rows}, key=lambda A: (len(A), sorted(A)))
anti = [R for n in range(1, len(rowsets) + 1) for R in itertools.combinations(rowsets, n)
        if all(not (A < B or B < A) for A, B in itertools.combinations(R, 2))]
if MODE == 'gens': anti = [R for R in anti if all(len(A) == 1 for A in R)]
MIN = {}
done = set()
def axioms():
    for x in range(len(G.terms)):
        if x in done: continue
        done.add(x)
        S.add_clause([-G.d(x)] + [G.le(x, p) for p in P])
        for p in P: S.add_clause([G.d(x), -G.le(x, p)])
        for A in subsets:
            if len(A) >= 2: S.add_clause([-G.le(x, P[i]) for i in A] + [G.le(x, rep[A])])
axioms()
orig_add = G.add_term
pending = []
def add_term(st, dep):
    i = orig_add(st, dep); axioms(); pending.append(i); minimality(); return i
G.add_term = add_term
def minimality():
    for R, m in MIN.items():
        for t in range(len(G.terms)):
            if (R, t) in mdone or t == m: continue
            Fs = [G.F.get((rep[A], t)) for A in R]
            if any(f is None for f in Fs): continue
            mdone.add((R, t))
            S.add_clause([G.d(t), -G.le(t, m)] + [-G.le(f, t) for f in Fs] + [G.le(m, t)])
mdone = set()
for R in anti:
    m = orig_add(None, 0); axioms(); MIN[R] = m
    S.add_clause([-G.d(m)])
for R, m in MIN.items():
    for A in R:
        f = orig_add((rep[A], m), 1) if (rep[A], m) not in G.F else G.F[(rep[A], m)]
        S.add_clause([G.le(f, m)])
axioms(); minimality()
def expand(M, cap):
    n = len(G.terms); D = [G.d(i) in M for i in range(n)]
    cand = [(0, x, y) for x in rows for y in range(n) if D[x] and not D[y] and (x, y) not in G.F]
    if not cand: return 0
    fs = G.fit(M, cand)
    best = sorted((int(fs[i]), G.depth[y], x, y) for i, (_, x, y) in enumerate(cand))[:cap]
    for _, _, x, y in best: G.add_term((x, y), G.depth[y] + 1)
    return len(best)
print(f"{SHAPE}: {len(anti)} minimality constants, {len(G.terms)} terms initially", flush=True)
t0 = time.time(); rnd = 0
while True:
    rnd += 1; M = G.solve()
    if M is None: print(f"{SHAPE} (no height bound, Skolemized DCC, {MODE}): UNSAT with {len(G.terms)} terms, {rnd} rounds, {time.time()-t0:.1f}s", flush=True); break
    if len(G.terms) >= CAP: print(f"{SHAPE} ({MODE}): still SAT at {len(G.terms)} terms, {time.time()-t0:.0f}s", flush=True); break
    if not expand(M, 1): print(f"{SHAPE}: CLOSED model, {len(G.terms)} terms", flush=True); break
    if rnd % 50 == 0: print(f"  round {rnd}: {len(G.terms)} terms, {time.time()-t0:.0f}s", flush=True)
