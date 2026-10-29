"""T_m over a family of orbit-defined sets.  X(A,B,C) = {x ∉ D : F(m_A,x) ≤ x, the F(m_B,·)-orbit of x enters D at a
value with labels ⊇ C}, for A ⊆ B (so the B-orbit descends from x ∈ S_A), C ≠ ∅.  Constant s minimal in the union of
the family; s ∈ X(A0,B0,C0) for a solver-chosen triple whose B0-orbit has length exactly m.  Minimality instances
'x < s ⇒ x ∉ X(A,B,C)' for every term x, triple and orbit length whose terms exist (sound under DCC).  No height bound.
  python3 orbmin.py shape m maxterms [orbitcap] [family]
family: full (all A ⊆ B, C ≠ all) | AB (C = A) | Ah (C = A, B = all) | explicit list "A/B/C,…" with digits, e.g. 1/12/1
(a single triple tests the DCC lemma "X(A,B,C) is empty" for orbit length m; §34.3z²¹)"""
import sys, os, itertools, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'sat'))
import cut_ground as c
SHAPE, MM, CAP = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); OC = int(sys.argv[4]) if len(sys.argv) > 4 else MM + 2
K = 3
subsets = [frozenset(A) for n in range(1, K + 1) for A in itertools.combinations(range(K), n)]
G = c.Ground(10**6, True, False, True, None, 'fit', False); S = G.S
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
FAM = sys.argv[5] if len(sys.argv) > 5 else "full"
def parse(t):   # e.g. "1/123/1" = (A={1}, B={1,2,3}, C={1})
    a, b, cc = t.split('/'); f = lambda w: frozenset(int(ch) - 1 for ch in w); return (f(a), f(b), f(cc))
TRI = [(A, B, C) for A in subsets for B in subsets for C in subsets if A <= B and C != frozenset(range(K))
       and (FAM == "full" or (FAM == "AB" and C == A) or (FAM == "Ah" and C == A and B == frozenset(range(K))))]
if FAM not in ("full", "AB", "Ah"): TRI = [parse(t) for t in FAM.split(',')]
done = set(); mdone = set()
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
F = lambda a, y: G.F.get((a, y))
s = orig_add(None, 0); axioms(); S.add_clause([-G.d(s)])
def orbit(row, x, n):
    hs = [x]
    for _ in range(n):
        nx = F(row, hs[-1])
        if nx is None: break
        hs.append(nx)
    return hs
def minimality():
    for x in range(len(G.terms)):
        if x == s or x in rows or x in (0, 1): continue
        for (A, B, C) in TRI:
            gA = F(rep[A], x)
            if gA is None: continue
            hs = orbit(rep[B], x, OC)
            for k in range(1, len(hs)):
                key = (x, A, B, C, k)
                if key in mdone: continue
                mdone.add(key)
                S.add_clause([-G.le(x, s), G.le(s, x), G.d(x), -G.le(gA, x)] + [G.d(hs[j]) for j in range(1, k)]
                             + [-G.le(hs[k], P[i]) for i in C])
def add_term(st, dep):
    i = orig_add(st, dep); axioms(); minimality(); return i
G.add_term = add_term
# s ∈ X(A0,B0,C0) with B0-orbit of length exactly MM (selector over triples)
sel = {}
for (A, B, C) in TRI:
    gA = F(rep[A], s) if F(rep[A], s) is not None else orig_add((rep[A], s), 1)
    o = [s]
    for k in range(MM + 1):
        nx = F(rep[B], o[-1]); o.append(nx if nx is not None else orig_add((rep[B], o[-1]), k + 1))
    axioms()
    v = G.var(); sel[(A, B, C)] = v
    S.add_clause([-v, G.le(gA, s)])
    for k in range(1, MM + 1): S.add_clause([-v, -G.d(o[k])])
    for i in C: S.add_clause([-v, G.le(o[MM + 1], P[i])])
S.add_clause(list(sel.values()))
minimality()
def expand(M, cap):
    n = len(G.terms); D = [G.d(i) in M for i in range(n)]; L = G.L
    for x in range(n):
        if D[x] or x == s or not L[x, s] or L[s, x]: continue
        for A in subsets:
            if F(rep[A], x) is None: G.add_term((rep[A], x), G.depth[x] + 1); return 1
        for B in subsets:
            y = x
            for k in range(OC):
                ny = F(rep[B], y)
                if ny is None: G.add_term((rep[B], y), G.depth[y] + 1); return 1
                if D[ny] if ny < n else False: break
                y = ny
    cand = [(0, x, y) for x in rows for y in range(n) if D[x] and not D[y] and (x, y) not in G.F]
    if not cand: return 0
    fs = G.fit(M, cand)
    best = sorted((int(fs[i]), G.depth[y], x, y) for i, (_, x, y) in enumerate(cand))[:cap]
    for _, _, x, y in best: G.add_term((x, y), G.depth[y] + 1)
    return len(best)
t0 = time.time(); rnd = 0
while True:
    rnd += 1; M = G.solve()
    if M is None: print(f"T_{MM} {SHAPE} (family of {len(TRI)}, orbit cap {OC}): UNSAT with {len(G.terms)} terms, {rnd} rounds, {time.time()-t0:.1f}s", flush=True); break
    if len(G.terms) >= CAP: print(f"T_{MM} {SHAPE}: still SAT at {len(G.terms)} terms, {time.time()-t0:.0f}s", flush=True); break
    if not expand(M, 1): print(f"T_{MM} {SHAPE}: CLOSED model with {len(G.terms)} terms", flush=True); break
