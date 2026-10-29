"""Multi-orbit DCC-lemma tester.  Family X = {x ∉ D : F(m_A,x) ≤ x, and for each j the F(m_Bj,·)-orbit of x enters D
at a value whose exact label set lies in 𝓛_j} (Bj ⊇ A).  T: no height bound, s ∈ X with the j-th orbit of length m_j,
s minimal in X (instances for every term and orbit length).  UNSAT ⇒ no minimal element of X with these lengths.
  python3 orbfam.py shape "A|B1:L,L|B2:L" m1,m2 maxterms     labels as digit strings, e.g. "12|123:1,2,12,13,23|12:3" """
import sys, os, itertools, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'sat'))
import cut_ground as c
SHAPE, SPEC, MS, CAP = sys.argv[1], sys.argv[2], [int(v) for v in sys.argv[3].split(',')], int(sys.argv[4])
K = 3; ALL = frozenset(range(K))
f = lambda w: frozenset(int(ch) - 1 for ch in w)
parts = SPEC.split('|'); A0 = f(parts[0])
ORBS = [(f(p.split(':')[0]), [f(L) for L in p.split(':')[1].split(',')]) for p in parts[1:]]
assert len(MS) == len(ORBS) and all(B >= A0 for B, _ in ORBS)
subsets = [frozenset(A) for n in range(1, K + 1) for A in itertools.combinations(range(K), n)]
G = c.Ground(10**6, True, False, True, None, 'fit', False); S = G.S
def equal_meets():
    if SHAPE == 'laminar': return [{frozenset({0, 2}), frozenset({1, 2}), ALL}]
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
F = lambda a, y: G.F.get((a, y))
labv = {}
def inlab(z, Ls):        # aux literal ⟺ exact label set of z is one of Ls
    key = (z, tuple(sorted(tuple(sorted(L)) for L in Ls)))
    if key in labv: return labv[key]
    ex = []
    for L in Ls:
        v = G.var(); ex.append(v)
        lits = [G.le(z, P[i]) if i in L else -G.le(z, P[i]) for i in range(K)]
        for l in lits: S.add_clause([-v, l])
        S.add_clause([v] + [-l for l in lits])
    e = G.var(); S.add_clause([-e] + ex)
    for v in ex: S.add_clause([e, -v])
    labv[key] = e; return e
def orbit(row, x, n):
    hs = [x]
    for _ in range(n):
        nx = F(row, hs[-1])
        if nx is None: break
        hs.append(nx)
    return hs
s = orig_add(None, 0); axioms(); S.add_clause([-G.d(s)])
OC = max(MS) + 2
mdone = set()
def minimality():
    for x in range(len(G.terms)):
        if x == s or x in rows or x in (0, 1): continue
        gA = F(rep[A0], x)
        if gA is None: continue
        obs = [orbit(rep[B], x, OC) for B, _ in ORBS]
        ranges = [range(1, len(o)) for o in obs]
        for ks in itertools.product(*ranges):
            key = (x, ks)
            if key in mdone: continue
            mdone.add(key)
            cl = [-G.le(x, s), G.le(s, x), G.d(x), -G.le(gA, x)]
            for (B, Ls), o, k in zip(ORBS, obs, ks):
                cl += [G.d(o[j]) for j in range(1, k)] + [-G.d(o[k]), -inlab(o[k], Ls)]
            S.add_clause(cl)
def add_term(st, dep):
    i = orig_add(st, dep); axioms(); minimality(); return i
G.add_term = add_term
gs = F(rep[A0], s) if F(rep[A0], s) is not None else orig_add((rep[A0], s), 1)
S.add_clause([G.le(gs, s)])
for (B, Ls), m in zip(ORBS, MS):
    o = [s]
    for k in range(m + 1):
        nx = F(rep[B], o[-1]); o.append(nx if nx is not None else orig_add((rep[B], o[-1]), k + 1))
    axioms()
    for k in range(1, m + 1): S.add_clause([-G.d(o[k])])
    S.add_clause([G.d(o[m + 1])]); S.add_clause([inlab(o[m + 1], Ls)])
minimality()
def expand(M, cap):
    n = len(G.terms); D = [G.d(i) in M for i in range(n)]; L = G.L
    for x in range(n):
        if D[x] or x == s or not L[x, s] or L[s, x]: continue
        for A in subsets:
            if F(rep[A], x) is None: G.add_term((rep[A], x), G.depth[x] + 1); return 1
        for B, _ in ORBS:
            y = x
            for k in range(OC):
                ny = F(rep[B], y)
                if ny is None: G.add_term((rep[B], y), G.depth[y] + 1); return 1
                if D[ny]: break
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
    if M is None: print(f"{SHAPE} {SPEC} m={MS}: UNSAT, {len(G.terms)} terms, {time.time()-t0:.1f}s", flush=True); break
    if len(G.terms) >= CAP: print(f"{SHAPE} {SPEC} m={MS}: SAT at {len(G.terms)} terms, {time.time()-t0:.0f}s", flush=True); break
    if not expand(M, 1): print(f"{SHAPE} {SPEC} m={MS}: CLOSED, {len(G.terms)} terms", flush=True); break
