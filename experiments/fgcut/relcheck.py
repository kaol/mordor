"""Relative Lefschetz check for the double cone.  D (with ⊥ = 0), C (with ⊤ = top); cells (ρ, σ) with ρ ⊆ D, σ ⊆ C
nonempty chains, order ρ ⊇ ρ', σ ⊆ σ'.  L = flags of cells with ⊥ ∉ ρ₁ (largest ρ) or ⊤ ∉ σ_r (largest σ).
carrier(cell) = (ρ ∖ ⊥) ∪ (σ ∖ ⊤) ⊆ P̄;  K = chains of P̄ = D̄ ⊕ C̄.
(1) sd: C(K) → C(L), τ ↦ Σ {complete-in-carrier L-flags s with carrier(s) = τ}; check ∂ sd = sd ∂ (mod 2).
(2) random monotone labellings z : cells → P̄; count L-flags s with |s| = |carrier(s)| and labels = carrier(s): parity."""
import itertools, random, sys
from collections import defaultdict
def closure(n, rel):
    le = [[i == j for j in range(n)] for i in range(n)]
    for a, b in rel: le[a][b] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if le[i][k] and le[k][j]: le[i][j] = True
    return le
INST = {
 'bowtie': (5, [(0,1),(0,2),(1,3),(1,4),(2,3),(2,4)], 5, [(0,2),(0,3),(1,2),(1,3),(2,4),(3,4)]),
 'small': (2, [(0,1)], 2, [(0,1)]),
 'V': (3, [(0,1),(0,2)], 3, [(0,2),(1,2)]),
 'bowchain': (5, [(0,1),(0,2),(1,3),(1,4),(2,3),(2,4)], 3, [(0,1),(1,2)]),
}
name = sys.argv[1]; NS = int(sys.argv[2]) if len(sys.argv) > 2 else 200
nD, rD, nC, rC = INST[name]
leD = closure(nD, rD); leC = closure(nC, rC)
N = nD + nC
def le(a, b):
    if a < nD and b < nD: return leD[a][b]
    if a < nD: return True
    if b < nD: return False
    return leC[a - nD][b - nD]
BOT, TOP = 0, N - 1
chains = lambda S: [frozenset(B) for r in range(1, len(S) + 1) for B in itertools.combinations(S, r) if all(le(a, b) or le(b, a) for a in B for b in B)]
chD = chains(range(nD)); chC = chains(range(nD, N))
cells = [(r, s) for r in chD for s in chC]
cle = lambda c, d: c[0] >= d[0] and c[1] <= d[1]
carrier = lambda c: (c[0] - {BOT}) | (c[1] - {TOP})
# flags (chains of cells, strictly increasing) — enumerate all chains in cell poset
succ = {c: [d for d in cells if d != c and cle(c, d)] for c in cells}
flags = []
def ext(fl):
    flags.append(tuple(fl))
    for d in succ[fl[-1]]: ext(fl + [d])
for c in cells: ext([c])
inL = lambda fl: (BOT not in fl[0][0]) or (TOP not in fl[-1][1])
Lf = [fl for fl in flags if inL(fl)]
Pbar = [x for x in range(N) if x not in (BOT, TOP)]
K = chains(Pbar)
print(f"{name}: {len(cells)} cells, {len(flags)} flags, |L| = {len(Lf)}, |K| = {len(K)}")
car = {fl: frozenset().union(*[carrier(c) for c in fl]) for fl in Lf}
sd = defaultdict(set)
for fl in Lf:
    if len(fl) == len(car[fl]): sd[car[fl]].add(fl)
def bd_flag(fl): return [fl[:i] + fl[i+1:] for i in range(len(fl))] if len(fl) > 1 else []
ok = True
for tau in K:
    lhs = defaultdict(int)
    for fl in sd[tau]:
        for f in bd_flag(fl): lhs[f] ^= 1
    rhs = defaultdict(int)
    if len(tau) > 1:
        for x in tau:
            for fl in sd[tau - {x}]: rhs[fl] ^= 1
    if {k for k, v in lhs.items() if v} != {k for k, v in rhs.items() if v}:
        ok = False; print('  chain-map FAILS at', sorted(tau)); break
print('  sd is a chain map:', ok, '; sd(vertex) sizes', sorted({len(sd[frozenset([v])]) for v in Pbar}))
# random monotone labellings into P̄ via random linear extension + monotone hull: z(c) = least element ≥ ... use F(min ρ, max σ)-style and generic
def rand_monotone():
    # generic: process cells in a linear extension; choose z(c) uniformly among P̄-values ≥ all z of predecessors, if any
    order = sorted(cells, key=lambda c: (-len(c[0]), len(c[1])))
    z = {}
    for c in order:
        lower = [z[d] for d in cells if d in z and cle(d, c)]
        cand = [v for v in Pbar if all(le(u, v) for u in lower)]
        if not cand: return None
        z[c] = random.choice(cand)
    return z
from pysat.solvers import Solver
Zv = {}; nvar = 0
for c in cells:
    for v in Pbar: nvar += 1; Zv[(c, v)] = nvar
cls = []
for c in cells:
    cls.append([Zv[(c, v)] for v in Pbar]); cls += [[-Zv[(c, a)], -Zv[(c, b)]] for a in Pbar for b in Pbar if a < b]
for c in cells:
    for d in succ[c]:
        for v in Pbar: cls.append([-Zv[(c, v)]] + [Zv[(d, w)] for w in Pbar if le(v, w)])
sol = Solver(name='cadical195', bootstrap_with=cls)
def sat_monotone():
    for _ in range(50):
        ass = [Zv[(random.choice(cells), random.choice(Pbar))] for _ in range(random.randint(3, 40))]
        if sol.solve(assumptions=ass):
            M = set(l for l in sol.get_model() if l > 0)
            return {c: next(v for v in Pbar if Zv[(c, v)] in M) for c in cells}
    return None
odd = even = fail = 0
for _ in range(NS):
    z = sat_monotone()
    if z is None: fail += 1; continue
    cnt = 0
    for fl in Lf:
        if len(fl) == len(car[fl]) and {z[c] for c in fl} == set(car[fl]) and len({z[c] for c in fl}) == len(fl): cnt += 1
    if cnt % 2: odd += 1
    else: even += 1
print(f"  random monotone labellings: odd {odd}, even {even}, construction failures {fail}")
