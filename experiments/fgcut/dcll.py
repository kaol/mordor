"""Double-cone chain labelling: P = D ⊕ C (ordinal sum), D a poset with bottom, C a poset with top.  Cells (ρ, σ):
ρ a nonempty chain of D, σ a nonempty chain of C; (ρ,σ) ≤ (ρ',σ') iff ρ ⊇ ρ', σ ⊆ σ'.  Values z ∈ D ∪ C, monotone.
W1: z ∈ D ⇒ z ≰ min ρ.  W2: z ∈ C ⇒ max σ ≰ z.  Sound for Cut on finite posets with no meets/joins required.
   python3 dcll.py nD nC   (all posets with bottom on nD, all with top on nC, up to iso)"""
import sys, itertools
from pysat.solvers import Cadical195
def posets_top(n):
    seen = set(); pairs = [(i, j) for i in range(n - 1) for j in range(n - 1) if i != j]
    for bits in itertools.product([0, 1], repeat=len(pairs)):
        le = [[i == j or j == n - 1 for j in range(n)] for i in range(n)]
        for (i, j), b in zip(pairs, bits):
            if b: le[i][j] = True
        if not all(not (le[i][j] and le[j][i]) for i in range(n) for j in range(n) if i != j): continue
        if not all(not (le[i][j] and le[j][k]) or le[i][k] for i in range(n) for j in range(n) for k in range(n)): continue
        key = min(tuple(le[p[i]][p[j]] for i in range(n) for j in range(n)) for p in [list(q) + [n - 1] for q in itertools.permutations(range(n - 1))])
        if key in seen: continue
        seen.add(key); yield le
def chains(le, n):
    return [frozenset(B) for r in range(1, n + 1) for B in itertools.combinations(range(n), r) if all(le[a][b] or le[b][a] for a in B for b in B)]
def solve(leD, nD, leC, nC):
    # D-poset with bottom: dual of a poset with top
    L = nD + nC
    def le(a, b):
        if a < nD and b < nD: return leD[b][a]          # dual
        if a < nD: return True
        if b < nD: return False
        return leC[a - nD][b - nD]
    chD = chains(leD, nD)
    chC = [frozenset(x + nD for x in c) for c in chains(leC, nC)]
    cells = [(r, s) for r in chD for s in chC]
    nv = [0]
    def new(): nv[0] += 1; return nv[0]
    Z = {c: [new() for _ in range(L)] for c in cells}
    cl = []
    for c in cells:
        cl.append(Z[c]); cl += [[-Z[c][a], -Z[c][b]] for a in range(L) for b in range(a + 1, L)]
        r, s = c
        mn = next(x for x in r if all(le(x, y) for y in r)); mx = next(x for x in s if all(le(y, x) for y in s))
        for v in range(L):
            if v < nD and le(v, mn): cl.append([-Z[c][v]])
            if v >= nD and le(mx, v): cl.append([-Z[c][v]])
    for c in cells:
        for d in cells:
            if c != d and c[0] >= d[0] and c[1] <= d[1]:
                for v in range(L):
                    cl.append([-Z[c][v]] + [Z[d][w] for w in range(L) if le(v, w)])
    return Cadical195(bootstrap_with=cl).solve()
nD, nC = int(sys.argv[1]), int(sys.argv[2])
tot = sat = 0
for leD in posets_top(nD):
    for leC in posets_top(nC):
        tot += 1
        if solve(leD, nD, leC, nC):
            sat += 1
            if sat <= 3: print(' SAT: D(dual)', [(i, j) for i in range(nD) for j in range(nD) if i != j and leD[i][j] and j != nD - 1], ' C', [(i, j) for i in range(nC) for j in range(nC) if i != j and leC[i][j] and j != nC - 1])
print(f"nD={nD} nC={nC}: {tot} pairs, {sat} SAT")
