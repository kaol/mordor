"""Round 23: minimal sets of cells whose cut constraints (with monotonicity of F) are already contradictory."""
import sys, time, collections
pass
from lat import *
from pysat.solvers import Cadical153
def build(L):
    n = L.n; nv = [0]; cl = []
    def new(): nv[0] += 1; return nv[0]
    Fv = [[[new() for v in range(n)] for y in range(n)] for x in range(n)]
    for x in range(n):
        for y in range(n):
            cl.append(Fv[x][y]); cl += [[-Fv[x][y][i], -Fv[x][y][j]] for i in range(n) for j in range(i+1, n)]
    for (x, x2) in L.covers:
        for y in range(n):
            for p in range(n):
                for q in range(n):
                    if not L.leq[p][q]: cl += [[-Fv[x][y][p], -Fv[x2][y][q]], [-Fv[y][x][p], -Fv[y][x2][q]]]
    return Fv, cl, nv
def mus(L, D):
    n = L.n; U = [y for y in range(n) if y not in D]
    Fv, cl, nv = build(L); s = Cadical153(bootstrap_with=cl); sel = {}
    for x in sorted(D):
        for y in U:
            nv[0] += 1; g = nv[0]; sel[(x, y)] = g
            for v in range(n):
                if L.leq[v][x] or L.leq[y][v]: s.add_clause([-g, -Fv[x][y][v]])
    S = list(sel)
    assert not s.solve(assumptions=[sel[c] for c in S])
    i = 0
    while i < len(S):
        T = S[:i] + S[i+1:]
        if not s.solve(assumptions=[sel[c] for c in T]): S = T
        else: i += 1
    return S
def maxs(L, X): return {x for x in X if not any(y != x and L.leq[x][y] for y in X)}
def mins(L, X): return {x for x in X if not any(y != x and L.leq[y][x] for y in X)}
t = time.time(); sizes = collections.Counter(); shape = collections.Counter(); examples = []
for L in moore_family(4):
    if L.n < 3: continue
    for D in downsets(L):
        S = mus(L, D); U = set(range(L.n)) - D
        sizes[len(S)] += 1
        xs = {x for x, _ in S}; ys = {y for _, y in S}
        key = (xs <= maxs(L, D) | {L.bot}, ys <= mins(L, U) | {L.top})
        shape[key] += 1
        if len(S) >= 6 and len(examples) < 3: examples.append((L.name, sorted(D), S))
print("MUS size distribution:", dict(sorted(sizes.items())))
print("(rows within max(D)+bot, cols within min(U)+top):", dict(shape))
for e in examples: print(e)
print(f"{time.time()-t:.0f}s")
