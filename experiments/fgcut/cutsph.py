"""Cut on P = D ⊕ C for structured cores.  D = ⊥ ⊕ D̄, C = C̄ ⊕ ⊤.  Rows: all of D; columns: all of C; F(x,y) ∈ P
monotone, W1: F ≰ x, W2: y ≰ F.  Ordinal sum is the most permissive cross order.   python3 cutsph.py SPEC_D SPEC_C
SPEC: 'lev:2,2,2' (ordinal sum of antichains, proper part S^(n-1)) or 'crown:n' (2n-crown, S^1)."""
import sys, itertools, time
from pysat.solvers import Solver
def proper(spec):
    kind, arg = spec.split(':')
    if kind == 'lev':
        sizes = [int(x) for x in arg.split(',')]; els = []; rel = []; prev = []
        for s in sizes:
            cur = list(range(len(els), len(els) + s)); els += cur
            rel += [(a, b) for a in prev for b in cur]; prev = cur
        return len(els), rel
    n = int(arg)    # crown: a_0..a_{n-1} < p_i, p_{i+1}
    rel = [(i, n + i) for i in range(n)] + [(i, n + (i + 1) % n) for i in range(n)]
    return 2 * n, rel
nd, rd = proper(sys.argv[1]); nc, rc = proper(sys.argv[2])
# D: 0 = ⊥, 1..nd = D̄ ; C: nd+1 .. nd+nc = C̄, top = nd+nc+1
N = nd + nc + 2; BOT = 0; TOP = N - 1
le = [[i == j for j in range(N)] for i in range(N)]
for a, b in rd: le[a + 1][b + 1] = True
for a, b in rc: le[nd + 1 + a][nd + 1 + b] = True
for i in range(N): le[BOT][i] = True; le[i][TOP] = True
for i in range(1, nd + 1):
    for j in range(nd + 1, N): le[i][j] = True
for k in range(N):
    for i in range(N):
        for j in range(N):
            if le[i][k] and le[k][j]: le[i][j] = True
D = list(range(0, nd + 1)); C = list(range(nd + 1, N))
nv = 0; Fv = {}
for x in D:
    for y in C:
        for v in range(N): nv += 1; Fv[(x, y, v)] = nv
cl = []
for x in D:
    for y in C:
        cl.append([Fv[(x, y, v)] for v in range(N)])
        cl += [[-Fv[(x, y, a)], -Fv[(x, y, b)]] for a in range(N) for b in range(a + 1, N)]
        for v in range(N):
            if le[v][x] or le[y][v]: cl.append([-Fv[(x, y, v)]])
cov = lambda S, a, b: le[a][b] and a != b and not any(le[a][c] and le[c][b] and c not in (a, b) for c in S)
for x in D:
    for y in C:
        for x2 in D:
            if cov(D, x, x2):
                for v in range(N): cl.append([-Fv[(x, y, v)]] + [Fv[(x2, y, w)] for w in range(N) if le[v][w]])
        for y2 in C:
            if cov(C, y, y2):
                for v in range(N): cl.append([-Fv[(x, y, v)]] + [Fv[(x, y2, w)] for w in range(N) if le[v][w]])
t = time.time(); r = Solver(name='cadical195', bootstrap_with=cl).solve()
print(f"Cut {sys.argv[1]} ⊕ {sys.argv[2]} ({N} elements): {'SAT — COUNTEREXAMPLE' if r else 'UNSAT'} ({time.time()-t:.1f}s)", flush=True)
