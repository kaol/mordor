"""Double-cone chain labelling via CP-SAT (table constraints).  python3 dcll_cp.py NAME [seconds]"""
import itertools, sys, time
from ortools.sat.python import cp_model
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
 'bowtie_chain': (5, [(0,1),(0,2),(1,3),(1,4),(2,3),(2,4)], 3, [(0,1),(1,2)]),
 'chain_chain': (3, [(0,1),(1,2)], 3, [(0,1),(1,2)]),
 'K33': (7, [(0,1),(0,2),(0,3)] + [(a,p) for a in (1,2,3) for p in (4,5,6)], 7, [(u,s) for u in (0,1,2) for s in (3,4,5)] + [(s,6) for s in (3,4,5)]),
 'crown': (7, [(0,1),(0,2),(0,3),(1,4),(1,5),(2,5),(2,6),(3,6),(3,4)], 7, [(0,3),(0,4),(1,4),(1,5),(2,5),(2,3)] + [(s,6) for s in (3,4,5)]),
}
name = sys.argv[1]; T = float(sys.argv[2]) if len(sys.argv) > 2 else 600
nD, relD, nC, relC = INST[name]
leD = closure(nD, relD); leC = closure(nC, relC); L = nD + nC
def le(a, b):
    if a < nD and b < nD: return leD[a][b]
    if a < nD: return True
    if b < nD: return False
    return leC[a - nD][b - nD]
ch = lambda n, l: [frozenset(B) for r in range(1, n + 1) for B in itertools.combinations(range(n), r) if all(l[a][b] or l[b][a] for a in B for b in B)]
chD = ch(nD, leD); chC = [frozenset(x + nD for x in c) for c in ch(nC, leC)]
cells = [(r, s) for r in chD for s in chC]
m = cp_model.CpModel(); Z = {}
for c in cells:
    r, s = c
    mn = next(x for x in r if all(le(x, y) for y in r)); mx = next(x for x in s if all(le(y, x) for y in s))
    dom = [v for v in range(L) if not ((v < nD and le(v, mn)) or (v >= nD and le(mx, v)))]
    if not dom: print(f'{name}: cell {sorted(r)},{sorted(s)} has an empty domain: trivially INFEASIBLE'); sys.exit()
    Z[c] = m.NewIntVarFromDomain(cp_model.Domain.FromValues(dom), '')
pairs = [(v, w) for v in range(L) for w in range(L) if le(v, w)]
ncov = 0
for c in cells:
    for d in cells:
        if c != d and c[0] >= d[0] and c[1] <= d[1] and (len(c[0]) - len(d[0])) + (len(d[1]) - len(c[1])) == 1:
            m.AddAllowedAssignments([Z[c], Z[d]], pairs); ncov += 1
sv = cp_model.CpSolver(); sv.parameters.max_time_in_seconds = T; sv.parameters.num_workers = 8
t = time.time(); st = sv.Solve(m)
print(f"{name}: {len(cells)} cells, {ncov} cover constraints: {sv.StatusName(st)} ({time.time()-t:.1f}s)", flush=True)
if st in (cp_model.FEASIBLE, cp_model.OPTIMAL):
    nm = lambda v: f"d{v}" if v < nD else f"c{v-nD}"
    for c in cells[:40]:
        print(' ', sorted(c[0]), sorted(x - nD for x in c[1]), '->', nm(sv.Value(Z[c])))
