"""Free stats (samples; one SAT model per lattice from the CGone mutant dumps): relations between the colour rows
when ColourGain holds at b only (a = the other colour).  r_x = last high element of row x."""
import sys, json, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W
import lib
C = collections.Counter()
for fn in sys.argv[1:]:
    for m in json.load(open(fn)):
        w = W(m['sets'], m['F']); A = lib.colours(w); F = w.F; le = w.le; h = w.h; L = w.L
        if len(A) != 2: continue
        cg = {c: any(le[c2][w.lam(c)] and not le[c2][c] for c2 in A) for c in A}
        bs = [c for c in A if cg[c]]
        if len(bs) != 1: C['CG at both or none'] += 1; continue
        b = bs[0]; a = A[0] if b == A[1] else A[1]; P = L.join[a][b]
        ra = w.desc(a)[w.lidx(a) - 1]; rb = w.desc(b)[w.lidx(b) - 1]
        C[('phi(r_a)==a', F[w.bot][ra] == a)] += 1
        C[('r_a vs r_b', 'eq' if ra == rb else ('ra>rb' if le[rb][ra] else ('ra<rb' if le[ra][rb] else 'incomp')))] += 1
        C[('lam(a) in Z', w.lam(a) in w.Z)] += 1
        C[('lam(b) == a', w.lam(b) == a)] += 1
        C[('r_a on desc(b)', ra in w.desc(b))] += 1
        C[('r_a >= P', le[P][ra])] += 1
for k, v in sorted(C.items(), key=str): print(v, k)
