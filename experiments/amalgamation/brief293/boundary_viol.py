"""Free analysis of dumped NoFix models (any relaxed world): for every atom q and row x in Z above q, the boundary
columns G_l = u_l(q) ^ u_{kappa(l)-1}(x) (kappa(l) = least k with u_l(q) ^ u_k(x) of height <= 2) and their colours
e_l = F(q, G_l).  Reports, per model, whether some boundary column violates Tb (F(q, G_l) <= q) -- the B1/LandEq proof
says a W0^2 (indeed Stair) NoFix model is impossible in branch b/g N = 1, and in general a pair with lambda(x) !=
lambda(q) and no violation must have an ATOM colour (a connector) on its boundary."""
import sys, json, collections
sys.path.insert(0, '.'); from corners import staircase
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W
C = collections.Counter()
for f in sys.argv[1:]:
    D = json.load(open(f)); D = D if isinstance(D, list) else [D]
    for k, d in enumerate(D):
        w = W(d['sets'], d['F']); le, F, h = w.le, w.F, w.h; dd, N = w.dN(); br = 'a' if h[dd] == 2 else 'atom'
        viol = False; conn = False
        for q in w.atoms:
            for x in w.Z:
                if not le[q][x]: continue
                G, kap, cs = staircase(w, q, x)
                for l in range(len(kap)):
                    g = G(l, kap[l] - 1); e = F[q][g]
                    if le[e][q]: viol = True
                    elif h[e] == 1 and w.lam(x) != w.lam(q): conn = True
        C[(br, 'N1' if N == 1 else 'N>=2', 'boundary Tb violated' if viol else 'no boundary violation', 'connector' if conn else '-')] += 1
for k, v in sorted(C.items()): print(v, k)
