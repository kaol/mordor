# Show a stored model: lattice covers, heights, Z, rows of F at Z, descents, landings (read-only on the repo)
import sys, json
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation'); sys.path.insert(0, '/home/user/mordor/experiments/separation')
import bank
def show(d):
    m = bank.M(d['sets'], d['F']); L = m.L; h = m.h; F = m.F
    print(f"|L|={m.n} H={L.height} Z={m.Z} M2={m.M2} atoms={m.atoms} d={m.d} N={m.N} branch={m.branch}")
    print(" covers:", {i: L.covers_up[i] for i in range(m.n)})
    print(" heights:", h)
    from rstages import a_of
    for x in m.Z:
        print(f"  row {x} (h{h[x]}): F={F[x]} desc={m.desc(x)} lam={m.lam(x)} i={m.lidx(x)} exits={m.exits(x)} a={a_of(L,F,x)}")
    print("  self-landing M2:", [x for x in m.M2 if m.lam(x) == x])
if __name__ == '__main__':
    for f in sys.argv[1:]:
        D = json.load(open(f)); D = D if isinstance(D, list) else [D]
        for d in D: print(f); show(d)
