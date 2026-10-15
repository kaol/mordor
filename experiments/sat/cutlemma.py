"""Round 22: the Cut Lemma.  For monotone F on a finite lattice L and a nonempty proper downset D (U = L \\ D),
there are x in D, y in U with F(x,y) <= x or F(x,y) >= y.  'cover' = only cover pairs x < y required."""
import random, sys, time
from lat import *
from pysat.solvers import Cadical153
def cut_counterexample_exists(L, D, covers_only=False):
    n = L.n; e = Enc.__new__(Enc); e.nv = 0; e.cl = []; e.L = L
    Fv = [[[e._new() for v in range(n)] for y in range(n)] for x in range(n)]
    for x in range(n):
        for y in range(n): e.exactly_one(Fv[x][y])
    for (x, x2) in L.covers:
        for y in range(n):
            for p in range(n):
                for q in range(n):
                    if not L.leq[p][q]: e.cl += [[-Fv[x][y][p], -Fv[x2][y][q]], [-Fv[y][x][p], -Fv[y][x2][q]]]
    for x in D:
        for y in set(range(n)) - D:
            if covers_only and (x, y) not in L.covers: continue
            for v in range(n):
                if L.leq[v][x] or L.leq[y][v]: e.cl.append([-Fv[x][y][v]])
    return Cadical153(bootstrap_with=e.cl).solve()
if __name__ == "__main__":
    t = time.time(); st = {"full": [0, 0], "cover": [0, 0]}
    for L in list(moore_family(4)) + [E(3)]:
        if L.n < 2: continue
        for D in downsets(L):
            for mode in st:
                st[mode][0] += 1; st[mode][1] += cut_counterexample_exists(L, D, mode == "cover")
    print(f"<=4 join-irreducibles + E3: (instances, counterexamples) {st}  {time.time()-t:.0f}s", flush=True)
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng = random.Random(99); t = time.time(); inst = nl = 0
    while time.time() - t < budget:
        L = closure_lattice(rng.sample(range(31), rng.randint(2, 10)), 5)
        if not 5 <= L.n <= 14: continue
        nl += 1; Ds = list(downsets(L)); rng.shuffle(Ds)
        for D in Ds[:12]:
            inst += 1; assert not cut_counterexample_exists(L, D)
    print(f"random 5-generator lattices: {nl} lattices, {inst} instances, 0 counterexamples")
