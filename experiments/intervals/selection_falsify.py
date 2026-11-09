"""Safe selection inside a crossing interval (log §34.3z¹²⁵; brief Programme A, D).

Instance: a finite lattice L, a monotone G : L × L → L, a cut D, a crossing interval I = [w, v] (w ∈ D, v ∉ D, w < v,
nonempty interior), S = {p : G(p) ∈ I}; G is witness-free on the crossing cells of S (x ∈ D, y ∉ D).
Traces (Lean `InterfaceTrace`): ℓ(p) = ⋁_{q ∉ S, q ≤ p} G(q), u(p) = ⋀_{q ∉ S, p ≤ q} G(q).
Range reduction (finite proxy of confinement to finitely many proper subintervals, both endpoints strict as in
`two_sided`): new values of crossing cells of S lie in the open interval (w, v).
Window of a crossing cell p = (x, y) ∈ S: W(p) = {z : ℓ(p) ≤ z ≤ u(p), w < z < v, z ≰ x, y ≰ z}; of a non-crossing
cell of S: [ℓ(p), u(p)].
Safe-selection lemma (proposed): all windows nonempty ⇒ a monotone selection p ↦ z_p ∈ W(p) exists.
Reported: instances, instances with an empty window (pinning needed), instances with all windows nonempty but no
monotone selection (counterexamples to the lemma), and the smallest counterexample.
  python3 selection_falsify.py SEED N
"""
import sys, random, itertools, json
from z3 import *
sys.path.insert(0, '../separation')
import separator_stages as ss

def chain(n): return ss.Lat(sorted([(1 << i) - 1 for i in range(n)], key=lambda x: (bin(x).count('1'), x)))
B2 = ss.Lat([0, 1, 2, 3]); C4 = chain(4)

def analyze(L, G, D, w, v):
    n = L.n; le = L.le
    cells = [(x, y) for x in range(n) for y in range(n)]
    I = lambda z: le[w][z] and le[z][v]
    S = [p for p in cells if I(G[p[0]][p[1]])]
    Sset = set(S)
    cross = lambda p: D[p[0]] and not D[p[1]]
    for (x, y) in S:
        if cross((x, y)) and (le[G[x][y]][x] or le[y][G[x][y]]): return None       # G must be witness-free there
    pl = lambda p, q: le[p[0]][q[0]] and le[p[1]][q[1]]
    def lo(p):
        z = L.bot
        for q in cells:
            if q not in Sset and pl(q, p): z = L.join[z][G[q[0]][q[1]]]
        return z
    def hi(p):
        z = L.top
        for q in cells:
            if q not in Sset and pl(p, q): z = L.meet[z][G[q[0]][q[1]]]
        return z
    W = {}
    for p in S:
        l, u = lo(p), hi(p)
        if cross(p):
            x, y = p
            W[p] = [z for z in range(n) if le[l][z] and le[z][u] and le[w][z] and le[z][v] and z != w and z != v
                    and not le[z][x] and not le[y][z]]
        else:
            W[p] = [z for z in range(n) if le[l][z] and le[z][u]]
    if not any(cross(p) for p in S): return None
    if any(not W[p] for p in S):
        return 'empty', [p for p in S if not W[p]]
    s = Solver(); Z = {p: Int(f"z_{p[0]}_{p[1]}") for p in S}
    LE = Function('LE', IntSort(), IntSort(), BoolSort())
    for a in range(n):
        for b in range(n): s.add(LE(a, b) == le[a][b])
    for p in S: s.add(Or([Z[p] == z for z in W[p]]))
    for p in S:
        for q in S:
            if p != q and pl(p, q): s.add(LE(Z[p], Z[q]))
    return ('selectable' if s.check() == sat else 'blocked'), None

def run(seed, N):
    rng = random.Random(seed); stats = dict(instances=0, empty=0, selectable=0, blocked=0); best = None
    lats = [('C4', C4), ('B2', B2)]
    for _ in range(N):
        if rng.random() < 0.3: name, L = rng.choice(lats)
        else:
            L = ss.Lat(ss.closure_system(rng.choice([3, 4]), rng.choice([3, 5, 8]), rng)); name = f"closure|L|={L.n}"
        n = L.n
        g = {(a, b): rng.randrange(n) for a in range(n) for b in range(n) if rng.random() < 0.15}
        G = ss.make_F(L, g)
        gens = [i for i in range(n) if i != L.top and rng.random() < 0.35] or [0]
        D = ss.Dof(L, gens)
        for w in range(n):
            for v in range(n):
                if not (D[w] and not D[v] and L.le[w][v] and w != v): continue
                if not any(z not in (w, v) and L.le[w][z] and L.le[z][v] for z in range(n)): continue
                r = analyze(L, G, D, w, v)
                if r is None: continue
                stats['instances'] += 1; stats[r[0]] += 1
                if r[0] == 'blocked' and (best is None or n < best['n']):
                    best = dict(n=n, lattice=name, sets=L.S, G=G, D=[i for i in range(n) if D[i]], interval=(w, v))
    print(json.dumps(stats))
    if best:
        print(f"smallest counterexample to safe selection: {best['lattice']} (|L| = {best['n']}), interval {best['interval']}, D = {best['D']}")
        json.dump(best, open(f'selection_counterexample_s{seed}.json', 'w'))

if __name__ == '__main__':
    run(int(sys.argv[1]), int(sys.argv[2]))
