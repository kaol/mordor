"""Where do Cut witnesses live? (log §34.3m)

For a lattice L, a down-set D (⊥ ∈ D, ⊤ ∉ D) and a set C of cells (x ∈ D, y ∉ D), SAT decides whether some monotone
F : L × L → L has no witness in C (witness: F(x,y) ≤ x or y ≤ F(x,y)). UNSAT means every F has a witness in C.
Candidate cell sets are defined from the boundary of D: max D, min U (U = L ∖ D), ⊥, ⊤.

  python3 locate.py 6 7          # all lattices with 6 and 7 elements"""
import sys, os, itertools
from pysat.solvers import Cadical153
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'gpu'))
import lattices as LT


def downsets(L):
    n, leq = L.n, L.leq
    for mask in range(1 << n):
        D = [x for x in range(n) if mask >> x & 1]
        Ds = set(D)
        if L.bot not in Ds or L.top in Ds: continue
        if any(leq[y, x] and y not in Ds for x in D for y in range(n)): continue
        yield frozenset(D)


def product_covers(L):
    cov = L.covers
    cells = [(x, y) for x in range(L.n) for y in range(L.n)]
    out = []
    for (x, y) in cells:
        for (a, b) in cov:
            if a == x: out.append(((x, y), (b, y)))
            if a == y: out.append(((x, y), (x, b)))
    return out


class Solver:
    """One CNF per lattice (monotone F, one-hot); witness-freedom added under assumptions per (D, C)."""
    def __init__(self, L):
        self.L = L; n = L.n; leq = L.leq
        self.var = {}; c = 0
        for x in range(n):
            for y in range(n):
                for k in range(n): c += 1; self.var[(x, y, k)] = c
        self.S = Cadical153()
        for x in range(n):
            for y in range(n):
                lits = [self.var[(x, y, k)] for k in range(n)]
                self.S.add_clause(lits)
                for i, j in itertools.combinations(lits, 2): self.S.add_clause([-i, -j])
        for (c1, c2) in product_covers(L):
            for k in range(n):
                for k2 in range(n):
                    if not leq[k, k2]: self.S.add_clause([-self.var[c1 + (k,)], -self.var[c2 + (k2,)]])

    def no_witness_possible(self, D, C):
        """Is there a monotone F with no witness on the cells C?"""
        n, leq = self.L.n, self.L.leq
        assum = []
        for (x, y) in C:
            for k in range(n):
                if leq[k, x] or leq[y, k]: assum.append(-self.var[(x, y, k)])
        return self.S.solve(assumptions=assum)


def cellsets(L, D):
    n, leq = L.n, L.leq
    U = [y for y in range(n) if y not in D]
    maxD = [x for x in D if not any(leq[x, z] and z != x for z in D)]
    minU = [y for y in U if not any(leq[z, y] and z != y for z in U)]
    allc = [(x, y) for x in D for y in U]
    return {
        'all': allc,
        'bot row ∪ top col': [(x, y) for (x, y) in allc if x == L.bot or y == L.top],
        'maxD ∪ minU lines': [(x, y) for (x, y) in allc if x in maxD or y in minU],
        'maxD × minU': [(x, y) for x in maxD for y in minU],
        'maxD rows': [(x, y) for (x, y) in allc if x in maxD],
        'minU cols': [(x, y) for (x, y) in allc if y in minU],
        'bot row ∪ maxD rows': [(x, y) for (x, y) in allc if x == L.bot or x in maxD],
        'top col ∪ minU cols': [(x, y) for (x, y) in allc if y == L.top or y in minU],
        'bot/top lines ∪ maxD×minU': [(x, y) for (x, y) in allc if x == L.bot or y == L.top or (x in maxD and y in minU)],
    }


if __name__ == '__main__':
    names = None; fails = {}; tot = 0
    for size in map(int, sys.argv[1:]):
        for L in LT.all_lattices(size):
            S = Solver(L)
            for D in downsets(L):
                cs = cellsets(L, D); names = list(cs)
                tot += 1
                for k, C in cs.items():
                    if S.no_witness_possible(D, C):
                        fails.setdefault(k, []).append((L.name, sorted(D)))
    print(f"(lattice, down-set) pairs: {tot}")
    for k in names:
        f = fails.get(k, [])
        print(f"  {k:28s} fails on {len(f):5d}" + (f"   e.g. {f[0]}" if f else ""))
