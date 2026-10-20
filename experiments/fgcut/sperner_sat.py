"""Product Sperner lemma by SAT (log §34.3n): no pair of Sperner labellings avoids every good maximal chain;
random labellings give odd counts. Slow beyond (3,3)."""
import itertools, random, sys
from pysat.solvers import Cadical153
def subsets(n): return [frozenset(c) for r in range(1, n+1) for c in itertools.combinations(range(n), r)]
def chains(k, l):
    out = []
    def covers(c):
        A, B = c
        return [(A - {i}, B) for i in sorted(A) if len(A) > 1] + [(A, B | {j}) for j in range(l) if j not in B]
    def ext(ch):
        cs = covers(ch[-1])
        if not cs: out.append(ch); return
        for d in cs: ext(ch + [d])
    for j in range(l): ext([(frozenset(range(k)), frozenset([j]))])
    return out
def good(ch, l1, l2, k, l):
    return len({l1[c] for c in ch[:k]}) == k and len({l2[c] for c in ch[k-1:]}) == l
def sat(k, l):
    cells = [(A, B) for A in subsets(k) for B in subsets(l)]; v = {}
    var = lambda key: v.setdefault(key, len(v) + 1)
    S = Cadical153()
    for c in cells:
        A, B = c
        S.add_clause([var(('1', c, i)) for i in A]); S.add_clause([var(('2', c, j)) for j in B])
    for ch in chains(k, l):
        for pi in itertools.permutations(range(k)):
            for rho in itertools.permutations(range(l)):
                lits = [var(('1', ch[t], pi[t])) for t in range(k)] + [var(('2', ch[k-1+s], rho[s])) for s in range(l)]
                S.add_clause([-x for x in lits])
    return S.solve()
def parity(k, l, trials):
    cells = [(A, B) for A in subsets(k) for B in subsets(l)]; chs = chains(k, l); res = set()
    for _ in range(trials):
        l1 = {c: random.choice(sorted(c[0])) for c in cells}; l2 = {c: random.choice(sorted(c[1])) for c in cells}
        res.add(sum(good(ch, l1, l2, k, l) for ch in chs) % 2)
    return res
for k, l in [(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(2,4),(4,2),(3,4)]:
    print((k, l), 'chains', len(chains(k, l)), 'exists-always:', not sat(k, l), 'parities seen:', parity(k, l, 300), flush=True)
