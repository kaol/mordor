"""Product Sperner lemma (log §34.3n), checked on the exact definitions of `lean/Mordor/Sperner.lean`.

Words = orderings of P ⊔ Q starting in Q and ending in P = maximal chains of the cell poset. Cells of prefixes;
good = λ1 bijective onto P on the first k cells and λ2 bijective onto Q on the last l cells. Checks: the per-chain
door parity, swap invariance of facets, boundary doors = good words of (P ∖ i0, Q), oddness, and the k = 1 base case.
"""
import itertools, random
from collections import Counter
def run(k, l, trials=50):
    P = list(range(k)); Q = list(range(l)); i0 = k - 1
    letters = [('L', i) for i in P] + [('R', j) for j in Q]
    def valid(w): return w[0][0] == 'R' and w[-1][0] == 'L'
    def cellOf(Pset, Qset, S):
        return (frozenset(a for a in Pset if ('L', a) not in S), frozenset(b for b in Qset if ('R', b) in S))
    def cells(Pset, Qset, w): return [cellOf(Pset, Qset, set(w[:t+1])) for t in range(len(w) - 1)]
    for _ in range(trials):
        l1, l2 = {}, {}
        def L1(c):
            if c not in l1: l1[c] = random.choice(sorted(c[0]))
            return l1[c]
        def L2(c):
            if c not in l2: l2[c] = random.choice(sorted(c[1]))
            return l2[c]
        def good(kk, Pset, Qset, cs):
            return Counter(L1(c) for c in cs[:kk]) == Counter(Pset) and Counter(L2(c) for c in cs[kk-1:]) == Counter(Qset)
        def door(f):
            return Counter(L1(c) for c in f[:k-1]) == Counter(a for a in P if a != i0) and Counter(L2(c) for c in f[k-2:]) == Counter(Q)
        W = [w for w in itertools.permutations(letters) if valid(w)]
        G = 0; Dtot = 0; Dbd = 0
        for w in W:
            cs = cells(P, Q, w); g = good(k, P, Q, cs); G += g
            doors = [t for t in range(len(cs)) if door(cs[:t] + cs[t+1:])]
            assert len(doors) % 2 == g, ('perchain', w)
            for t in doors:
                Dtot += 1
                n = len(w)
                if (t == 0 and w[1][0] == 'L') or (t == n - 2 and w[n-2][0] == 'R'):
                    Dbd += 1
                    assert t == 0 and w[1] == ('L', i0)
                else:
                    w2 = list(w); w2[t], w2[t+1] = w2[t+1], w2[t]; w2 = tuple(w2)
                    assert valid(w2)
                    cs2 = cells(P, Q, w2)
                    assert cs2[:t] + cs2[t+1:] == cs[:t] + cs[t+1:]
        P2 = [a for a in P if a != i0]
        letters2 = [('L', i) for i in P2] + [('R', j) for j in Q]
        G2 = sum(good(k-1, P2, Q, cells(P2, Q, w)) for w in itertools.permutations(letters2) if valid(w))
        assert Dbd == G2, (Dbd, G2)
        assert G % 2 == 1
    print((k, l), 'ok')
for k, l in [(2,1),(2,2),(3,1),(2,3),(3,2),(3,3)]: run(k, l)
# base case k = 1: exactly one good word
def base(l, trials=50):
    for _ in range(trials):
        lab = {}
        def L2(B):
            if B not in lab: lab[B] = random.choice(sorted(B))
            return lab[B]
        cnt = 0
        for u in itertools.permutations(range(l)):
            cs = [frozenset(u[:t+1]) for t in range(l)]
            cnt += Counter(L2(B) for B in cs) == Counter(range(l))
        assert cnt == 1
    print('base l =', l, 'count 1')
for l in range(1, 6): base(l)
