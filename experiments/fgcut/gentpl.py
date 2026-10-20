"""Generalised two-pointer lemma: D0 ⊊ P a down-set ∋ ⊥, U0 ⊊ Q an up-set ∋ ⊤; interior (P∖D0)×(Q∖U0);
H: x ≰ f, g ≰ y on the interior. Claim: some interior cell has f ∈ D0 and g ∈ U0."""
import itertools
from twoptr import *

def downsets(L):
    out = []
    for mask in range(1 << L.n):
        S = {i for i in range(L.n) if mask >> i & 1}
        if L.bot in S and L.top not in S and all(z in S for s in S for z in range(L.n) if L.leq[z][s]): out.append(S)
    return out

def gtest(L1, D0, L2, U0):
    n1, n2 = L1.n, L2.n; cells = [(x, y) for x in range(n1) for y in range(n2)]
    v = {}
    def var(k):
        if k not in v: v[k] = len(v) + 1
        return v[k]
    S = Cadical153()
    for c in cells:
        S.add_clause([var(('f', c, a)) for a in range(n1)]); S.add_clause([var(('g', c, b)) for b in range(n2)])
        for a, a2 in itertools.combinations(range(n1), 2): S.add_clause([-var(('f', c, a)), -var(('f', c, a2))])
        for b, b2 in itertools.combinations(range(n2), 2): S.add_clause([-var(('g', c, b)), -var(('g', c, b2))])
        x, y = c
        if x not in D0 and y not in U0:
            for a in range(n1):
                if L1.leq[x][a]: S.add_clause([-var(('f', c, a))])
            for b in range(n2):
                if L2.leq[b][y]: S.add_clause([-var(('g', c, b))])
            for a in D0:
                for b in U0: S.add_clause([-var(('f', c, a)), -var(('g', c, b))])
    for c in cells:
        for c2 in cells:
            if c != c2 and L1.leq[c[0]][c2[0]] and L2.leq[c[1]][c2[1]]:
                for a in range(n1):
                    for a2 in range(n1):
                        if not L1.leq[a][a2]: S.add_clause([-var(('f', c, a)), -var(('f', c2, a2))])
                for b in range(n2):
                    for b2 in range(n2):
                        if not L2.leq[b][b2]: S.add_clause([-var(('g', c, b)), -var(('g', c2, b2))])
    return S.solve()

if __name__ == '__main__':
    Ps = [lat.chain(3), lat.powerset(2), lat.M(3), lat.N5(), bowtie, W, Mp]
    bad = 0; tot = 0
    for A in Ps:
        for B in Ps:
            for D0 in downsets(A):
                for Dq in downsets(B):
                    U0 = set(range(B.n)) - Dq
                    tot += 1
                    if gtest(A, D0, B, U0):
                        bad += 1
                        if bad <= 5: print('SAT', A.name, sorted(D0), B.name, sorted(U0), flush=True)
    print(f'{bad} SAT of {tot}')
