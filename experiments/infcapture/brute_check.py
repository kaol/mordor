"""Independent brute-force check of the minimal counterexample of monotone_good_words.py (no z3).
System on P* = {p0, p1}, U* = {u0, u1}; exhaustion ({p0},{u0}) ⊂ ({p0,p1},{u0}) ⊂ ({p0,p1},{u0,u1})."""
import itertools
P = ['p0', 'p1']; U = ['u0', 'u1']
def subsets(xs): return [frozenset(c) for r in range(1, len(xs) + 1) for c in itertools.combinations(xs, r)]
cells = [(A, B) for A in subsets(P) for B in subsets(U)]
SP = {c: set() for c in cells}; SU = {c: set() for c in cells}
SU[(frozenset(['p0']), frozenset(['u0', 'u1']))] = {'u1'}
for B in [['u0'], ['u1'], ['u0', 'u1']]: SP[(frozenset(P), frozenset(B))] = {'p0'}
# system axioms
for c in cells:
    A, B = c
    assert not A <= SP[c] and not B <= SU[c] and not (SP[c] and SU[c])
    for c2 in cells:
        if c2[0] <= A and B <= c2[1]:
            assert SP[c2] <= SP[c] and SU[c] <= SU[c2]
admP = {c: sorted(c[0] - SP[c]) for c in cells}; admU = {c: sorted(c[1] - SU[c]) for c in cells}
stages = [(('p0',), ('u0',)), (('p0', 'p1'), ('u0',)), (('p0', 'p1'), ('u0', 'u1'))]
def wcells(w, A, B):
    return [(frozenset(x for x in A if x not in w[:t]), frozenset(x for x in B if x in w[:t])) for t in range(1, len(w))]
def good(w, A, B, fP, fU):
    if w[0] not in B or w[-1] not in A: return False
    cs = wcells(w, A, B)
    return sorted(fP[c] for c in cs[:len(A)]) == sorted(A) and sorted(fU[c] for c in cs[len(cs) - len(B):]) == sorted(B)
keys = cells
found = 0; total = 0
for chP in itertools.product(*[admP[c] for c in keys]):
    for chU in itertools.product(*[admU[c] for c in keys]):
        total += 1
        fP = dict(zip(keys, chP)); fU = dict(zip(keys, chU))
        G = [[w for w in itertools.permutations(A + B) if good(w, A, B, fP, fU)] for A, B in stages]
        assert all(len(g) % 2 == 1 for g in G)  # odd_goods
        for w3 in G[2]:
            w2 = tuple(x for x in w3 if x != 'u1'); w1 = tuple(x for x in w2 if x != 'p1')
            if w2 in G[1] and w1 in G[0]: found += 1; break
print(f"selector systems tried: {total}; with a compatible chain: {found}")
print("admissible P-labels:", {(tuple(sorted(c[0])), tuple(sorted(c[1]))): admP[c] for c in cells if len(admP[c]) < len(c[0])})
print("admissible U-labels:", {(tuple(sorted(c[0])), tuple(sorted(c[1]))): admU[c] for c in cells if len(admU[c]) < len(c[1])})

# every exhaustion of the 2 × 2 universe: a maximal chain of (A, B) from a singleton pair to (P*, U*)
def all_exhaustions():
    out = []
    for p in P:
        for u in U:
            start = ((p,), (u,)); rest = [x for x in P + U if x not in (p, u)]
            for order in itertools.permutations(rest):
                st = [start]; A, B = [p], [u]
                for x in order:
                    (A if x in P else B).append(x); st.append((tuple(sorted(A)), tuple(sorted(B))))
                out.append(st)
    return out
def compatible_exists(stages):
    for chP in itertools.product(*[admP[c] for c in keys]):
        for chU in itertools.product(*[admU[c] for c in keys]):
            fP = dict(zip(keys, chP)); fU = dict(zip(keys, chU))
            G = [set(w for w in itertools.permutations(A + B) if good(w, A, B, fP, fU)) for A, B in stages]
            layer = G[-1]
            for k in range(len(stages) - 1, 0, -1):
                new = set(stages[k][0] + stages[k][1]) - set(stages[k - 1][0] + stages[k - 1][1])
                layer = {tuple(x for x in w if x not in new) for w in layer} & G[k - 1]
            if layer: return True
    return False
res = [(st, compatible_exists(st)) for st in all_exhaustions()]
print("exhaustions:", len(res), "with a compatible chain:", sum(r for _, r in res))
for st, r in res:
    print("  ", [(''.join(a), ''.join(b)) for a, b in st], r)
