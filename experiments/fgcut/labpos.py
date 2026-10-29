"""Join-free labellings for the finite reduced theory (log §34.3z²⁹).  Column poset C (finite, with top), generators [k].
Cells (A, B): A ⊆ [k] nonempty, B ⊆ C nonempty with a least upper bound in C (mode sup), or a chain (mode chains:
the chain labelling lemma), or a singleton (mode single); noW1 / noW2 are controls.  Cell value z ∈ D-labels or C:
  alpha(c) ⊆ [k] (labels of z if z ∈ D), zc(c) ∈ C ∪ {none} (z if z is a column); exactly one nonempty.
  W1: A ⊄ alpha.  W2 + sup: B ⊄ ↓zc.  Monotone: (A,B) ≤ (A',B') iff A ⊇ A', B ⊆ B'  ⇒  z ≤ z'.
Sound for the reduced theory: a finite reduced model gives a labelling.   python3 labpos.py k n [mode]"""
import sys, itertools
from pysat.solvers import Cadical195
K, N = int(sys.argv[1]), int(sys.argv[2])
MODE = sys.argv[3] if len(sys.argv) > 3 else 'sup'   # sup | chains | single | noW1 | noW2
def posets(n):          # all partial orders on range(n) with n-1 = top, up to labelling (naive, small n)
    seen = set(); pairs = [(i, j) for i in range(n - 1) for j in range(n - 1) if i != j]
    for bits in itertools.product([0, 1], repeat=len(pairs)):
        le = [[i == j or j == n - 1 for j in range(n)] for i in range(n)]
        for (i, j), b in zip(pairs, bits):
            if b: le[i][j] = True
        ok = all(not (le[i][j] and le[j][i]) for i in range(n) for j in range(n) if i != j) and \
             all(not (le[i][j] and le[j][k]) or le[i][k] for i in range(n) for j in range(n) for k in range(n))
        if not ok: continue
        key = min(tuple(le[p[i]][p[j]] for i in range(n) for j in range(n)) for p in
                  [list(q) + [n - 1] for q in itertools.permutations(range(n - 1))])
        if key in seen: continue
        seen.add(key); yield le
def solve(le, n):
    C = range(n)
    def sup(B):
        ub = [u for u in C if all(le[b][u] for b in B)]
        least = [u for u in ub if all(le[u][w] for w in ub)]
        return least[0] if least else None
    chain = lambda B: all(le[a][b] or le[b][a] for a in B for b in B)
    keepB = {'chains': chain, 'single': lambda B: len(B) == 1}.get(MODE, lambda B: True)
    Bs = [frozenset(B) for r in range(1, n + 1) for B in itertools.combinations(C, r) if sup(B) is not None and keepB(B)]
    As = [frozenset(A) for r in range(1, K + 1) for A in itertools.combinations(range(K), r)]
    cells = [(A, B) for A in As for B in Bs]
    nv = [0]
    def new(): nv[0] += 1; return nv[0]
    al = {c: [new() for _ in range(K)] for c in cells}
    zc = {c: [new() for _ in C] for c in cells}       # one-hot or none
    isc = {c: new() for c in cells}
    cl = []
    for c in cells:
        A, B = c
        cl.append([-isc[c]] + zc[c]); cl += [[isc[c], -v] for v in zc[c]]
        cl += [[-zc[c][u], -zc[c][w]] for u in C for w in C if u < w]
        cl += [[-isc[c], -a] for a in al[c]]; cl.append([isc[c]] + al[c])         # exactly one of α ≠ ∅, z column
        if MODE != 'noW1': cl.append([-al[c][i] for i in A])                       # W1
        for u in C:
            if MODE != 'noW2' and all(le[b][u] for b in B): cl.append([-zc[c][u]])                    # W2 + sup: some b ∈ B with b ≰ z
    for c in cells:
        for d in cells:
            if c != d and c[0] >= d[0] and c[1] <= d[1]:
                for i in range(K): cl.append([-al[d][i], al[c][i]])  # α antitone
                cl.append([-isc[c], isc[d]])                                        # column stays column
                for u in C:
                    cl.append([-zc[c][u]] + [zc[d][w] for w in C if le[u][w]])      # z monotone
    cl = [x for x in cl if x != []]
    s = Cadical195(bootstrap_with=cl); return s.solve(), len(cells)
tot = sat = 0
for le in posets(N):
    r, nc = solve(le, N); tot += 1
    if r:
        sat += 1
        if sat <= 3: print(' SAT on poset', [(i, j) for i in range(N) for j in range(N) if i != j and le[i][j] and j != N - 1])
print(f"k={K} n={N} {MODE}: {tot} posets, {sat} SAT")
