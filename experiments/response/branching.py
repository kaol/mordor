"""Branch-complete frontier trees (log §34.3z⁹⁵), z3.

Root frontier pair (x, y): z = F(x, y), a = y ⊓ z ∈ D, b = x ⊔ z ∉ D. Split: case A (z ∈ D) children (x, b), (z, b);
case B (z ∉ D) children (a, y), (a, z). Every child is terminalized: its frontier pair (x', y') has x' ≥ child row,
y' ≤ child column, and its own z', a' ∈ D, b' ∉ D; then it splits again (depth 2). Named partial model: generators,
pairwise meets (glbs), anchors (lubs), all pair elements; cells: every anchor row and every generator row at every
named outside column, and each pair's own cell F(x, y); monotone, witness-free on cross cells; nothing on D × D.
Question: is the whole tree consistent with NO anchor transfer at any named outside column
(¬ F(cᵢ, u) ≤ pⱼ for i ≠ j)? If so, the branch-alignment lemma has no local content at this depth."""
import itertools, sys
from z3 import *

def run(K, pattern, depth, notransfer=True):
    I = list(range(1, K + 1)); P = [f"p{i}" for i in I]
    pairs = list(itertools.combinations(I, 2))
    M = {f"m{a}{b}": [f"p{a}", f"p{b}"] for a, b in pairs}
    C = {f"c{i}": [f"m{min(i,j)}{max(i,j)}" for j in I if j != i] for i in I} if K >= 2 else {}
    nodes = []          # (name, parent, case, childrow, childcol)
    elems = ['bot', 'top'] + P + list(M) + list(C)
    def node_elems(n): return [f"x{n}", f"y{n}", f"z{n}", f"a{n}", f"b{n}"]
    # tree: node 0 root; children of node n: 2n+1, 2n+2 (binary heap), up to given depth
    N = 2 ** (depth + 1) - 1
    for n in range(N): elems += node_elems(n)
    cases = {n: pattern[n] for n in range(min(N, len(pattern)))}
    rows_fixed = P + list(C)
    cols_named = ['top'] + [f"y{n}" for n in range(N)] + [f"b{n}" for n in range(N)] + [f"z{n}" for n in range(N)]
    cell = {(r, c): f"F[{r},{c}]" for r in rows_fixed for c in cols_named}
    for n in range(N): cell[(f"x{n}", f"y{n}")] = f"F[x{n},y{n}]"
    E = list(dict.fromkeys(elems + list(cell.values())))
    s = Solver(); le = {(u, v): Bool(f"le|{u}|{v}") for u in E for v in E}
    for u in E:
        s.add(le[u, u], le['bot', u], le[u, 'top'])
        for v in E:
            for w in E: s.add(Implies(And(le[u, v], le[v, w]), le[u, w]))
    inD = {u: Or([le[u, q] for q in P]) for u in E}
    for u, v in itertools.permutations(P, 2): s.add(Not(le[u, v]))
    def glb(zz, xs): s.add([le[zz, q] for q in xs]); s.add([Implies(And([le[w, q] for q in xs]), le[w, zz]) for w in E])
    def lub(zz, xs): s.add([le[q, zz] for q in xs]); s.add([Implies(And([le[q, w] for q in xs]), le[zz, w]) for w in E])
    for k, v in M.items(): glb(k, v)
    for k, v in C.items(): lub(k, v)
    if K == 3: s.add(Not(le['m23', 'p1']), Not(le['m13', 'p2']), Not(le['m12', 'p3']))
    s.add(Not(inD['top']))
    for (r, c), v in cell.items():
        for (r2, c2), v2 in cell.items():
            if (r, c) != (r2, c2): s.add(Implies(And(le[r, r2], le[c, c2]), le[v, v2]))
        s.add(Implies(And(inD[r], Not(inD[c])), And(Not(le[v, r]), Not(le[c, v]))))
    eq = lambda u, v: And(le[u, v], le[v, u])
    for n in range(N):
        x, y, z, a, b = node_elems(n)
        s.add(inD[x], Not(inD[y]), eq(z, cell[(x, y)]))
        glb(a, [y, z]); lub(b, [x, z]); s.add(inD[a], Not(inD[b]))
        if n in cases: s.add(inD[z] if cases[n] == 'A' else Not(inD[z]))
        for ch, which in [(2 * n + 1, 0), (2 * n + 2, 1)]:
            if ch >= N: continue
            if cases.get(n, 'B') == 'A': cr, cc = (x, b) if which == 0 else (z, b)
            else: cr, cc = (a, y) if which == 0 else (a, z)
            s.add(le[cr, f"x{ch}"], le[f"y{ch}", cc])
    if notransfer and K >= 2:
        for u in cols_named:
            for i in I:
                for j in I:
                    if i != j: s.add(Implies(Not(inD[u]), Not(le[cell[(f"c{i}", u)], f"p{j}"])))
    return s.check()

for K in [1, 2, 3]:
    for depth in [1, 2]:
        for pat in (["B", "BB", "AB"] if K == 1 else ["A", "B", "AAB", "BAB", "BBB"]):
            if depth == 1 and len(pat) > 1 and False: continue
            p = (pat * 7)[: 2 ** (depth + 1) - 1] if len(pat) == 1 else pat
            if K == 1 and 'A' in p: continue
            print(f"k={K} depth={depth} cases {p}: no transfer anywhere -> {run(K, p, depth)}", flush=True)
