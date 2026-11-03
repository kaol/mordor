"""Feedback-core structure of the verified height-4 / height-5 certificates (log §34.3z⁹⁶).

Terms form a DAG under the subterm relation (no cycles, so its strongly connected components are singletons).
Feedback vertices = terms used both as a row and as a column. For each: depth, first role at H = 4 (if present), and
whether its row/column uses at H = 5 were already present at H = 4. Also: how the 69 new H = 5 terms split by whether
their row and column were already used in that role at H = 4, and the grid-restricted H = 6 pool size
{F(r, c) : r ∈ rows(T5), c ∈ cols(T5)}."""
import collections
from classify import parse, parse_term, tok, depth
def load(path, name): return {k: parse_term(tok(v))[0] for k, v in parse(path, name).items()}
T4 = load("../../lean/Mordor/CutHeight4.lean", "tv4"); T5 = load("../../lean/Mordor/CutHeight5.lean", "tv5")
idx5 = {t: k for k, t in T5.items()}
def roles(S):
    R, C = collections.Counter(), collections.Counter()
    for t in S:
        if not isinstance(t, str): R[t[1]] += 1; C[t[2]] += 1
    return R, C
S4, S5 = set(T4.values()), set(T5.values())
R4, C4 = roles(S4); R5, C5 = roles(S5)
fb4 = set(R4) & set(C4); fb5 = set(R5) & set(C5)
print(f"feedback vertices: H=4 {len(fb4)}, H=5 {len(fb5)}; H=4 feedback still feedback at H=5: {len(fb4 & fb5)}")
for t in sorted(fb5, key=lambda t: idx5[t]):
    old = "in T4" if t in S4 else "new"
    r4 = "row@4" if t in R4 else ""; c4 = "col@4" if t in C4 else ""
    print(f"   term {idx5[t]:2d} depth {depth(t)} ({old}; {r4} {c4}) rows-use {R5[t]} cols-use {C5[t]}")
new = [t for t in S5 - S4 if not isinstance(t, str)]
cat = collections.Counter()
for t in new:
    cat[("row-old" if t[1] in R4 else ("row-T4" if t[1] in S4 else "row-new"),
         "col-old" if t[2] in C4 else ("col-T4" if t[2] in S4 else "col-new"))] += 1
print("new H=5 terms by provenance of (row, column):")
for k, v in sorted(cat.items(), key=lambda kv: -kv[1]): print(f"   {k}: {v}")
pool = {("F", r, c) for r in R5 for c in C5} | S5
print(f"grid-restricted H=6 pool rows(T5) x cols(T5) ∪ T5: {len(pool)} terms (vs |F(T5,T5)| = {len(S5)**2})")
