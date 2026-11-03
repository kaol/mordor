"""Dependency structure of the height-4 and height-5 certificate terms (log §34.3z⁹⁵).

For T4 (17 terms) and T5 (86 terms): roles (row / column use), generation levels of T5 over T4
(L0 = T4, L_{n+1} = L_n ∪ {F(r, c) ∈ T5 : r, c ∈ L_n}), the row × column grid each certificate fills, and the size of
the naive one-step closure pools. Uses the parser of classify.py."""
import collections, itertools
from classify import parse, parse_term, tok
def load(path, name):
    return {k: parse_term(tok(v))[0] for k, v in parse(path, name).items()}
T4 = load("../../lean/Mordor/CutHeight4.lean", "tv4"); T5 = load("../../lean/Mordor/CutHeight5.lean", "tv5")
S4, S5 = set(T4.values()), set(T5.values())
def roles(S):
    rows, cols = set(), set()
    for t in S:
        if not isinstance(t, str): rows.add(t[1]); cols.add(t[2])
    return rows, cols
for H, S in [(4, S4), (5, S5)]:
    R, Cc = roles(S)
    Fterms = [t for t in S if not isinstance(t, str)]
    print(f"H={H}: {len(Fterms)} F-terms; rows used {len(R)}; columns used {len(Cc)}; grid {len(R)}x{len(Cc)} = "
          f"{len(R)*len(Cc)} cells, filled {len(Fterms)} ({100*len(Fterms)/(len(R)*len(Cc)):.0f}%)")
    print(f"   terms used both as row and as column: {len(R & Cc)}")
L = set(S4); lev = 0; sizes = [len(L & S5)]
while True:
    new = {t for t in S5 if not isinstance(t, str) and t[1] in L and t[2] in L} - L
    if not new: break
    L |= new; lev += 1; sizes.append(len(L))
print(f"T5 generated from T4 in {lev} closure levels (sizes {sizes}); covered {len(L & S5)} of {len(S5)}")
R4, C4 = roles(S4)
pool1 = {("F", r, c) for r in S4 for c in S4}
print(f"naive one-step pool F(T4, T4): {len(pool1)} terms, contains {len(pool1 & S5)} of the {len(S5 - S4)} new T5 terms")
