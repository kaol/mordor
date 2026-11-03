"""Classify the F-terms of the verified height-4 and height-5 certificates (log §34.3z⁹⁴).

Parses `tv4`/`tv5` from lean/Mordor/CutHeight{4,5}.lean. Every term is ⊥, ⊤ or F(r, c). Classes:
  descent      F(⊥, c) with c = ⊤ or a descent term       (the bottom-column orbit c_k = F(⊥, c_{k-1}))
  row-iter     F(r, c) with r an F-term and c a descent term or ⊤ (a new row applied to the initial column/box)
  col-iter     F(⊥, c) with c not a descent term          (bottom row applied to a non-descent column)
  mixed        F(r, c) with r an F-term and c a non-descent F-term
Also reports: the height-4 terms that are height-5 terms (inclusion), depth profile, and which F-values are used as
rows (the "escaped values re-entered as inputs")."""
import re, sys, collections
def parse(path, name):
    txt = open(path).read()
    block = txt[txt.index(f"def {name}"):]
    terms = {}
    for m in re.finditer(r"\|\s*(\d+)\s*=>\s*(.+)", block):
        idx = int(m.group(1)); t = m.group(2).strip()
        if t.startswith("F") or t in ("⊥", "⊤"): terms[idx] = t
        if idx > 0 and not (t.startswith("F") or t in ("⊥", "⊤")): break
    return terms
def tok(s):
    s = s.replace("(", " ( ").replace(")", " ) ")
    return s.split()
def parse_term(toks, i=0):
    t = toks[i]
    if t == "(":
        v, i = parse_term(toks, i + 1); assert toks[i] == ")"; return v, i + 1
    if t in ("⊥", "⊤"): return t, i + 1
    assert t == "F"
    r, i = parse_term(toks, i + 1); c, i = parse_term(toks, i)
    return ("F", r, c), i
def depth(t): return 0 if isinstance(t, str) else 1 + max(depth(t[1]), depth(t[2]))
for H, path, name in [(4, "../../lean/Mordor/CutHeight4.lean", "tv4"), (5, "../../lean/Mordor/CutHeight5.lean", "tv5")]:
    raw = parse(path, name)
    T = {k: parse_term(tok(v))[0] for k, v in raw.items()}
    desc = set(); cur = "⊤"
    while True:
        cur = ("F", "⊥", cur)
        if cur in T.values(): desc.add(cur)
        else: break
    cls = collections.Counter(); rows = collections.Counter(); byclass = collections.defaultdict(list)
    for k, t in sorted(T.items()):
        if isinstance(t, str): continue
        _, r, c = t
        if r == "⊥": kind = "descent" if (c == "⊤" or c in desc) else "col-iter"
        else: kind = "row-iter" if (c == "⊤" or c in desc) else "mixed"
        cls[kind] += 1; byclass[kind].append(k)
        if r != "⊥": rows[r] += 1
    print(f"H={H}: {len(T)} terms (incl. ⊥, ⊤); descent length {len(desc)}; classes {dict(cls)}")
    print(f"   distinct F-terms used as rows: {len(rows)}; max depth {max(depth(t) for t in T.values())}")
    for r, n in rows.most_common(6):
        rk = [k for k, t in T.items() if t == r][0]
        print(f"   row term {rk} used {n} times")
    globals()[f"T{H}"] = set(T.values())
print(f"H=4 terms contained in H=5 terms: {len(T4 & T5)} of {len(T4)}")
