"""Anatomy of the Lean-checked ground certificates CutHeight4.lean / CutHeight5.lean (log §34.3z¹¹⁹; brief C1).

Parses the term equations `t i = F (t a) (t b)` and the clause instances `cl_<family> ...` of the generated Lean file
(a drat-trim core, not a minimal one) and reports: clause families; the rows (first arguments) used and how many
cells each row has; the ⊥-row share; orbit chains (t_{k+1} = F(r, t_k) with the same row r); which terms occur in the
no-witness clauses (cl_now1: F(x,y) ≰ x side, cl_now2: y ≰ F(x,y) side) and in the down-set / rank clauses.
  python3 core_anatomy.py ../../lean/Mordor/CutHeight5.lean"""
import re, sys, collections

src = open(sys.argv[1]).read()
eqs = {int(i): (int(a), int(b)) for i, a, b in re.findall(r"\(e(\d+) : t \d+ = F \(t (\d+)\) \(t (\d+)\)\)", src)}
names = {0: '⊥', 1: '⊤'}
fam = collections.Counter(re.findall(r"cl_([a-z0-9_]+)", src))
now1 = [int(x) for x in re.findall(r"cl_now1 H e(\d+)", src)]
now2 = [int(x) for x in re.findall(r"cl_now2 H e(\d+)", src)]
mono = re.findall(r"cl_mono H e(\d+) e(\d+)", src)
rows = collections.Counter(a for a, b in eqs.values())
cols = collections.Counter(b for a, b in eqs.values())
depth = {0: 0, 1: 0}
for i in sorted(eqs):
    a, b = eqs[i]; depth[i] = 1 + max(depth[a], depth[b])
def show(i): return names.get(i, f"t{i}")
print(f"{sys.argv[1].split('/')[-1]}: {len(eqs)} F-terms, max depth {max(depth.values())}")
print("clause families:", dict(sorted(fam.items(), key=lambda kv: -kv[1])))
print(f"rows used: {len(rows)} distinct; ⊥-row cells: {rows.get(0, 0)} of {len(eqs)}; ⊤ as column: {cols.get(1, 0)}")
print("cells per row (row: count):", ", ".join(f"{show(r)}:{n}" for r, n in rows.most_common()))
# orbits from ⊤: t_{k+1} = F(r, t_k), starting at F(r, ⊤)
inv = {v: k for k, v in eqs.items()}
orbits = {}
for r in rows:
    o = [1]
    while (r, o[-1]) in inv: o.append(inv[(r, o[-1])])
    if len(o) > 1: orbits[r] = o
print("orbits from ⊤ present (row: length):", ", ".join(f"{show(r)}:{len(o) - 1}" for r, o in sorted(orbits.items())))
on_orbit = {x for o in orbits.values() for x in o[1:]}
print(f"terms on some orbit from ⊤: {len(on_orbit)} of {len(eqs)}")
print(f"no-witness instances: F≰x side on {len(set(now1))} cells, y≰F side on {len(set(now2))} cells; "
      f"cells with both: {len(set(now1) & set(now2))}")
print(f"monotonicity instances: {len(mono)} (distinct cell pairs {len(set(mono))})")
