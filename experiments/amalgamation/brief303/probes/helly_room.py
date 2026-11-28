"""Room report for the Helly2 runs (free analysis of dumped mutant models): number of distinct colour-row landings,
how many lie in Z, number of pair-joins, |A|, and whether some three colour-row landings pairwise meet."""
import json, glob, itertools
from alib import *
for f in sorted(glob.glob('../runs/r*/plu_helly*.json')):
    D=json.load(open(f)); rows=[]
    for d in D:
        M=Mod(d['sets'],d['F']); lams={M.lam(c) for c in M.cols}
        tri=any(all(set(M.C(p))&set(M.C(q)) for p,q in itertools.combinations(T,2)) and not set.intersection(*[set(M.C(p)) for p in T]) for T in itertools.combinations(lams,3))
        rows.append((len(lams), sum(p in M.Zs for p in lams), len(M.pjs), len(M.cols), tri, d["N"]))
    print(f.split('/')[-1], len(D), 'max distinct colour landings', max(r[0] for r in rows), 'max in Z', max(r[1] for r in rows),
          'max #pj', max(r[2] for r in rows), '|A|', sorted({r[3] for r in rows}), 'models with a triangle of landings', sum(r[4] for r in rows), 'N', sorted({r[5] for r in rows}))
