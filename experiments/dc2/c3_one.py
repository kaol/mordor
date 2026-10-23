"""Run one (pattern, k) instance of the M_ω² × C_n DC2 check with an explicit closure, appending one JSON result line.
usage: c3_one.py CLOSURE_JSON_FILE K OUT_FILE [n=3]
CLOSURE_JSON_FILE holds one line {"tag": ..., "k": "closure", "w": ..., "cells": [...]} (as printed by c3_widen.py).
Run one process per k = 0 .. 2w in parallel; results merge with the driver's files (c3_summary.py reads them all)."""
import sys, json, time
import c3, dc2_lazy as d
from thick_patterns import width

cl = json.loads(open(sys.argv[1]).read().strip().splitlines()[-1])
k = int(sys.argv[2]); out = sys.argv[3]; n = int(sys.argv[4]) if len(sys.argv) > 4 else 3
tag = cl['tag']; cells = [(tuple(c[0]), tuple(c[1])) for c in cl['cells']]
pat = next(p for p in c3.all_patterns(n) if c3.tag(p, n) == tag)
d.PREC_L2 = False; d.BLOCK_MAXL1 = 1
d.DPAT = pat; d.ZERO0 = None; d.SEL0 = False
shapes = c3.find_shapes(pat, cells, n) if k > 0 else []
d.DPAT = pat; d.CLOSED0 = lambda x, y, cs=set(cells): (x, y) in cs
closed1 = set(c for i in range(k) for c in c3.inst(shapes, ('a', i)))
d.CLOSED1 = lambda x, y: (x, y) in closed1
t0 = time.time()
d.SKIP_BLOCKS = True
rm = d.run(k, 1, n, verbose=False)
d.SKIP_BLOCKS = False
if not rm:
    rec = {'tag': tag, 'k': k, 'res': 'UNSAT', 'how': 'master', 's': round(time.time() - t0)}
else:
    m = 2 * width(sorted(closed1, key=str)) if k else 0
    r = d.run(k, m, n, verbose=False)
    rec = {'tag': tag, 'k': k, 'm': m, 'res': 'SAT' if r else 'UNSAT', 'how': 'lazy', 's': round(time.time() - t0)}
with open(out, 'a') as f: f.write(json.dumps(rec) + '\n')
print(rec, flush=True)
