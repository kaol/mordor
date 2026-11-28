"""Summarize the SAT models dumped by plu_probe runs: per file and mode, count, N values, |A|, branch, max |C(m)|."""
import json, glob, collections
for f in sorted(glob.glob('../runs/r*/plu_*.json')):
    D=json.load(open(f)); by=collections.defaultdict(list)
    for d in D: by[d['mode']].append(d)
    for md,L in by.items():
        print(f.split('/')[-2], f.split('/')[-1][:60], md, len(L), 'N', sorted({d['N'] for d in L}), '|A|', sorted({len(d['cols']) for d in L}),
              'branch', sorted({d['branch'] for d in L}), 'max|C(m)|', max(d['Cm'] for d in L), 'max n', max(len(d['sets']) for d in L))
