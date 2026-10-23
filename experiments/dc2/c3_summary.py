"""Summarize all c3_results*.jsonl in this directory: per pattern, closure width w and per-k verdicts
(u = UNSAT by lazy check, um = UNSAT by master alone, S = SAT, needs attention)."""
import json, glob, collections, os, sys
import c3
n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
here = os.path.dirname(os.path.abspath(__file__))
by = collections.defaultdict(dict)
for f in glob.glob(os.path.join(here, 'c3_results*.jsonl')):
    for l in open(f):
        r = json.loads(l)
        if r['k'] == 'closure' and r.get('w') is not None: by[r['tag']]['closure'] = r
        else: by[r['tag']].setdefault(r['k'], r)
pats = list(c3.all_patterns(n)); reps, seen = [], set()
for p in pats:
    t = c3.tag(p, n)
    if t in seen: continue
    seen.add(t); seen.add(c3.tag(c3.swap_pat(p), n)); reps.append(t)
ncomp = 0
for t in reps:
    ks = by.get(t, {})
    if 'closure' not in ks: print(f"{t} not started"); continue
    w = ks['closure'].get('w')
    kk = sorted(k for k in ks if k != 'closure')
    res = ' '.join({'UNSAT': 'u', 'SAT': 'S'}[ks[k]['res']] + ('m' if ks[k].get('how') == 'master' else '') for k in kk)
    full = w is not None and kk == list(range(2 * w + 1)) and all(ks[k]['res'] == 'UNSAT' for k in kk)
    ncomp += full
    flag = 'COMPLETE' if full else ('NO-CLOSURE' if w is None else ('HAS-SAT' if any(ks[k]['res'] == 'SAT' for k in kk) else 'running'))
    print(f"{t} w={w} {flag:9s} k: {res}")
print(f"{ncomp}/{len(reps)} patterns complete")
