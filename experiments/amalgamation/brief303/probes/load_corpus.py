"""Run-28 briefer: load every stored model (sets, F) under experiments/amalgamation (bank, holding, brief*, direct*),
dedupe, and pickle the list of (sets, F, src) for the free analyses.  Read-only on the repository."""
import sys, json, glob, os, pickle
A='/home/user/mordor/experiments/amalgamation'
seen=set(); out=[]
for f in sorted(glob.glob(A+'/**/*.json', recursive=True)):
    try: D=json.load(open(f))
    except Exception: continue
    items = D if isinstance(D,list) else [D]
    if isinstance(D,dict) and 'models' in D and isinstance(D['models'],list): items=D['models']
    for d in items:
        if not isinstance(d,dict) or 'sets' not in d or 'F' not in d: continue
        key=json.dumps([d['sets'],d['F']])
        if key in seen: continue
        seen.add(key); out.append((d['sets'],d['F'],os.path.relpath(f,A)))
print(len(out),'distinct stored models')
pickle.dump(out,open(sys.argv[1],'wb'))
