"""Free analysis of stored NoFix models: is Z colour-thin (no z in Z above two colours)? pair-joins in Z, colour graph."""
import sys, json, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from look import analyse
for fn in sys.argv[1:]:
    D=json.load(open(fn)); D=D if isinstance(D,list) else [D]
    stats=[]
    for m in D:
        o,L=analyse(m['sets'],m['F']); le=L.le; cols=o['cols']; Z=o['Z']
        pj=[(a,b) for a,b in itertools.combinations(cols,2) if any(le[a][z] and le[b][z] for z in Z)]
        stats.append((len(cols),len(pj),o['n'],o['H']))
    thin=sum(1 for s in stats if s[1]==0)
    print(os.path.basename(fn), 'models',len(stats),'colour-thin',thin, 'cols/pairjoins/n/H', stats[:12])
