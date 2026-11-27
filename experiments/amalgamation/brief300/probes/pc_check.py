"""Free check on stored models: PC (pair-closure of landings) for colour rows and pair-join rows:
 for every landing row y in R* (colours, pair-joins) and every pair-join m: C(m) meets K(y) => C(m) inside K(y).
Also: does some pair-join row self-land (lambda(m) <= m)?  Does some pair-join row fail ColourGain?"""
import sys, json, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from look import analyse
for fn in sys.argv[1:]:
    D=json.load(open(fn)); D=D if isinstance(D,list) else [D]; C=collections.Counter()
    for m in D:
        o,L=analyse(m['sets'],m['F']); le=L.le; h=L.rank; cols=o['cols']; Z=o['Z']
        pjs=[z for z in Z if h[z]==2 and sum(le[c][z] for c in cols)>=2]
        rows={r['x']:r for r in o['rows']}
        Cs=lambda z:{c for c in cols if le[c][z]}
        pcf=0; pcf_col=0
        for y in cols+pjs:
            p=rows[y]['lam']
            if p is None: continue
            K=Cs(p)
            for mm in pjs:
                if Cs(mm)&K and not Cs(mm)<=K: pcf+=1; pcf_col+= (y in cols)
        self=[mm for mm in pjs if rows[mm]['lam'] is not None and le[rows[mm]['lam']][mm]]
        cgf=[mm for mm in pjs if not rows[mm]['cg']]
        C['models']+=1; C['PC fails (some y)']+=(pcf>0); C['PC fails at a colour row']+=(pcf_col>0); C['pair-join self-lands']+=bool(self); C['pair-join CG fails']+=bool(cgf)
    print(os.path.basename(fn), dict(C))
