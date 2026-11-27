"""Free analysis of stored W_col NoFix models (no D_p): which branch of the PairSelf proof skeleton they sit in.
Case A = some colour row lands in Z; universal colour = a colour below lambda(z) for every z in R*;
the self-landing pair-joins m (lambda(m) <= m) and whether C(m) lies below lambda(m)."""
import sys, json, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from look import analyse
C=collections.Counter()
for fn in sys.argv[1:]:
    D=json.load(open(fn)); D=D if isinstance(D,list) else [D]
    for md in D:
        o,L=analyse(md['sets'],md['F']); le=L.le; h=L.rank; cols=o['cols']; Z=o['Z']
        rows={r['x']:r for r in o['rows']}; lam=lambda z: rows[z]['lam']
        pjs=[z for z in Z if h[z]==2 and sum(le[c][z] for c in cols)>=2]
        R=cols+pjs
        caseA=any(lam(a) in Z for a in cols)
        univ=[c for c in cols if all(lam(z) is not None and le[c][lam(z)] for z in R)]
        selfl=[m for m in pjs if le[lam(m)][m]]
        C['models']+=1; C['caseA']+=caseA; C['universal colour exists']+=bool(univ)
        C['some pj self-lands']+=bool(selfl)
        ea=[rows[a]['phir'] for a in cols if lam(a) in Z]
        C['caseA: e(a) single colour']+=any(sum(le[c][e] for c in cols)==1 for e in ea)
        C['caseA: e(a) pair-join']+=any(sum(le[c][e] for c in cols)>=2 for e in ea)
print(dict(C))
# D2 anatomy: for a universal colour c0, follow lambda from c0 through the pair-joins above c0
D2=collections.Counter()
for fn in sys.argv[1:]:
    D=json.load(open(fn)); D=D if isinstance(D,list) else [D]
    for md in D:
        o,L=analyse(md['sets'],md['F']); le=L.le; h=L.rank; cols=o['cols']; Z=o['Z']
        rows={r['x']:r for r in o['rows']}; lam=lambda z: rows[z]['lam'] if z in rows else None
        pjs=[z for z in Z if h[z]==2 and sum(le[c][z] for c in cols)>=2]; R=cols+pjs
        univ=[c for c in cols if all(lam(z) is not None and le[c][lam(z)] for z in R)]
        for c0 in univ[:1]:
            m=lam(c0); path=[c0]
            while m is not None and m not in path:
                path.append(m)
                if m in Z and h[m]==2 and le[lam(m)][m]: break
                m=lam(m)
            kind='lam(c0) exits' if lam(c0) not in Z else ('lam(c0) pair-join' if lam(c0) in pjs else 'lam(c0) in Z, not pj')
            D2[kind]+=1
            D2[('steps to a self-landing height-2 Z element', len(path)-1, 'pj' if path[-1] in pjs else 'nonpj')]+=1
print(dict(D2))
