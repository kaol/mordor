"""Free analysis of stored models: anatomy of SCL breaks for x a colour row, y in R* (colour or pair-join rows).
For each break at corner A (a pair-join): does row A self-land (lambda(A) <= A)?  Is lambda(y) in Z?  Also PC* failures:
y in R*, pair-join m with C(m) meeting K(y) but not inside it: does row m self-land?"""
import sys, json, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from look import analyse
from scl_check import staircase
tot=collections.Counter()
for fn in sys.argv[1:]:
    D=json.load(open(fn)); D=D if isinstance(D,list) else [D]; C=collections.Counter()
    for md in D:
        o,L=analyse(md['sets'],md['F']); F=md['F']; le=L.le; h=L.rank; cols=o['cols']; Z=o['Z']
        pjs=[z for z in Z if h[z]==2 and sum(le[c][z] for c in cols)>=2]
        rows={r['x']:r for r in o['rows']}; lam=lambda z: rows[z]['lam'] if z in rows else None
        Cs=lambda z:{c for c in cols if le[c][z]}
        selfl=lambda m: lam(m) is not None and le[lam(m)][m]
        anyself=any(selfl(m) for m in pjs)
        for x in cols:
            for y in cols+pjs:
                st=staircase(L,F,x,y)
                if st is None: continue
                v,w,ix,iy,kap,steps=st; K=Cs(w[iy])
                if not (Cs(steps[0][2])&K): continue
                for l in range(ix-1):
                    e=steps[l][2]; A,B,en=steps[l+1]
                    if Cs(e)&K and not (Cs(en)&K):
                        C['breaks']+=1; C['break corner self-lands']+=selfl(A); C['break: some pj self-lands']+=anyself
                        C['break: y colour']+=(y in cols); C['break: lam(y) in Z']+=(lam(y) in Z)
                        break
        for y in cols+pjs:
            K=Cs(lam(y))
            for m in pjs:
                if Cs(m)&K and not Cs(m)<=K:
                    C['PC* fail']+=1; C['PC* fail, m self-lands']+=selfl(m)
    print(os.path.basename(fn), dict(C)); tot.update(C)
print('TOTAL', dict(tot))
