"""Free replay on the Case B models of W produced by run 3 (every colour row exits): for every ordered pair of colour
rows, the colourStair walk; BD-B claims every break corner A has lambda(A) <= A.  Also records whether every two colour
rows' landings share a colour (the hypothesis `hint` of certAtom_of_caseB) and which pairs fail it."""
import json, glob, collections
from mlib import Mod, world_pairselfM, scl_walk
C=collections.Counter()
for f in sorted(glob.glob('../runs/r3/plocal_caseB*.json')):
    for d in json.load(open(f)):
        if d['mode']!='caseB': continue
        M=Mod(d['sets'],d['F'],f); assert world_pairselfM(M) and all(M.lam(c) not in M.Zs for c in M.cols)
        C['caseB models']+=1
        for x in M.cols:
            for y in M.cols:
                if x==y: continue
                r=scl_walk(M,x,y)
                C[('walk',r[0])]+=1
                if r[0]=='break':
                    A=r[2]['A']; C[('break corner', 'lam(A)<=A' if M.le[M.lam(A)][A] else 'lam(A) not<=A (BD-B FAILS)')]+=1
                disj = not (set(M.K(x))&set(M.K(y)))
                C[('K(x) & K(y)', 'disjoint' if disj else 'meet')]+=1
for k,v in sorted(C.items(), key=lambda t:str(t[0])): print(' ',v,k)
