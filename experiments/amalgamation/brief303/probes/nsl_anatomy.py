"""Anatomy of every NSL counterexample found by plu_probe (free analysis of stored run output):
type of lambda(t) for the non-self leaf t (atom c0 / height-2 in Z / exit), and where PairLocalS's hypothesis fails."""
import json, glob
from alib import *
for f in sorted(glob.glob('../runs/r*/plu_*.json')):
    for d in json.load(open(f)):
        if d['mode']!='ns': continue
        M=Mod(d['sets'],d['F']); le=M.le
        for (c0,m,cm,cpm) in d['inst']:
            for t in Cp(M,m):
                if t==c0: continue
                n=M.lam(t)
                if not(le[c0][n] and not le[t][n]): continue
                typ='atom=c0' if n==c0 else ('Z-h2' if n in M.Zs else 'exit')
                bad=[c for c in Cp(M,m) if c!=c0 and not le[c0][M.lam(c)]]
                print(f.split('/')[-2], 'n',M.n,'c0',c0,'m',m,'|C|',cm,'t',t,'lam(t)',n,typ,'| PLS fails at',bad,'| lam(m)',M.lam(m),'self pj',[z for z in M.pjs if M.lam(z)==z])
