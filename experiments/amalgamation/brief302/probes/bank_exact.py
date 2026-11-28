"""Bank (write to ../cex/) the smallest SAT model of every statement refuted by an exact run of plocal_probe.py,
re-checked from the definitions (world_pairselfM + the statement's failure), with room coordinates."""
import json, glob, os
from mlib import Mod, world_pairselfM
import bank_cex
from bank_cex import coords
ST={'esc':'EscapeLow: every model of W (PairSelf world without D_p) has a pair-join m with lambda(m) = m and a colour c <= m with lambda(c) <= m',
    'cx':'CrossExists: every model of W has colours a != b with a v b in Z, b <= lambda(a), a <= lambda(b)',
    'cp':'CrossPair (in W): colours a != b with a v b = m in Z, b <= lambda(a), a <= lambda(b) ==> lambda(m) = m',
    'caseB':'CaseBEmpty-in-W: no model of W has every colour row exiting',
    'bd':'BreakDichotomy (BD): in W, a colourStair break (colour rows x != y) at corner A forces lambda(A) <= A or lambda(u) = A for a colour u <= A',
    'escM':'ClosedColour-in-W (mutant column)', 'plocalM':'d2pM (mutant column)', 'cpM':'OneCross (mutant column)', 'caseAall':'CaseAallEmpty (mutant column)'}
found={}
for f in glob.glob('../runs/**/plocal_*.json', recursive=True)+glob.glob('../runs/**/bd_*.json', recursive=True):
    for d in json.load(open(f)):
        md=d['mode']
        if md not in ('esc','cx','cp','caseB','plocal','plne','bd'): continue
        M=Mod(d['sets'],d['F'],f); assert world_pairselfM(M), 'not in W'
        if md not in found or M.n<found[md][0].n: found[md]=(M,f,d)
for md,(M,f,d) in found.items():
    out=dict(statement=ST.get(md,md), world='W = PairSelf world without D_p (checked by world_pairselfM)', run_file=os.path.relpath(f,'..'),
             found='brief run 27, exact run of probes/plocal_probe.py mode '+md, coords=coords(M), sets=M.sets, F=M.F)
    json.dump(out, open('../cex/%s_min.json'%md,'w')); print('banked', md, coords(M), 'from', os.path.relpath(f,'..'))
