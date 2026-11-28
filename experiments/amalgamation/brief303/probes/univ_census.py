"""Free census on stored W-models (samples only): colours universal over the colour rows (c0 <= lambda(c) for every
colour c), over R* (colour rows and pair-join rows), and the escape of each PLS instance."""
import pickle
from alib import *
W=[Mod(s,F,src) for s,F,src in pickle.load(open('W.pkl','rb'))]
n_uc=n_ur=n_none=0; inZ=0; exitc=0
for M in W:
    le=M.le
    uc=[c0 for c0 in M.cols if all(le[c0][M.lam(c)] for c in M.cols)]
    ur=[c0 for c0 in uc if all(le[c0][M.lam(m)] for m in M.pjs)]
    n_uc+=bool(uc); n_ur+=bool(ur); n_none+= not uc
    for c0 in uc:
        p=M.lam(c0)
        if p in M.Zs: inZ+=1
        else: exitc+=1
print(f'{len(W)} W-models: universal over colour rows in {n_uc}, over R* in {n_ur}, none in {n_none}; universal colours landing in Z {inZ}, exiting {exitc}')
