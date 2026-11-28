"""Free census on stored W-models (samples only): Helly2 = 'the colour-row colour sets K(c) pairwise intersect' =>
'some colour lies in every K(c)'."""
import pickle, itertools
from alib import *
W=[Mod(s,F,src) for s,F,src in pickle.load(open('W.pkl','rb'))]
pw=0; pw_nouniv=0; nopw=0; ex=[]
for M in W:
    Ks=[set(M.K(c)) for c in M.cols]
    if all(a & b for a, b in itertools.combinations(Ks, 2)):
        pw+=1
        if not set.intersection(*Ks): pw_nouniv+=1; ex.append(M.src)
    else: nopw+=1
print(f'{len(W)} W-models: colour-row K pairwise intersecting in {pw} (no common colour in {pw_nouniv}); not pairwise in {nopw}', ex[:5])
