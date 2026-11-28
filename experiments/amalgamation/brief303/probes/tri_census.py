"""Free census (samples only): NoTriangle on stored W-models -- no three colour rows whose landing colour sets pairwise
intersect with no common colour."""
import pickle, itertools
from alib import *
W=[Mod(s,F,src) for s,F,src in pickle.load(open('W.pkl','rb'))]
bad=0; inst=0
for M in W:
    K={c:set(M.K(c)) for c in M.cols}
    for T in itertools.combinations(M.cols,3):
        if all(K[a]&K[b] for a,b in itertools.combinations(T,2)):
            inst+=1
            if not (K[T[0]]&K[T[1]]&K[T[2]]): bad+=1
print(f'{len(W)} W-models: pairwise-meeting colour-row triples {inst}, triangles (no common colour) {bad}')
