"""Census of the relaxed world W (= PairSelf's world without D_p, brief302 mlib.world_pairselfM) in the stored corpus:
|A|, number of pair-joins, max |C(m)|, and the landing types of colours."""
from alib import *
from collections import Counter
Ms=load(); W=[M for M in Ms if world_pairselfM(M)]
print(len(W),'W-models')
cA=Counter(); cC=Counter(); cpj=Counter(); srcs=Counter()
for M in W:
    cA[len(M.cols)]+=1; cpj[len(M.pjs)]+=1
    cC[max(len(M.C(m)) for m in M.pjs)]+=1; srcs[M.src.split('/')[0]]+=1
print('|A|',sorted(cA.items())); print('#pj',sorted(cpj.items())); print('max|C(m)|',sorted(cC.items())); print(srcs)
import pickle; pickle.dump([(M.sets,M.F,M.src) for M in W],open('W.pkl','wb'))
