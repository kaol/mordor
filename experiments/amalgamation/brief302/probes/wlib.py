"""Load the cached relaxed-world (pairselfM) models: every distinct stored model satisfying world_pairselfM."""
import pickle
from mlib import Mod
def relaxed():
    return [Mod(s,F,src) for (src,s,F) in pickle.load(open(__file__.replace('wlib.py','pairselfM_models.pkl'),'rb'))]
