"""Run-28 briefer: analysis helpers over stored models (read-only; uses brief302/probes/mlib.Mod for lattice data)."""
import sys, pickle
sys.path.insert(0,'/home/user/mordor/experiments/amalgamation/brief302/probes')
from mlib import Mod, tb_at, world_pairselfM, world_pairself
def load(path='corpus.pkl'):
    out=[]
    for sets,F,src in pickle.load(open(path,'rb')):
        try: out.append(Mod(sets,F,src))
        except Exception: pass
    return out
def hi(M): return [y for y in range(M.n) if M.h[y]>2]
def zt(M): return all(M.phi[B]!=M.bot for B in hi(M))
def Cp(M,p):
    """C'(p): atoms below p that are values phi(X) at a high column X."""
    return sorted({M.phi[X] for X in hi(M) if M.h[M.phi[X]]==1 and M.le[M.phi[X]][p]})
def a_bot(M):
    from rstages import a_of
    return a_of(M.L,M.F,M.bot)==M.bot
