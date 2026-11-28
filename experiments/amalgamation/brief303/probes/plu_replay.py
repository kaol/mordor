"""Free replay on the stored W corpus (PairSelf's world without D_p): PairLocal variants.
Instance: colour c0, m = lambda(c0) a pair-join with c0 <= m.
  PL   (refuted):  some other colour c1 <= m with c0 <= lambda(c1)        => lambda(m) = m ?
  PLU  :           every colour c <= m has c0 <= lambda(c)                 => lambda(m) = m ?
  PLS  :           every colour c in C'(m) has c0 <= lambda(c)             => lambda(m) = m ?
  NS   :           leaf: colour t <= m, t != c0, c0 <= lambda(t), t not <= lambda(t)  (count; and whether lambda(m) = m)"""
import pickle
from alib import *
W=[Mod(s,F,src) for s,F,src in pickle.load(open('W.pkl','rb'))]
st={k:[0,0] for k in ('PL','PLU','PLS','NS')}; viol={k:[] for k in st}
for M in W:
    le=M.le
    for c0 in M.cols:
        m=M.lam(c0)
        if m not in M.pjs or not le[c0][m]: continue
        others=[c for c in M.C(m) if c!=c0]; Cpm=[c for c in Cp(M,m) if c!=c0]
        selfl = M.lam(m)==m
        def rec(k,hyp):
            if hyp:
                st[k][0]+=1
                if not selfl: st[k][1]+=1; viol[k].append((M.src,c0,m,len(M.C(m))))
        rec('PL', any(le[c0][M.lam(c)] for c in others))
        rec('PLU', all(le[c0][M.lam(c)] for c in others))
        rec('PLS', all(le[c0][M.lam(c)] for c in Cpm))
        rec('NS', any(le[c0][M.lam(t)] and not le[t][M.lam(t)] for t in others))
for k in st: print(f'{k}: instances {st[k][0]}, lambda(m) != m in {st[k][1]}', viol[k][:4])
