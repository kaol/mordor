"""Free analysis (no search): local form of D2' on stored models of the relaxed worlds (pairselfM, d2pM, colrows+TbA)
and on stored W0 models.  Instance: colour c0 with lambda(c0) = m a pair-join (m in Z, two colours below m) and c0 <= m.
PairLocal claim: lambda(m) != m  ==>  some colour c' <= m, c' != c0, has c0 not <= lambda(c').
Also records the type of lambda(c') for c' with c0 <= lambda(c') (case split of §301)."""
import collections, sys
from mlib import load_all
pats=sys.argv[1:] or ['holding/cgall_d2pM_*.json','holding/cgall_pairselfM_*.json','holding/cgall_colrows_*TbA.json']
ms=load_all(pats)
print('models', len(ms), 'patterns', pats)
C=collections.Counter(); ex=[]
for M in ms:
    le=M.le
    if not M.nofix(): C['has fixed atom (skipped for claim)']+=1
    for c0 in M.cols:
        m=M.lam(c0)
        if m not in M.pjs or not le[c0][m]: continue
        lm=M.lam(m)
        others=[c for c in M.C(m) if c!=c0]
        good=[c for c in others if M.lam(c) is not None and le[c0][M.lam(c)]]
        bad=[c for c in others if c not in good]
        C[('inst', 'lam(m)=m' if lm==m else 'lam(m)!=m', 'all others have c0<=lam' if not bad else 'some other has c0 not<=lam', 'nofix' if M.nofix() else 'fix')]+=1
        if lm!=m and not bad and M.nofix(): ex.append((M.src,c0,m))
        for c in good:
            l1=M.lam(c)
            C[('c0<=lam(c\')', 'in Z' if l1 in M.Zs else ('exit to c0' if M.phi[l1]==c0 else 'exit other'), 'lam(c\')=m' if l1==m else '', 'lam(m)=m' if lm==m else 'lam(m)!=m')]+=1
for k,v in sorted(C.items(), key=lambda t:str(t[0])): print(' ',v,k)
print('PairLocal counterexamples (NoFix):', ex[:10])
