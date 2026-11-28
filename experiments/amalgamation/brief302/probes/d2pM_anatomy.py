"""Free analysis (no search) of the stored d2pM mutant models (lambda(c0) = m a pair-join, lambda(m) != m, c0 not
required universal). For each such c0: which rows z of R* = colours + pair-joins have c0 not below lambda(z)."""
import collections
from mlib import load_all
ms=load_all(['holding/cgall_d2pM_*.json'])
print('d2pM models', len(ms))
C=collections.Counter()
for M in ms:
    le=M.le; R=M.cols+M.pjs
    for c0 in M.cols:
        m=M.lam(c0)
        if m not in M.pjs or M.lam(m)==m: continue
        others=[c for c in M.C(m) if c!=c0]
        bad=[z for z in R if not le[c0][M.lam(z)]]
        kinds=tuple(sorted(set(('other colour of m' if z in others else ('colour' if z in M.cols else ('pj m' if z==m else ('pj containing c0' if le[c0][z] else 'pj not containing c0')))) for z in bad)))
        C[kinds]+=1
        lm=M.lam(m)
        C[('lam(m) in Z' if lm in M.Zs else 'lam(m) exits', 'c0<=lam(m)' if le[c0][lm] else 'c0 not<=lam(m)')]+=1
        for c1 in others:
            l1=M.lam(c1)
            C[('lam(c\') in Z' if l1 in M.Zs else 'lam(c\') exits, colour %s'%('c0' if M.phi[l1]==c0 else 'other'), 'c0<=lam(c\')' if le[c0][l1] else 'c0 not<=')]+=1
for k,v in sorted(C.items(), key=lambda t:-t[1]): print(' ',v,k)
