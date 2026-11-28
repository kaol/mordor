"""Free analysis (no search): ClosedColour on the stored relaxed-world models (pairselfM predicate, D_p dropped).
ClosedColour(c): c <= lambda(c) = m in Z and c <= lambda(m)   (by SelfLand then lambda(m) = m).
Also: universal colour over colour rows (UCc) and over R* (UC*), and whether the closed colour is universal."""
import collections
from wlib import relaxed
C=collections.Counter(); miss=[]
for M in relaxed():
    le=M.le; R=M.cols+M.pjs
    closed=[c for c in M.cols if le[c][M.lam(c)] and M.lam(c) in M.Zs and le[c][M.lam(M.lam(c))]]
    ucc=[c for c in M.cols if all(le[c][M.lam(z)] for z in M.cols)]
    ucs=[c for c in M.cols if all(le[c][M.lam(z)] for z in R)]
    C[('closed' if closed else 'NO closed', 'UCc' if ucc else 'no UCc', 'UC*' if ucs else 'no UC*')]+=1
    if not closed: miss.append(M.src)
    # sanity: SelfLand consequence lambda(m) = m for every closed colour
    for c in closed: assert M.lam(M.lam(c))==M.lam(c)
for k,v in sorted(C.items(), key=lambda t:-t[1]): print(' ',v,k)
print('models without a closed colour:', len(miss), miss[:10])
