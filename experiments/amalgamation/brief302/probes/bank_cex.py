"""Write the counterexamples found by free analysis of stored models (no search) to ../cex/, with the statement each
refutes and its room coordinates.  Every model is re-checked here from the definitions (world_pairselfM predicate)."""
import json
from wlib import relaxed
from mlib import scl_walk, world_pairselfM
def width(M):
    # largest antichain, brute force over elements by greedy-free exact search (small n)
    import itertools
    n=M.n; le=M.le; best=1
    els=list(range(n))
    def ext(ch, cand):
        nonlocal best
        best=max(best,len(ch))
        for i,c in enumerate(cand):
            if all(not le[c][d] and not le[d][c] for d in ch): ext(ch+[c], cand[i+1:])
    ext([], els); return best
def coords(M):
    tb=M.desc(M.bot); nz=[t for t in tb if t!=M.bot]; d=nz[-1] if nz else None
    return dict(n=M.n, H=M.h[M.top], width=width(M), N=tb.index(d) if d is not None else None,
                d_height=M.h[d] if d is not None else None, colours=M.cols, pairjoins=M.pjs)
R=relaxed()
# 1. BreakCornerSelf (brief300 §3 D1 test form): a staircase break at a pair-join corner A forces lambda(A) <= A
bcs=[]
for M in R:
    for x in M.cols:
        for y in M.cols+M.pjs:
            r=scl_walk(M,x,y)
            if r and r[0]=='break':
                A=r[2]['A']
                if not M.le[M.lam(A)][A]: bcs.append((M.n,M,x,y,r))
bcs.sort(key=lambda t:t[0]); _,M,x,y,r=bcs[0]; assert world_pairselfM(M)
json.dump(dict(statement='BreakCornerSelf (brief300 §3, D1 located test form): in PairSelf world without D_p, if the value-bot staircase of rows x (colour) and y (colour or pair-join) breaks at a corner A (A in Z, carried colour of K(y) below A, boundary value a colour outside K(y)), then lambda(A) <= A',
               refuted_by=dict(x=x,y=y,corner=r[2]['A'],B=r[2]['B'],e=r[2]['e'],carried=r[2]['carried'],lam_A=M.lam(r[2]['A'])),
               world='pairselfM (PairSelf without D_p): checked by world_pairselfM', source=M.src, found='brief run 27, free replay of stored models (probes/breaks.py)',
               coords=coords(M), instances_failing=len(bcs), sets=M.sets, F=M.F), open('../cex/breakCornerSelf_min.json','w'))
print('BreakCornerSelf counterexamples (break, lambda(A) not <= A):', len(bcs), 'smallest', coords(M), (x,y,r))
# 2. ClosedColour-in-W: every pairselfM model has a colour c <= lambda(c) = m in Z with c <= lambda(m)
cc=[]
for M in R:
    le=M.le
    if not [c for c in M.cols if le[c][M.lam(c)] and M.lam(c) in M.Zs and le[c][M.lam(M.lam(c))]]: cc.append(M)
cc.sort(key=lambda M:M.n)
for k,M in enumerate(cc):
    assert world_pairselfM(M)
    sw=[(a,b) for a in M.cols for b in M.cols if a<b and M.lam(a)==b and M.lam(b)==a]
    json.dump(dict(statement='ClosedColour-in-W: every model of the PairSelf world without D_p has a colour c with c <= lambda(c) = m in Z and c <= lambda(m) (then lambda(m) = m by selfLand)',
                   escape='no closed colour; colour swap pairs (lambda(a)=b, lambda(b)=a): %s; self-landing pair-joins: %s'%(sw,[m for m in M.pjs if M.lam(m)==m]),
                   world='pairselfM, checked by world_pairselfM', source=M.src, found='brief run 27, free analysis (probes/closed.py)',
                   coords=coords(M), sets=M.sets, F=M.F), open('../cex/closedColourW_%d.json'%k,'w'))
    print('ClosedColour-in-W counterexample', k, coords(M), 'swaps', sw)
