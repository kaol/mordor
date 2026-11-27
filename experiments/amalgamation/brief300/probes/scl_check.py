"""Free replay (no search) of the paper lemma SCL (colour-set staircase) on stored models.
For every ordered pair (x, y) of rows that land, walk the pairStair staircase of rows x, y with value row bot:
  corners A_l = v_l /\ w_{kappa(l)} (low), boundary values e_l = phi(v_l /\ w_{kappa(l)-1}).
Invariant: some colour of K = C(lambda(y)) lies below e_l.
Paper claim (needs only ZT, a(bot) = bot, landing of x and y, and C(e(y)) meeting K):
  the invariant can break only at a corner A in Z of height 2 with C(A) meeting K, C(A) not inside K, e = a colour outside K.
Prints, per model: pairs checked, pairs whose start fails, breaks of the claimed kind, violations of the claim (must be 0)."""
import sys, json, os, itertools
A='/home/user/mordor/experiments/amalgamation'; sys.path.insert(0,A); sys.path.insert(0,A+'/../separation')
import tight_probe as tp
from rstages import a_of
ss=tp.ss
def staircase(L,F,x,y):
    n=L.n; le=L.le; h=L.rank; top=L.top; meet=L.meet
    def desc(r):
        z=top; s=[top]
        for _ in range(4*n): 
            z=F[r][z]; s.append(z)
        return s
    v=desc(x); w=desc(y)
    ix=next((i for i,z in enumerate(v) if h[z]<=2),None); iy=next((i for i,z in enumerate(w) if h[z]<=2),None)
    if ix is None or iy is None: return None
    D=lambda j,k: meet[v[j]][w[k]]
    kap=[next(k for k in range(iy+1) if h[D(l,k)]<=2) for l in range(ix)]
    steps=[]
    for l in range(ix):
        B=D(l,kap[l]-1); Acorner=D(l,kap[l]); e=F[L.bot][B]
        steps.append((Acorner,B,e))
    return v,w,ix,iy,kap,steps
def run(sets,F):
    L=ss.Lat(sets); n=L.n; le=L.le; h=L.rank; bot=L.bot
    if not hasattr(L,'meet'):
        L.meet=[[max((z for z in range(n) if le[z][i] and le[z][j]), key=lambda z:h[z]) for j in range(n)] for i in range(n)]
    phi=F[bot]; Z=set(y for y in range(n) if phi[y]==bot)
    if a_of(L,F,bot)!=bot or any(h[z]>2 for z in Z): return None
    cols=sorted({phi[w] for w in range(n) if h[phi[w]]==1 and phi[w] in Z}); C=lambda z:{c for c in cols if le[c][z]}
    res=dict(pairs=0,startfail=0,breaks=0,viol=0,concl_fail_nobreak=0)
    for x in range(n):
        for y in range(n):
            st=staircase(L,F,x,y)
            if st is None: continue
            v,w,ix,iy,kap,steps=st
            K=C(w[iy]); res['pairs']+=1
            e0=steps[0][2]
            if not (C(e0)&K): res['startfail']+=1; continue
            broke=False
            for l in range(ix-1):
                e=steps[l][2]; Anext,Bn,en=steps[l+1]
                # e_l <= A_{l+1} check (paper)
                assert le[e][Anext], 'e_l not below next corner'
                assert le[phi[Anext]][en] and le[en][Anext]
                if C(e)&K and not (C(en)&K):
                    if Anext in Z and h[Anext]==2 and (C(Anext)&K) and (C(Anext)-K) and h[en]==1 and en in (C(Anext)-K): res['breaks']+=1
                    else: res['viol']+=1
                    broke=True; break
            if not broke:
                ex=phi[v[ix-1]]
                if not (C(ex)&K): res['concl_fail_nobreak']+=1
    return res
if __name__=='__main__':
    tot={}
    for fn in sys.argv[1:]:
        D=json.load(open(fn)); D=D if isinstance(D,list) else [D]
        for k,m in enumerate(D):
            if 'sets' not in m: continue
            r=run(m['sets'],m['F'])
            if r is None: continue
            for kk,vv in r.items(): tot[kk]=tot.get(kk,0)+vv
        print(os.path.basename(fn), tot, flush=True)
    print('TOTAL', tot)
