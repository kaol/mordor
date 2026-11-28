"""Shared read-only model library for the run-27 briefer's free analyses (no search).
Loads stored models (sets, F) via the repository's lattice class; computes phi, Z, colours, landings, pair-joins."""
import sys, json, glob, os
A='/home/user/mordor/experiments/amalgamation'; sys.path.insert(0,A); sys.path.insert(0,A+'/../separation')
import tight_probe as tp
from rstages import a_of
ss=tp.ss
class Mod:
    def __init__(s, sets, F, src=''):
        s.src=src; s.sets=sets; s.F=F
        L=s.L=ss.Lat(sets); n=s.n=L.n; le=s.le=L.le; h=s.h=L.rank; s.bot=bot=L.bot; s.top=top=L.top
        s.meet=[[max((z for z in range(n) if le[z][i] and le[z][j]), key=lambda z:h[z]) for j in range(n)] for i in range(n)]
        s.join=[[min((z for z in range(n) if le[i][z] and le[j][z]), key=lambda z:h[z]) for j in range(n)] for i in range(n)]
        s.phi=phi=F[bot]; s.Z=[y for y in range(n) if phi[y]==bot]; s.Zs=set(s.Z)
        s.cols=sorted({phi[w] for w in range(n) if h[phi[w]]==1 and phi[w] in s.Zs})
        s.atoms=[q for q in s.Z if h[q]==1]
        s.pjs=[z for z in s.Z if h[z]==2 and sum(le[c][z] for c in s.cols)>=2]
        s._d={}
    def desc(s,x):
        if x in s._d: return s._d[x]
        z=s.top; out=[]
        while z not in out: out.append(z); z=s.F[x][z]
        s._d[x]=out; return out
    def lidx(s,x): return next((i for i,v in enumerate(s.desc(x)) if s.h[v]<=2),None)
    def lam(s,x):
        i=s.lidx(x); return None if i is None else s.desc(x)[i]
    def C(s,z): return [c for c in s.cols if s.le[c][z]]
    def K(s,x):
        p=s.lam(x); return None if p is None else s.C(p)
    def fixed(s,q):
        p=s.lam(q); return p is not None and p not in s.Zs and s.phi[p]==q
    def nofix(s): return not any(s.fixed(q) for q in s.atoms)
    def unb(s): return not any(all(s.le[c][z] for c in s.cols) for z in s.Z)
    def w0(s):
        # W0 via the (T) form: a(bot)=bot, ZT, n1, h(top)>=3, Ta and Tb at every row of Z
        L=s.L; h=s.h; n=s.n; F=s.F; le=s.le
        if a_of(L,F,s.bot)!=s.bot or any(h[z]>2 for z in s.Z) or not any(h[z]==2 for z in s.Z) or h[s.top]<3: return False
        hi=[y for y in range(n) if h[y]>2]
        return all(not le[F[x][y]][x] and not le[y][F[x][y]] for x in s.Z for y in hi)
def load_all(patterns, base=A):
    seen=set(); out=[]
    for pat in patterns:
        for f in sorted(glob.glob(os.path.join(base,pat), recursive=True)):
            try: D=json.load(open(f))
            except Exception: continue
            for d in (D if isinstance(D,list) else [D]):
                if not isinstance(d,dict) or 'sets' not in d or 'F' not in d: continue
                key=json.dumps([d['sets'],d['F']])
                if key in seen: continue
                seen.add(key)
                try: out.append(Mod(d['sets'],d['F'],os.path.relpath(f,base)))
                except Exception as e: pass
    return out
def tb_at(M, x):
    hi=[y for y in range(M.n) if M.h[y]>2]
    return all(not M.le[M.F[x][y]][x] for y in hi)
def world_pairselfM(M):
    """PairSelf's world without D_p, as a predicate on a stored model: a(bot)=bot, ZT, n1, h(top)>=3, unbounded colours,
    non-thin, colour rows land with ColourGain and Tb, pair-join rows land, NoFix."""
    from rstages import a_of
    h=M.h; le=M.le
    if a_of(M.L,M.F,M.bot)!=M.bot or any(h[z]>2 for z in M.Z) or not any(h[z]==2 for z in M.Z) or h[M.top]<3: return False
    if not M.cols or not M.unb() or not M.pjs or not M.nofix(): return False
    for c in M.cols:
        p=M.lam(c)
        if p is None or not tb_at(M,c) or not any(le[g][p] and not le[g][c] for g in M.cols): return False
    return all(M.lam(m) is not None for m in M.pjs)
def world_pairself(M):
    return world_pairselfM(M) and all(not M.le[M.lam(m)][m] for m in M.pjs)
def staircase(M, x, y):
    """pairStair staircase of rows x, y (value row bot), as in ThinColour.colourStair: v = desc(x), w = desc(y),
    kappa(l) = first k with meet(v_l, w_k) low (l < i(x)); corner A_l = meet(v_l, w_kappa(l)), boundary B_l = meet(v_l, w_(kappa(l)-1)),
    boundary value e_l = phi(B_l).  Returns None if a row does not land."""
    ix=M.lidx(x); iy=M.lidx(y)
    if ix is None or iy is None: return None
    def u(r,j):
        z=M.top
        for _ in range(j): z=M.F[r][z]
        return z
    v=[u(x,j) for j in range(ix+1)]; w=[u(y,k) for k in range(iy+1)]
    D=lambda j,k: M.meet[v[j]][w[k]]
    kap=[next(k for k in range(iy+1) if M.h[D(l,k)]<=2) for l in range(ix)]
    steps=[(D(l,kap[l]), D(l,kap[l]-1), M.phi[D(l,kap[l]-1)], kap[l]) for l in range(ix)]
    return v,w,ix,iy,steps
def scl_walk(M, x, y):
    """Walk colourStair's invariant 'some colour of K(y) lies below e_l'. Returns ('nostart'|'ok'|'break', l, data)."""
    st=staircase(M,x,y)
    if st is None: return None
    v,w,ix,iy,steps=st; K=set(M.K(y)); le=M.le
    if not (set(M.C(steps[0][2]))&K): return ('nostart',0,None)
    for l in range(ix-1):
        e=steps[l][2]; A,B,en,_=steps[l+1]
        carried=[c for c in K if le[c][e]]
        if carried and not (set(M.C(en))&K): return ('break',l+1,dict(A=A,B=B,e=en,carried=carried))
    return ('ok',ix-1,None)
