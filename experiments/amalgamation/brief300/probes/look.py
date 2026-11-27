"""Describe stored models: colours, Z, landings, ColourGain per row, exits. Read-only analysis (no search)."""
import sys, json, os
A='/home/user/mordor/experiments/amalgamation'; sys.path.insert(0,A); sys.path.insert(0,A+'/../separation')
import tight_probe as tp
ss=tp.ss
def analyse(sets,F,verbose=True):
    L=ss.Lat(sets); n=L.n; le=L.le; h=L.rank; bot=L.bot; top=L.top
    phi=F[bot]; Z=[y for y in range(n) if phi[y]==bot]
    def desc(x):
        z=top; s=[]
        while z not in s: s.append(z); z=F[x][z]
        return s
    def lam(x): return next((z for z in desc(x) if h[z]<=2),None)
    def lidx(x): return next((i for i,z in enumerate(desc(x)) if h[z]<=2),None)
    cols=sorted({phi[w] for w in range(n) if h[phi[w]]==1 and phi[w] in Z})
    C=lambda z:[c for c in cols if le[c][z]]
    out=dict(n=n,H=h[top],cols=cols,Z=Z)
    rows=[]
    for x in Z:
        p=lam(x); i=lidx(x); d=desc(x); r=d[i-1] if i else None
        ex= p is not None and phi[p]!=bot
        cg=[c for c in cols if le[c][p] and not le[c][x]] if p is not None else None
        rows.append(dict(x=x,hx=h[x],Cx=C(x),lam=p,hl=h[p] if p is not None else None,Cl=C(p) if p is not None else None,
              exit=phi[p] if ex else None, r=r, phir=phi[r] if r is not None else None, Cphir=C(phi[r]) if r is not None else None, cg=cg, idx=i))
    out['rows']=rows
    return out,L
if __name__=='__main__':
    for fn in sys.argv[1:]:
        D=json.load(open(fn))
        if isinstance(D,dict): D=[D]
        for k,m in enumerate(D):
            o,L=analyse(m['sets'],m['F'])
            print(f'== {os.path.basename(fn)}[{k}] n={o["n"]} H={o["H"]} cols={o["cols"]} Z={o["Z"]}')
            for r in o['rows']:
                print('   x=%d h%d C%s -> lam=%s h%s C%s exit=%s | r=%s phi(r)=%s C%s | CG%s idx%s'%(r['x'],r['hx'],r['Cx'],r['lam'],r['hl'],r['Cl'],r['exit'],r['r'],r['phir'],r['Cphir'],r['cg'],r['idx']))
