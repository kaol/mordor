"""Free census (no search) over every distinct stored W0 + n1 model under experiments/amalgamation (as jstuck296.py).
Per model: colours, unbounded?, thin? (no element of Z above two colours), pair-joins; and the SCL break count over
ordered pairs of landing rows (x, y) among colour rows and pair-join rows (R*), and among all rows of Z.
These models all have a fixed atom (CertAtom holds in W0 on every corpus), so this is context, not evidence."""
import sys, json, glob, os, collections
A='/home/user/mordor/experiments/amalgamation'; sys.path.insert(0,A); sys.path.insert(0,A+'/../separation')
os.chdir(A); import bank
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))) if False else None
from importlib.machinery import SourceFileLoader
scl = SourceFileLoader('scl', '/tmp/claude-0/-home-user/3b6fdd2c-c95c-5c07-b47c-6ae28c687a4c/scratchpad/amr_run25/brief/probes/scl_check.py').load_module()
seen=set(); models=[]
for f in glob.glob('**/*.json', recursive=True):
    try: D=json.load(open(f))
    except Exception: continue
    for d in (D if isinstance(D,list) else [D]):
        if not isinstance(d,dict) or 'sets' not in d or 'F' not in d: continue
        key=json.dumps([d['sets'],d['F']])
        if key in seen: continue
        seen.add(key)
        try: m=bank.M(d['sets'],d['F'])
        except Exception: continue
        if m.w0: models.append((f,m))
print('distinct W0 + n1 models', len(models))
C=collections.Counter(); ex=[]
for f,m in models:
    le=m.le; h=m.h; F=m.F; bot=m.bot
    cols=sorted({F[bot][w] for w in range(m.n) if h[F[bot][w]]==1 and F[bot][F[bot][w]]==bot})
    unb=not any(all(le[c][z] for c in cols) for z in m.Z)
    pjs=[z for z in m.Z if h[z]==2 and sum(le[c][z] for c in cols)>=2]
    thin=not pjs
    fixed=[q for q in m.atoms if m.fixed(q)]
    C['models']+=1; C['unbounded']+=unb; C[('unb', 'thin' if thin else 'nonthin', len(cols) if len(cols)<4 else '4+')]+=unb
    if unb and not thin and len(cols)>=3:
        L=m.L
        rows=[x for x in cols+pjs]
        br=0; pairs=0
        for x in rows:
            for y in rows:
                st=scl.staircase(L,F,x,y)
                if st is None: continue
                v,w,ix,iy,kap,steps=st; K={c for c in cols if le[c][w[iy]]}; pairs+=1
                if not ({c for c in cols if le[c][steps[0][2]]}&K): C['startfail']+=1; continue
                for l in range(ix-1):
                    e=steps[l][2]; en=steps[l+1][2]
                    if {c for c in cols if le[c][e]}&K and not ({c for c in cols if le[c][en]}&K): br+=1; break
        C['R*pairs']+=pairs; C['R*breaks']+=br; C['models_with_R*break']+=(br>0)
        fx_in_pj=any(any(le[q][p] for p in pjs) for q in fixed)
        C['fixed below a pair-join']+=fx_in_pj
        ex.append((os.path.basename(f), m.n, m.L.height, m.N, len(cols), len(pjs), fixed, br))
for k,v in C.items(): print(' ',k,v)
print('unbounded non-thin |A|>=3 models (file, n, H, N, |A|, |P|, fixed atoms, R* breaks):')
for e in ex[:40]: print('  ',e)
