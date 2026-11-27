"""Save the stored W0-flat & NoFix models that refute LfpLand / LfpMinAll (exact models; found by free replay feat8.py)."""
import sys, json; sys.path.insert(0, '.'); from world import *
import bank
ms = [(n, w) for n, w in dedup(load_all()) if w.w0flat() and w.nofix()]
for name, w in ms:
    le = w.le; Zs = set(w.Z)
    Y = set(v for x in w.Z for v in w.desc(x)[:w.lidx(x)]); Ym = [y for y in Y if not any(z != y and le[z][y] for z in Y)]
    fails = []
    if not all(w.b(y) in Zs for y in Ym): fails.append('LfpMinAll (W0-flat, NoFix: every minimal descent column y has b(y) in Z)')
    if not any(w.b(y) in Zs and y in w.desc(w.b(y)) for y in Ym): fails.append('LfpLand (W0-flat, NoFix: some minimal descent column y has b(y) in Z and y on row b(y)\'s descent)')
    if not fails: continue
    d, N = w.dN(); br = 'a' if w.h[d] == 2 else 'atom'
    rec = dict(sets=w.sets, F=w.F, source=name, refutes=fails, world='W0-flat & NoFix (Tb dropped at height-2 rows)',
               coords=dict(n=w.n, H=w.L.height, width=bank.width(w.L), N=N, branch=br, M2=len(w.M2), Ymin=Ym,
                           b_of_Ymin={y: w.b(y) for y in Ym}, witness=w.witnesses()))
    fn = 'cex/' + name.replace('/', '_').replace('#', '_') + '.json'; json.dump(rec, open(fn, 'w')); print(fn, fails, rec['coords'])
