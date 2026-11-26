"""Run 1 (diagnostic, NOT a search): structure of the STORED models (fixed L and F) from the definitions.
No quantifier over F; nothing here is evidence for a candidate. Prints, per stored model: Z, maximal elements,
height-2 elements M2, landings, exits, mu, good atoms, which M2 elements lie above each good atom, TopCell per m,
and the DL cell test for undominated exits.  python3 diag.py FILE..."""
import sys, json
sys.path.insert(0, '/home/user/mordor/experiments/separation'); sys.path.insert(0, '/home/user/mordor/experiments/amalgamation')
import separator_stages as ss
from rstages import stages, a_of
def run(L, F, tag):
    n = L.n; le = L.le; h = L.rank; bot = L.bot; top = L.top; mt = L.meet; jn = L.join
    st = stages(L, F); inR = lambda z, i: st[z] is not None and st[z] <= i
    w0 = a_of(L, F, bot) == bot and all(h[z] <= 2 for z in range(n) if inR(z, 2)) and not inR(top, 2) and any(h[z] > 1 for z in range(n) if inR(z, 1))
    Z = [x for x in range(n) if F[bot][x] == bot]; Zs = [x for x in Z if x != bot]
    def desc(x):
        v = top; s = []
        while v not in s: s.append(v); v = F[x][v]
        return s
    lam = lambda x: next(v for v in desc(x) if h[v] <= 2)
    li = lambda x: next(j for j, v in enumerate(desc(x)) if h[v] <= 2)
    ex = lambda x: F[bot][lam(x)] != bot
    c = lambda x: F[bot][lam(x)]
    mu = lambda x: c(x) if ex(x) else lam(x)
    good = lambda q: q in desc(q) or le[q][a_of(L, F, q)]
    DL = lambda r, p: all(le[y][p] for y in range(n) if le[y][F[r][jn[p][y]]])
    tb = desc(bot); d = [t for t in tb if t != bot][-1]
    maxZ = [x for x in Zs if not any(y != x and le[x][y] for y in Z)]
    M2 = [x for x in Zs if h[x] == 2]; atoms = [x for x in Zs if h[x] == 1]
    print(f'== {tag}: n={n} H={L.height} W0+n1={w0} |Z|={len(Z)} atoms={len(atoms)} M2={len(M2)} maxZ={maxZ} d={d} h(d)={h[d]}')
    print('   bot-descent heights', [h[t] for t in tb])
    for x in Zs:
        p = lam(x)
        s = f'   x={x:2d} h{h[x]} max={x in maxZ} li={li(x)} lam={p}(h{h[p]},{"Z" if p in Z else "exit"})'
        if ex(x): s += f' c={c(x)} dom={le[c(x)][x]} DL(c,lam)={DL(c(x), p)} cell c<=F(c,lam)={le[c(x)][F[c(x)][p]]}'
        if h[x] == 1: s += f' | GOOD={good(x)} fixed={mu(x) == x} a={a_of(L, F, x)}(h{h[a_of(L,F,x)]}) above_in_M2={[m for m in M2 if le[x][m]]}'
        if h[x] == 2:
            q = mt[x][p]; s += f' | meet(x,lam)={q}(h{h[q]}) TopCell={h[q] == 1 and h[p] == 2 and le[q][F[q][p]]}'
        print(s)
    G = [q for q in atoms if good(q)]
    print('   good atoms', G, '| non-maximal good', [q for q in G if any(le[q][m] for m in M2)], '| mu-fixed', [q for q in atoms if mu(q) == q])
    print('   mu-orbit of bot', end=' ')
    x = bot; seen = []
    while x not in seen: seen.append(x); x = mu(x) if x != bot else d
    print(seen, '->', x)
for fn in sys.argv[1:]:
    M = json.load(open(fn)); Ms = M if isinstance(M, list) else [M]
    for i, m in enumerate(Ms): run(ss.Lat(m['sets']), m['F'], f'{fn.split("/")[-1]}[{i}]')
