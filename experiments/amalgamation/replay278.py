"""§34.3z²⁷⁸: replay of a stored model from the definitions (independent of every SAT encoding): world W0 + n1 via
rstages.stages, d, L2, OrbitDom, JoinCert, the BreakCert breakpoint, Cert1 and GoodAtom1.
  python3 replay278.py FILE.json"""
import json, sys, os
os.chdir('/home/user/mordor/experiments/amalgamation'); sys.path.insert(0, '.')
import tight_probe as tp; ss = tp.ss
from rstages import stages, a_of
FN = sys.argv[1]
M = json.load(open(os.path.abspath(FN) if os.path.isabs(FN) else os.path.join(os.path.dirname(os.path.abspath(__file__)), FN))); L = ss.Lat(M['sets']); F = M['F']; n = L.n; le = L.le; h = L.rank; bot = L.bot; top = L.top; mt = L.meet; jn = L.join
st = stages(L, F); inR = lambda x, i: st[x] is not None and st[x] <= i
R1 = [z for z in range(n) if inR(z, 1)]; R2 = [z for z in range(n) if inR(z, 2)]
Z = [x for x in range(n) if F[bot][x] == bot]
w0 = a_of(L, F, bot) == bot and all(h[z] <= 2 for z in R2) and top not in R2 and any(h[z] > 1 for z in R1)
def desc(x):
    v = top; s = []
    while v not in s: s.append(v); v = F[x][v]
    return s
def lam(x): return next((v for v in desc(x) if h[v] <= 2), None)
def good(y): return le[y][a_of(L, F, y)] or y in desc(y)
ex = {x: F[bot][lam(x)] for x in Z if x != bot and F[bot][lam(x)] != bot}
tb = desc(bot); d = [t for t in tb if t != bot][-1]
z = d if d in ex else (lam(d) if lam(d) in Z and lam(d) in ex else None)
L2 = z is not None
q = ex[z] if z is not None else None
orbitdom = L2 and any(ex.get(x2) == q and le[q][x2] for x2 in ex)
joincert = L2 and any(h[r] == 1 and le[r][z] and ex.get(jn[r][q]) == q for r in range(n))
cert1 = any(le[c][x] for x, c in ex.items())
atoms = [a for a in R1 if h[a] == 1]
print(sys.argv[1].split('/')[-1], '| n', n, 'H', L.height, '| W0+n1', w0, 'Z==R1', set(Z) == set(R1))
print('  d h', h[d], 'good', good(d), '| z', z, 'q', q, '| L2', L2, 'OrbitDom', orbitdom, 'JoinCert', joincert, 'Cert1', cert1)
print('  exits', ex, '| good atoms of R1', [a for a in atoms if good(a)], 'GoodAtom1', any(good(a) for a in atoms))
dd = desc(d)
if h[d] == 1 and not good(d):
    r = [y for y in dd if le[d][y]][-1]
    k = [k for k in range(len(tb) - 1) if mt[r][tb[k]] != d and mt[r][tb[k + 1]] == d][-1]; w = mt[r][tb[k]]; p = lam(w)
    print('  breakpoint w', w, 'h', h[w], '| lambda(w) in Z', p in Z, '| c(w)', F[bot][p], '<= w', le[F[bot][p]][w], '| BreakCert', p not in Z and le[F[bot][p]][w])
