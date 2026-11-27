"""Save, as JSON in cex/, copies of the stored W0 models that refute this brief's free-refuted routes (the sources stay
where they are in the repository; nothing there is touched).  Each entry: sets, F, source, refutes, coordinates
(|L|, H, width, N, branch, |calA|).  Statements (all universal over W0 + n1 models; FAIL recomputed here):
  AbsorbExists : some x in Z has every calA-atom below lambda(x) below x.
  TopLand_X    : the iteration of G_X = join_{z in Z, z <= X} F(z, .) from top gets low, X = join of calA.
  TopLand_S    : the iteration of g_S = join_{z in S} F(z, .) gets low, S = {bot} u calA u {q v q' in Z}.
  ClosureLand  : the closure iteration of closure_census.py ends CLOSED (never STUCK).
  Restrict     : for s = t_j high (1 <= j < N), the restriction F ^ s on down(s) lies in W0."""
import sys, os, json, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from world import load_all, dedup
from closure_census import first_low, closure
from restrict_census import restrict
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation'); from bank import width
import functools
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cex'); os.makedirs(OUT, exist_ok=True)
R = collections.defaultdict(list)
for name, w in dedup(load_all()):
    try:
        if not (w.base() and w.w0flat() and w.w0()): continue
    except Exception: continue
    d, N = w.dN(); br = 'a' if w.h[d] == 2 else 'atom'; phi = w.F[w.bot]; L = w.L
    calA = sorted({phi[y] for y in range(w.n) if phi[y] != w.bot and w.h[phi[y]] == 1 and phi[phi[y]] == w.bot})
    X = functools.reduce(lambda a, b: L.join[a][b], calA, w.bot)
    coords = dict(n=w.n, H=w.h[w.top], width=width(L), N=N, branch=br, calA=len(calA))
    rec = lambda st: R[st].append(dict(sets=w.sets, F=w.F, source=name, refutes=st, **coords))
    if not any(all(w.le[q][x] for q in calA if w.le[q][w.lam(x)]) for x in w.Z if x != w.bot): rec('AbsorbExists')
    if first_low(w, [z for z in w.Z if w.le[z][X]]) is None: rec('TopLand_X')
    S = {w.bot} | set(calA) | {L.join[a][b] for a in calA for b in calA if a != b and L.join[a][b] in w.Z}
    if first_low(w, sorted(S)) is None: rec('TopLand_S')
    if closure(w)[0] == 'STUCK': rec('ClosureLand')
    tb = w.tdesc()
    for j in range(1, N):
        s = tb[j]
        if w.h[s] < 3: continue
        w2, keep = restrict(w, s)
        if not (w2.mono and w2.base() and w2.w0flat() and w2.w0()): rec('Restrict'); break
for st, L_ in R.items():
    L_.sort(key=lambda e: e['n'])
    json.dump(L_, open(os.path.join(OUT, st + '.json'), 'w'))
    e = L_[0]
    print(f"{st}: {len(L_)} refuting stored W0 models; smallest |L| {e['n']} H {e['H']} width {e['width']} N {e['N']} "
          f"branch {e['branch']} |calA| {e['calA']} ({e['source']})")
