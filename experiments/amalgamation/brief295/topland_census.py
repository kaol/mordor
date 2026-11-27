"""Free check on stored models (no SAT; from the definitions via brief291/world.py). Samples only, except that a
single failing W0 model refutes a universal statement.

  calA  = atoms of Z of the form phi(w) (phi = F(bot, .)); all lie below t1 = phi(top).
  X     = join of calA (in L);  G_X(y) = join of F(z, y) over z in Z with z <= X  (the least row an element X can carry
          once the rows outside Z are normalized; CertAtom only sees the rows of Z).
  TopLand(X): the iteration of G_X from top reaches an element of height <= 2.          FAIL = W0 model where it does not.
  TopRow (paper + Lean, brief run 20 §4): TopLand ==> CertAtom, and more precisely the first low element p of the G_X
          iteration lies outside Z and c = phi(p) is a mu-fixed atom.   PROOF-FAIL = p in Z, or c not mu-fixed.
  Same for X = t1 (the larger row G_t1).
  Also: is X in Z (then TopLand holds by Ta at the row X)."""
import sys, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import load_all, dedup

def joinrow(w, xs):
    J = w.L.join if hasattr(w.L, 'join') else None
    def j(a, b): return J[a][b]
    return lambda y: (lambda vals: __import__('functools').reduce(j, vals, w.bot))([w.F[z][y] for z in xs])

def iterate_land(w, g):
    v = w.top; seen = []
    while v not in seen:
        if w.h[v] <= 2: return v, len(seen)
        seen.append(v); v = g(v)
    return None, len(seen)

C = collections.Counter()
for name, w in dedup(load_all(sys.argv[1:])):
    try:
        if not (w.base() and w.w0flat() and w.w0()): continue
    except Exception: continue
    d, N = w.dN(); br = 'a' if w.h[d] == 2 else 'atom'; tag = (br, 'N1' if N == 1 else 'N>=2')
    phi = w.F[w.bot]; L = w.L
    calA = sorted({phi[y] for y in range(w.n) if phi[y] != w.bot and w.h[phi[y]] == 1 and phi[phi[y]] == w.bot})
    X = w.bot
    for q in calA: X = L.join[X][q]
    t1 = phi[w.top]
    for lab, Y in (('X=join calA', X), ('X=t1', t1)):
        rows = [z for z in w.Z if w.le[z][Y]]
        p, k = iterate_land(w, joinrow(w, rows))
        if p is None:
            C[tag + (lab, 'TopLand FAIL')] += 1
            if lab == 'X=join calA': print('TopLand FAIL', name, 'n', w.n, 'H', w.h[w.top], 'N', N, br, '|calA|', len(calA), 'X in Z', X in w.Z)
            continue
        if phi[p] == w.bot: res = 'PROOF-FAIL p in Z'
        else:
            c = phi[p]; res = 'c fixed' if (c in w.atoms and w.fixed(c)) else 'PROOF-FAIL c not fixed'
        C[tag + (lab, 'TopLand holds', res, 'X in Z' if Y in w.Z else 'X not in Z')] += 1
        if 'PROOF-FAIL' in res: print(res, name)
print(__doc__)
for k, v in sorted(C.items(), key=str): print(v, k)

# ---- TopLand_S: virtual row g_S = join of the rows of S = {bot} + calA + {q v q' in Z : q, q' in calA} ----
print('\nTopLand_S (virtual row over S = {bot} u calA u {q v q\' in Z}); FAIL = W0 model whose g_S iteration never gets low;')
print('PROOF-FAIL = first low p of the g_S iteration lies in Z, or phi(p) is not mu-fixed.')
C2 = collections.Counter(); fails = []
for name, w in dedup(load_all(sys.argv[1:])):
    try:
        if not (w.base() and w.w0flat() and w.w0()): continue
    except Exception: continue
    d, N = w.dN(); br = 'a' if w.h[d] == 2 else 'atom'; tag = (br, 'N1' if N == 1 else 'N>=2')
    phi = w.F[w.bot]; L = w.L
    calA = sorted({phi[y] for y in range(w.n) if phi[y] != w.bot and w.h[phi[y]] == 1 and phi[phi[y]] == w.bot})
    S = {w.bot} | set(calA) | {L.join[a][b] for a in calA for b in calA if a != b and L.join[a][b] in w.Z}
    p, k = iterate_land(w, joinrow(w, sorted(S)))
    if p is None:
        C2[tag + ('TopLand_S FAIL', '|calA|=%d' % len(calA))] += 1; fails.append((w.n, w.h[w.top], N, br, len(calA), name)); continue
    res = 'PROOF-FAIL p in Z' if phi[p] == w.bot else ('c fixed' if w.fixed(phi[p]) else 'PROOF-FAIL c not fixed')
    C2[tag + ('TopLand_S holds', res)] += 1
    if 'PROOF' in res: print(res, name)
for k, v in sorted(C2.items(), key=str): print(v, k)
for f in sorted(fails): print('  TopLand_S fails:', f)
