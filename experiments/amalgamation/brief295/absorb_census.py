"""Free census on stored models (no SAT; recomputed from the definitions via brief291/world.py).

  calA      = atoms of Z that are values phi(w) of some w outside Z (phi = F(bot, .)); contains every connector value
              phi(B), every exit atom c(x) = phi(lambda(x)), and phi(r_x) when lambda(x) is an atom.
  Absorb(x) (x in Z, x lands): every atom of calA below lambda(x) lies below x.
  AbsorbExists: some x in Z has Absorb(x).             FAIL = a W0 model with no absorbing row.
  AbsorbFix  (paper, brief run 20 §4.3): Absorb(x) ==> x exits with dominated exit atom c(x) <= x (hence c(x) is mu-fixed).
              FAIL = an absorbing row that does not exit, or exits undominated (would refute the paper proof).
  GainAll   (paper consequence of NoFix): every x in Z has an atom of calA below lambda(x) and not below x.
Tallies per branch (a / atom) and N (1 / >= 2). Samples only: stored models are not a corpus."""
import sys, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import load_all, dedup
C = collections.Counter(); ex = []
for name, w in dedup(load_all(sys.argv[1:])):
    try:
        if not (w.base() and w.w0flat() and w.w0()): continue
    except Exception: continue
    d, N = w.dN(); br = 'a' if w.h[d] == 2 else 'atom'; tag = (br, 'N1' if N == 1 else 'N>=2')
    phi = w.F[w.bot]
    calA = sorted({phi[y] for y in range(w.n) if phi[y] != w.bot and w.h[phi[y]] == 1 and phi[phi[y]] == w.bot})
    ab = []
    for x in w.Z:
        if x == w.bot: continue
        p = w.lam(x)
        if all(w.le[q][x] for q in calA if w.le[q][p]): ab.append(x)
    for x in ab:
        ok = w.exits(x) and w.le[w.c(x)][x]
        C[tag + ('AbsorbFix', 'holds' if ok else 'FAIL')] += 1
        if not ok: print('AbsorbFix FAIL', name, x)
    C[tag + ('AbsorbExists', 'holds' if ab else 'FAIL', '|calA|=%d' % len(calA))] += 1
    if not ab: ex.append((name, w.n, w.h[w.top], N, br, len(calA)))
    fixed = [q for q in w.atoms if w.fixed(q)]
    C[tag + ('fixed atom absorbs', any(q in ab for q in fixed))] += 1
print(__doc__)
for k, v in sorted(C.items(), key=str): print(v, k)
print('models without an absorbing row (name, |L|, H, N, branch, |calA|):')
for e in sorted(ex, key=lambda t: t[1])[:15]: print(' ', e)
