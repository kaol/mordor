"""Free check on stored models (no SAT; from the definitions via brief291/world.py).

ClosureLand (candidate, brief run 20 P2).  calA = atoms of Z of the form phi(w).  For a set S of rows of Z put
g_S(y) = join_{z in S} F(z, y) (a virtual row) and p(S) = first element of height <= 2 of the g_S-iteration from top.
S is CLOSED when p = p(S) exists and
   (p not in Z and phi(p) in S)  or  (p in Z and calA ^ down(p) <= S and (|calA ^ down(p)| >= 2 ==> p in S)).
TopRow' (paper, brief §4.3): a closed S gives CertAtom, with phi(p) mu-fixed (the p-in-Z branch is contradictory).
Iteration: S_0 = {bot}; while S not closed: if p(S) undefined -> STUCK; else add the missing rows (phi(p), or
calA ^ down(p) and p).  Sets only grow (S_k within {bot} u calA u {q v q' in Z}), so it ends: CLOSED or STUCK.
Quantifier: for every stored W0 model.  FAIL = STUCK.  PROOF-FAIL = closed S whose p is in Z or phi(p) not fixed.
Also reported: the number of rounds, and whether the plain mu-orbit of bot (refuted BotOrbit) reaches a fixed atom."""
import sys, collections, functools
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import load_all, dedup

def first_low(w, rows):
    J = w.L.join
    g = lambda y: functools.reduce(lambda a, b: J[a][b], [w.F[z][y] for z in rows], w.bot)
    v = w.top; seen = set()
    while v not in seen:
        if w.h[v] <= 2: return v
        seen.add(v); v = g(v)
    return None

def closure(w):
    phi = w.F[w.bot]
    calA = {phi[y] for y in range(w.n) if phi[y] != w.bot and w.h[phi[y]] == 1 and phi[phi[y]] == w.bot}
    S = {w.bot}; rounds = 0
    while True:
        rounds += 1
        p = first_low(w, sorted(S))
        if p is None: return 'STUCK', rounds, S, None
        if phi[p] != w.bot:
            need = {phi[p]}
        else:
            Ap = {q for q in calA if w.le[q][p]}
            need = Ap | ({p} if len(Ap) >= 2 else set())
        if need <= S: return 'CLOSED', rounds, S, p
        S |= need

def botorbit_fixed(w):
    x = w.bot; seen = []
    while x is not None and x not in seen:
        seen.append(x); p = w.lam(x)
        if p is None: return False
        x = p if w.F[w.bot][p] == w.bot else w.F[w.bot][p]
        if x in w.atoms and w.fixed(x): return True
    return False

if __name__ == '__main__':
    print(__doc__)
    C = collections.Counter()
    for name, w in dedup(load_all(sys.argv[1:])):
        try:
            if not (w.base() and w.w0flat() and w.w0()): continue
        except Exception: continue
        d, N = w.dN(); br = 'a' if w.h[d] == 2 else 'atom'; tag = (br, 'N1' if N == 1 else 'N>=2')
        res, rounds, S, p = closure(w)
        if res == 'CLOSED':
            phi = w.F[w.bot]
            ok = phi[p] != w.bot and w.fixed(phi[p])
            if not ok: print('PROOF-FAIL', name)
            C[tag + ('CLOSED', 'rounds %d' % rounds, 'botorbit fixed' if botorbit_fixed(w) else 'botorbit NOT fixed')] += 1
        else:
            C[tag + ('STUCK',)] += 1; print('STUCK', name, 'n', w.n, 'H', w.h[w.top], 'N', N, br, 'S', sorted(S))
    for k, v in sorted(C.items(), key=str): print(v, k)
