"""Free census (no SAT), every stored W0+n1 model.
SELF-CLOSED: T in L with F(z, T) <= T for every z in Z with z <= T (the minimal virtual row G_T of T maps T below T).
Then down(T) with the rows of Z cap down(T) is again a W0-type world with top T (if h(T) >= 3).
T-relative landing lam_T(x): first element of height <= 2 on x's descent from T; T-fixed atom: atom q of Z, q <= T,
lam_T(q) not in Z, phi(lam_T(q)) = q.
Statements (quantifier: every model, every high self-closed T):
  LiftFix   every T-fixed atom is mu-fixed in L.            FAIL = a T-fixed atom that is not L-fixed.
  FixT      some T-fixed atom exists (CertAtom of the restricted world; holds if CertAtom is a theorem). FAIL = none.
Also: for minimal high self-closed T whether G_T(T) is low (one-step landing, TopRow applies) or = T."""
import lib, collections, sys, json
print(__doc__)
D = [(n, w) for n, w, i, l in lib.get() if i]
C = collections.Counter(); fails = []
for name, w in D:
    A = lib.colours(w); unb = not lib.bounded(w, A); L = w.L; F = w.F; le = w.le; h = w.h
    Lfix = set(q for q in w.atoms if w.fixed(q))
    def G(T, y):
        v = w.bot
        for z in w.Z:
            if le[z][T]: v = L.join[v][F[z][y]]
        return v
    SC = [T for T in range(w.n) if h[T] >= 3 and le[G(T, T)][T]]
    mins = [T for T in SC if not any(T2 != T and le[T2][T] for T2 in SC)]
    tag = ('unb' if unb else 'bdd', '|A|=%d' % len(A))
    C[tag + ('#highSC=%s' % ('1' if len(SC) == 1 else '>1'),)] += 1
    for T in SC:
        Tfix = set(q for q in w.atoms if le[q][T] and (lambda p: p is not None and p not in w.Z and F[w.bot][p] == q)(lib.lamfrom(w, q, T)))
        ok = Tfix <= Lfix
        C[tag + ('LiftFix', 'holds' if ok else 'FAIL')] += 1
        C[tag + ('FixT', 'holds' if Tfix else 'FAIL')] += 1
        if not ok: fails.append((name, T, sorted(Tfix), sorted(Lfix)))
        if T in mins:
            g = G(T, T)
            C[tag + ('minT', 'G_T(T) low' if h[g] <= 2 else ('G_T(T)=T' if g == T else 'other'), 'T=top' if T == w.top else 'T<top')] += 1
for k, v in sorted(C.items(), key=str): print(v, k)
print('LiftFix failures (first 10):', fails[:10])
json.dump(fails, open('selfclosed_fails.json', 'w'))
