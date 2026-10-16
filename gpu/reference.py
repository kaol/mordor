"""reference.py: plain-python observation of one bifunction, independent of the torch engine.

Derived maps are computed from fixed-point SETS (greatest / least element of {y : F(x,y) = y}), not by Kleene
iteration as on the device, and R(F) by a naive closure. `observe_one` returns the same per-F record that the
engine's `observe` produces; `engine.Plan.selftest` and tests/ compare the two."""
import numpy as np

REL_EQ, REL_LT, REL_GT, REL_INC = 0, 1, 2, 3


def rel(L, u, v):
    if u == v: return REL_EQ
    if L.leq[u, v]: return REL_LT
    if L.leq[v, u]: return REL_GT
    return REL_INC


def greatest(L, S): return next(x for x in S if all(L.leq[y, x] for y in S))
def least(L, S): return next(x for x in S if all(L.leq[x, y] for y in S))


def observe_one(L, F):
    F = np.asarray(F); n = L.n; rng = range(n)
    a = [greatest(L, [y for y in rng if F[x, y] == y]) for x in rng]
    b = [least(L, [x for x in rng if F[x, y] == x]) for y in rng]
    m = least(L, [x for x in rng if a[x] == x]); nn = greatest(L, [y for y in rng if b[y] == y])
    phi = [a[b[x]] for x in rng]; psi = [b[a[x]] for x in rng]
    fa = [a[x] == x for x in rng]; fb = [b[x] == x for x in rng]
    down = lambda S: {z for z in rng if any(L.leq[z, s] for s in S)}
    ideal = lambda S: any(down({z}) == S for z in S)
    J = lambda S: next(z for z in rng if all(L.leq[s, z] for s in S) and all(L.leq[z, w] for w in rng if all(L.leq[s, w] for s in S)))
    R = down({L.bot}); stages = 0; first_bad = -1
    r = L.bot; kst = 0; lax = -1; tlax = False
    for it in range(2 * n + 2):
        if first_bad < 0 and not ideal(R): first_bad = stages
        sR = J(R)
        tlax |= not L.leq[sR, r]
        if lax < 0 and sR != r: lax = it
        r2 = J({r, a[r]} | {y for y in rng if L.leq[b[y], r]})
        R2 = down(R | {a[x] for x in R} | {y for y in rng if b[y] in R})
        grew, rg = R2 != R, r2 != r
        stages += grew; kst += rg; R, r = R2, r2
        if not (grew or rg): break
    defects = [x for x in rng if phi[x] != psi[x]]
    return dict(
        a=a, b=b, m=m, n=nn,
        comm=all(phi[x] == psi[x] for x in rng),
        semi_ba_le_ab=all(L.leq[psi[x], phi[x]] for x in rng),
        semi_ab_le_ba=all(L.leq[phi[x], psi[x]] for x in rng),
        polar=(a[L.bot] == L.bot and b[L.bot] == L.bot and a[L.top] == L.top and b[L.top] == L.top),
        meqn=(m == nn),
        ncf=sum(fa[x] and fb[x] for x in rng),
        ndef=len(defects),
        sig=sorted(16 * rel(L, phi[x], x) + 4 * rel(L, psi[x], x) + rel(L, phi[x], psi[x]) for x in defects),
        rstages=stages, rfull=(len(R) == n), rfirst_nonideal=first_bad, kstages=kst, laxfirst=lax,
        trip_lax=tlax, trip_pcut=r != L.top,
        trip_i1=not L.leq[m, nn], trip_l1=a[nn] != nn, trip_l2=b[m] != m,
        trip_fusion=any((phi[x] == x) != (fa[x] and fb[x]) for x in rng),
        trip_i2=(m == nn) != (sum(fa[x] and fb[x] for x in rng) == 1),
    )
