"""Orbit laxity of the transposed Cut Lemma (§32.6).

Stages R_0 = ↓⊥, R_{k+1} = Θ(R_k) = ↓(R_k ∪ a(R_k) ∪ b⁻¹(R_k)) in O(L); r_0 = ⊥, r_{k+1} = κ(r_k) = r_k ∨ a(r_k) ∨ ⋁{y : b(y) ≤ r_k}.
The lax square gives ⋁R_k ≤ r_k. Question: does equality fail on the actual orbit, and on which lattices?

Lemma (proved in §32.6): if R_k = ↓s is principal and s = r_k then ⋁R_{k+1} = κ(s) = r_{k+1}. So strictness first appears after a
non-principal R_k with ⋁R_k = r_k < ⊤; a lattice in which every non-principal down-set has join ⊤ ("top-closed") admits none.
z3 decides existence of F with ⋁R_k ≠ r_k for some k ≤ K; prints a witness (a, b and the stage sequences), checked by gpu/reference.

  python3 orbit_lax.py            # default lattice list
  python3 orbit_lax.py B3 N5"""
import os, sys, itertools
import numpy as np, z3
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'gpu'))
import lattices, reference


def downsets(L):
    n = L.n
    for bits in itertools.product([0, 1], repeat=n):
        S = [i for i in range(n) if bits[i]]
        if all(bits[z] for s in S for z in range(n) if L.leq[z, s]): yield S


def top_closed(L):
    """Every non-principal down-set has join ⊤."""
    J = lambda S: next(z for z in range(L.n) if all(L.leq[s, z] for s in S) and
                       all(L.leq[z, w] for w in range(L.n) if all(L.leq[s, w] for s in S)))
    prin = lambda S: any(set(S) == {z for z in range(L.n) if L.leq[z, s]} for s in S)
    return all(prin(S) or J(S) == L.top for S in downsets(L) if S)


def search(L, K=None, delay=0):
    """F with r_k ≰ ⋁R_{k+delay} for some k ≤ K (delay 0: the orbit is not tight)."""
    n = L.n; K = K or n; R = range(n)
    s = z3.Solver()
    F = [[z3.Int(f'F_{x}_{y}') for y in R] for x in R]
    leq = lambda u, v: z3.Or([z3.And(u == i, v == j) for i in R for j in R if L.leq[i, j]])
    for x in R:
        for y in R:
            s.add(F[x][y] >= 0, F[x][y] < n)
    for x, y in itertools.product(R, R):                                # monotone along covers
        for x2 in R:
            if x2 != x and L.leq[x, x2]: s.add(leq(F[x][y], F[x2][y]))
        for y2 in R:
            if y2 != y and L.leq[y, y2]: s.add(leq(F[x][y], F[x][y2]))
    # a(x) = greatest fixed point of F(x,·), b(y) = least fixed point of F(·,y): one-hot booleans
    A = [[z3.Bool(f'a_{x}_{v}') for v in R] for x in R]; Bv = [[z3.Bool(f'b_{y}_{v}') for v in R] for y in R]
    for x in R:
        s.add(z3.PbEq([(A[x][v], 1) for v in R], 1))
        for v in R:
            fix = [F[x][y] == y for y in R]
            s.add(A[x][v] == z3.And(fix[v], *[z3.Not(fix[y]) for y in R if not L.leq[y, v]]))
    for y in R:
        s.add(z3.PbEq([(Bv[y][v], 1) for v in R], 1))
        for v in R:
            fix = [F[x][y] == x for x in R]
            s.add(Bv[y][v] == z3.And(fix[v], *[z3.Not(fix[x]) for x in R if not L.leq[v, x]]))
    join = lambda S: [z3.And(*[z3.Not(S[i]) for i in R if not L.leq[i, j]],               # j upper bound of S
                             *[z3.Or(*[S[i] for i in R if not L.leq[i, k]]) for k in R if not L.leq[j, k]])
                      for j in R]                                            # one-hot ⋁S: j ub, and no k ⋡ j is an ub
    Rk = [z3.BoolVal(L.leq[i, L.bot]) for i in R]
    rk = [z3.BoolVal(i == L.bot) for i in R]                                  # one-hot r_k
    diff = []
    stages = []
    for k in range(K + delay):
        aR = [z3.Or(*[z3.And(Rk[x], A[x][v]) for x in R]) for v in R]           # a(R_k) as a set
        bR = [z3.Or(*[z3.And(Bv[y][v], Rk[v]) for v in R]) for y in R]          # b⁻¹(R_k)
        U = [z3.Or(Rk[i], aR[i], bR[i]) for i in R]
        R2 = [z3.Or(*[U[j] for j in R if L.leq[i, j]]) for i in R]
        # κ(r_k) = r_k ∨ a(r_k) ∨ ⋁{y : b(y) ≤ r_k}: the set whose join it is
        Kset = [z3.Or(rk[i], z3.Or(*[z3.And(rk[x], A[x][i]) for x in R]),
                      z3.Or(*[z3.And(Bv[i][v], rk[w]) for v in R for w in R if L.leq[v, w]])) for i in R]
        r2v = [z3.Bool(f'r_{k+1}_{j}') for j in R]; s.add(*[r2v[j] == join(Kset)[j] for j in R])
        sR2 = [z3.Bool(f's_{k+1}_{j}') for j in R]; s.add(*[sR2[j] == join(R2)[j] for j in R])
        Rv = [z3.Bool(f'R_{k+1}_{i}') for i in R]; s.add(*[Rv[i] == R2[i] for i in R])
        stages.append((Rv, sR2, r2v))
        Rk, rk = Rv, r2v
    for k in range(K):                                                       # r_{k+1} ≰ ⋁R_{k+1+delay}
        r_, s_ = stages[k][2], stages[k + delay][1]
        diff.append(z3.Or(*[z3.And(r_[i], s_[j]) for i in R for j in R if not L.leq[i, j]]))
    s.add(z3.Or(*diff))
    if s.check() != z3.sat: return None
    M = s.model()
    Fv = np.array([[M.eval(F[x][y]).as_long() for y in R] for x in R])
    return Fv


def orbits(L, F):
    """Plain-set recomputation (independent of the z3 encoding): ([⋁R_k], [r_k]) until both are stable."""
    o = reference.observe_one(L, F); a, b, n, R = o['a'], o['b'], L.n, range(L.n)
    down = lambda S: {z for z in R if any(L.leq[z, t] for t in S)}
    J = lambda S: next(z for z in R if all(L.leq[t, z] for t in S) and all(L.leq[z, w] for w in R if all(L.leq[t, w] for t in S)))
    D, r, sR, rs = down({L.bot}), L.bot, [], []
    for _ in range(2 * n + 2):
        sR.append(J(D)); rs.append(r)
        D, r = down(D | {a[x] for x in D} | {y for y in R if b[y] in D}), J({r, a[r]} | {y for y in R if L.leq[b[y], r]})
    return sR, rs


def delay(L, F):
    """Least d with r_k ≤ ⋁R_{k+d} for all k."""
    sR, rs = orbits(L, F)
    return next(d for d in range(len(rs)) if all(L.leq[rs[k], sR[min(k + d, len(sR) - 1)]] for k in range(len(rs))))


if __name__ == '__main__':
    specs = sys.argv[1:] or ['C4', 'B2', 'M3', 'N5', 'C2xC3', 'B3', 'E2', 'D3', 'C3xC3']
    for spec in specs:
        L = lattices.parse(spec)
        for d in (1, 2):
            W = search(L, delay=d)
            if W is not None: assert delay(L, W) > d
            print(f'{spec:6} delay-{d} simulation (r_k ≤ ⋁R_(k+{d}) for all k): ' + ('holds (unsat)' if W is None else
                  f'fails: (⋁R_k, r_k) = {list(zip(*orbits(L, W)))[:5]}, a={reference.observe_one(L, W)["a"]}, '
                  f'b={reference.observe_one(L, W)["b"]}'), flush=True)
            if W is None: break
        tc = top_closed(L)
        Fv = search(L)
        if Fv is None:
            print(f'{spec:6} n={L.n} top-closed={tc}: no F with ⋁R_k ≠ r_k (unsat)', flush=True); continue
        o = reference.observe_one(L, Fv)
        assert o['laxfirst'] >= 0 and not o['trip_lax'] and not o['trip_pcut'], o
        sR, rs = orbits(L, Fv); assert any(u != v for u, v in zip(sR, rs))
        print(f'{spec:6} n={L.n} top-closed={tc}: witness, first strict stage {o["laxfirst"]}, polar={o["polar"]}, '
              f'a={o["a"]} b={o["b"]}', flush=True)
