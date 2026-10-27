"""Box cells and the box Cut Lemma (log §34.3z¹⁵, second opinion on a uniform potential).

A box cell is F(x, y) with x ∈ D, y ∉ D, x < y.
  python3 box_cut.py cells H [maxterms]   ground refutation adding only cells that are box cells in the current model
  python3 box_cut.py cut H [maxterms] [opts]   the box Cut theory: no-witness asserted only for s < t; UNSAT means
                                          every bounded poset of edge-height ≤ H has a witness with x < y.
      opts (comma-separated): disk  clauses go to box_H<H>.body, not RAM (same trajectory; on UNSAT writes box_H<H>.cnf)
                              forget=B  bounded transitivity clauses, as in run_height.py (another trajectory)
                              lazyrank  height bound by violated-chain clauses instead of 6n² eager rank clauses
                                        (another trajectory; H = 5 Cut: 98 terms; cut_lean.py does not translate these)
  python3 box_cut.py finite k             the box Cut Lemma on every lattice of closure systems on k points, all D
  python3 box_cut.py minimize H in.pkl    deletion-minimal subterm-closed term set of a certificate (terms as nested
                                          pairs over '⊥', '⊤', e.g. read from tv4/tv5 of CutHeight4/5.lean)
Both ground modes keep WLOG F(⊥,⊤) ∉ D: the box theory is self-dual (the dual of x < y is y <ᵒᵈ x, W1 ↔ W2)."""
import sys, time, pickle
import numpy as np
import cut_ground as c


def box_cells(H, cap):
    orig_fit, orig_exp = c.Ground.fit, c.Ground.expand
    def fit(self, M, cand):                          # non-box cells go to the back of the queue
        fs = orig_fit(self, M, cand)
        return fs + np.array([0 if self.L[x, y] else 10**6 for (_, x, y) in cand], dtype=fs.dtype)
    def expand(self, M, cap):
        n = len(self.terms); D = [self.d(i) in M for i in range(n)]
        if not any(D[x] and not D[y] and self.L[x, y] and (x, y) not in self.F for x in range(n) for y in range(n)):
            return 0                                     # closed under the box rule
        return orig_exp(self, M, cap)
    c.Ground.fit, c.Ground.expand = fit, expand
    return c.run(H, cap, per_round=1, wlog=True, room='fit')


def box_theory(H, cap, opts=()):
    orig_add = c.Ground.add_term
    def add_term(self, st, dep):
        nw = self.nowitness; self.nowitness = False
        i = orig_add(self, st, dep); self.nowitness = nw
        if st is not None and nw and st[0] != st[1]:
            s, t = st
            self.S.add_clause([-self.d(s), self.d(t), -self.le(s, t), -self.le(i, s)])
            self.S.add_clause([-self.d(s), self.d(t), -self.le(s, t), -self.le(t, i)])
        return i
    c.Ground.add_term = add_term
    body = f"box_H{H}.body" if 'disk' in opts else None
    fg = next((int(float(o.split('=')[1])) for o in opts if o.startswith('forget=')), None)
    if fg: body = None                                   # forget keeps compact clause stores; .cnf written from them
    ok, G = c.run(H, cap, per_round=1, wlog=True, room='fit', stream=body, lazy_rank='lazyrank' in opts, forget=fg)
    if ok and fg: c.write_dimacs(G, f"box_H{H}.cnf"); print(f"wrote box_H{H}.cnf", flush=True)
    if ok and body: c.write_dimacs(G, f"box_H{H}.cnf"); print(f"wrote box_H{H}.cnf ({G.nclauses} clauses)", flush=True)
    return ok, G


def finite(k):
    from lat import moore_family, downsets
    from pysat.solvers import Cadical153
    seen = cx = 0; t0 = time.time()
    for L in moore_family(k):
        if L.n < 3: continue
        n = L.n; nv = 0; cl = []
        Fv = [[list(range(nv + 1 + n * (n * x + y), nv + 1 + n * (n * x + y + 1))) for y in range(n)] for x in range(n)]
        for x in range(n):
            for y in range(n):
                cl.append(Fv[x][y]); cl += [[-Fv[x][y][i], -Fv[x][y][j]] for i in range(n) for j in range(i + 1, n)]
        for (x, x2) in L.covers:                         # F monotone in each argument (covers suffice)
            for y in range(n):
                for p in range(n):
                    for q in range(n):
                        if not L.leq[p][q]: cl += [[-Fv[x][y][p], -Fv[x2][y][q]], [-Fv[y][x][p], -Fv[y][x2][q]]]
        for D in downsets(L):
            if 0 not in D or 1 in D: continue
            s = Cadical153(bootstrap_with=cl)
            for x in D:
                for y in range(n):
                    if y in D or not L.leq[x][y]: continue
                    for v in range(n):
                        if L.leq[v][x] or L.leq[y][v]: s.add_clause([-Fv[x][y][v]])
            seen += 1
            if s.solve(): cx += 1; print('box Cut fails:', n, sorted(D), flush=True)
            s.delete()
    print(f'k={k}: {seen} (L, D) pairs, {cx} without a box witness, {time.time() - t0:.0f}s')


def minimize(H, T):
    depth = lambda t: 0 if not isinstance(t, tuple) else 1 + max(depth(t[0]), depth(t[1]))
    has = lambda u, t: u == t or (isinstance(u, tuple) and (has(u[0], t) or has(u[1], t)))
    def unsat(T):
        G = c.Ground(H, True, False, False, None, False, False); idx = {'⊥': 0, '⊤': 1}
        for t in sorted(T, key=depth):
            if t not in idx: idx[t] = G.add_term((idx[t[0]], idx[t[1]]), depth(t))
        G.S.add_clause([-G.d(idx[('⊥', '⊤')])])
        return G.solve() is None
    T = set(T); assert unsat(T)
    for t in sorted(T, key=lambda t: -depth(t)):
        if t in ('⊥', '⊤', ('⊥', '⊤')) or t not in T: continue
        T2 = {u for u in T if not has(u, t)}
        if unsat(T2): T = T2
    return sorted(T, key=lambda t: (depth(t), str(t)))


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'cells': box_cells(int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 3000)
    elif mode == 'cut': box_theory(int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 3000,
                                   sys.argv[4].split(',') if len(sys.argv) > 4 else ())
    elif mode == 'finite': finite(int(sys.argv[2]))
    elif mode == 'minimize':
        T = pickle.load(open(sys.argv[3], 'rb')); M = minimize(int(sys.argv[2]), T)
        print(f'{len(T)} -> {len(M)} terms'); pickle.dump(M, open(sys.argv[3] + '.min', 'wb'))
