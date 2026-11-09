"""Lattice ground refutation with a bound on the height of the cut (log §34.3z¹⁴³).

lattice_ground.LGround (edge-height ≤ H, lattice terms, no-witness, WLOG F(⊥,⊤) ∉ D) plus the lazy axiom family
"no strict chain ⊥ < z₁ < … < z_{r+1} with z_{r+1} ∈ D" (D has height ≤ r). UNSAT proves: on every bounded lattice of
edge-height ≤ H, every cut D of height ≤ r has a witness for every monotone F. (r = 1 is a Lean theorem at every
height, `BottomMaxCell.cut_of_atomic`; r = H is the unrestricted theory.)
  python3 dheight_ground.py H r maxterms per_round J [seconds] [--dimacs OUT.cnf] [--stream CLAUSES.txt]
                            [--forget B] [--every N]
--dimacs: on UNSAT write the clause set (DIMACS) for an independent check (drat_certify.py, then cut_lean.py-style
replay). --stream: keep the clause log on disk instead of in memory (needed for --dimacs at large sizes).
--forget B: rebuild the solver from the live transitivity clauses once more than B are kept (cut_ground's memory
option). --every N: progress line every N rounds (default 1).
"""
import sys, time, resource
import numpy as np
import lattice_ground as lg

class DGround(lg.LGround):
    rD = None
    def solve(self):
        while True:
            M = super().solve()
            if M is None: return None
            if not self.d_chains(self.L, M): return M

    def d_chains(self, L, M, cap=400):
        n = len(L); S = L & ~L.T; D = np.array([self.d(i) in M for i in range(n)])
        order = np.argsort(S.sum(0), kind='stable')
        length = np.ones(n, dtype=int); pred = -np.ones(n, dtype=int)
        for q in order:
            ps = np.nonzero(S[:, q])[0]
            if len(ps): p = ps[np.argmax(length[ps])]; length[q] = length[p] + 1; pred[q] = p
        added = 0
        for q in np.argsort(-length)[:cap * 4]:
            if added >= cap: break
            if length[q] <= self.rD + 1: break
            if not D[q]: continue
            ch = [int(q)]
            while pred[ch[-1]] >= 0: ch.append(int(pred[ch[-1]]))
            ch = ch[::-1][-(self.rD + 2):]
            c = [-self.d(ch[-1])]
            for a, b in zip(ch, ch[1:]): c += [-self.le(a, b), self.le(b, a)]
            self.S.add_clause(c); added += 1
        return added

def run(H, r, maxterms, per_round, J, seconds, dimacs=None, stream=None, forget=None, every=1):
    G = DGround(H, True, False, False, stream, 'front', False, forget); G.lat_keys = set(); G.rD = r
    cc = G.add_term((0, 1), 1); G.S.add_clause([-G.d(cc)])
    t0 = time.time(); rnd = 0
    while True:
        rnd += 1; M = G.solve()
        if M is None:
            print(f"H={H}, D-height ≤ {r}: UNSAT with {len(G.terms)} terms ({len(G.F)} F, {len(G.latt)} lattice), "
                  f"{rnd} rounds, {time.time() - t0:.1f}s", flush=True)
            if dimacs:
                import cut_ground; cut_ground.write_dimacs(G, dimacs); print(f"clauses written to {dimacs}", flush=True)
            return True
        if len(G.terms) >= maxterms or time.time() - t0 > seconds:
            print(f"H={H}, D-height ≤ {r}: inconclusive, SAT at {len(G.terms)} terms, {rnd} rounds, {time.time() - t0:.0f}s", flush=True)
            return False
        a = G.expand(M, per_round); b = G.expand_lat(M, J)
        if rnd % every == 0:
            print(f"  round {rnd}: {len(G.terms)} terms ({len(G.F)} F, {len(G.latt)} lattice), {G.nclauses} clauses, "
                  f"{time.time() - t0:.0f}s, RSS {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6:.2f} GB", flush=True)
        if not a and not b:
            print(f"H={H}, D-height ≤ {r}: closed partial model at {len(G.terms)} terms", flush=True); return False

if __name__ == '__main__':
    args = sys.argv[1:]; opt = {}
    for k in ('--dimacs', '--stream', '--forget', '--every'):
        if k in args: i = args.index(k); opt[k] = args[i + 1]; del args[i:i + 2]
    H, r, cap, pr, J = (int(x) for x in args[:5]); secs = float(args[5]) if len(args) > 5 else 1e9
    run(H, r, cap, pr, J, secs, opt.get('--dimacs'), opt.get('--stream'),
        int(opt['--forget']) if '--forget' in opt else None, int(opt.get('--every', 1)))
