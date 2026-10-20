"""Finitely generated cuts (log §34.3m): ground refutation of the cut theory with NO height bound, for down-sets
D = ↓p₁ ∪ … ∪ ↓p_k and complements U = ↑u₁ ∪ … ∪ ↑u_l (constants p_i ∈ D, u_j ∉ D; every term in D lies below some
p_i, every term outside D above some u_j). UNSAT proves the Cut Lemma for every such cut in every bounded poset, of
any height, finite or infinite (ladders need a down-set without maximal elements).

  python3 cut_gen.py K L [maxterms]"""
import sys, time
import cut_ground as C


def run(k, l, maxterms=3000, per_round=1, lattice=False):
    G = C.Ground(H=50, lazy_rank=True, room='fit')          # lazy_rank with no chain check: no height axiom at all
    G.chains = lambda L: 0
    P = [G.add_term(None, 0) for _ in range(k)]; U = [G.add_term(None, 0) for _ in range(l)]
    S = G.S
    for p in P: S.add_clause([G.d(p)])
    for u in U: S.add_clause([-G.d(u)])
    lat = []                                                  # (kind, a, b, c): c = a ∧ b or a ∨ b, universal over terms
    if lattice:                                               # meets of subsets of P, joins of subsets of U
        import itertools as _it
        for r in range(2, k + 1):
            for A in _it.combinations(P, r):
                c = G.add_term(None, 0); lat.append(('meet', A, c))
                for a in A: S.add_clause([G.le(c, a)])
        for r in range(2, l + 1):
            for B in _it.combinations(U, r):
                c = G.add_term(None, 0); lat.append(('join', B, c))
                for b in B: S.add_clause([G.le(b, c)])
    lat_done = set()
    def lattice_axioms():
        for (kind, A, c) in lat:
            for t in range(len(G.terms)):
                if (c, t) in lat_done: continue
                lat_done.add((c, t))
                if kind == 'meet': S.add_clause([-G.le(t, a) for a in A] + [G.le(t, c)])
                else: S.add_clause([-G.le(a, t) for a in A] + [G.le(c, t)])
    gen_done = set()
    def generation():
        for t in range(len(G.terms)):
            if t in gen_done: continue
            gen_done.add(t)
            S.add_clause([-G.d(t)] + [G.le(t, p) for p in P])     # D = ↓P
            S.add_clause([G.d(t)] + [G.le(u, t) for u in U])      # U = ↑U
    orig_add = G.add_term
    def add_term(st, dep):
        i = orig_add(st, dep); generation(); lattice_axioms(); return i
    G.add_term = add_term
    generation(); lattice_axioms()
    G.add_term((0, 1), 1)                                     # seed F(⊥, ⊤)
    t0 = time.time(); rnd = 0
    while True:
        rnd += 1
        M = G.solve()
        if M is None:
            print(f"k={k}, l={l}: UNSAT with {len(G.terms)} terms after {rnd} rounds, {time.time()-t0:.1f}s: "
                  f"the Cut Lemma holds for every {k}x{l}-generated cut in every bounded {'lattice' if lattice else 'poset'}", flush=True)
            return True, G
        if len(G.terms) >= maxterms:
            print(f"k={k}, l={l}: inconclusive at {len(G.terms)} terms", flush=True); return False, G
        if not G.expand(M, per_round):
            print(f"k={k}, l={l}: SAT, closed under the term rule ({len(G.terms)} terms): a partial model", flush=True)
            return False, G
        if rnd % 50 == 0: print(f"  round {rnd}: {len(G.terms)} terms, {time.time()-t0:.0f}s", flush=True)


if __name__ == '__main__':
    k, l = int(sys.argv[1]), int(sys.argv[2])
    run(k, l, int(sys.argv[3]) if len(sys.argv) > 3 else 3000, lattice='--lattice' in sys.argv)
