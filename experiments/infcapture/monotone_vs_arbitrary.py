"""Lemma A′ (some exhaustion admits a compatible chain): F-monotone versus arbitrary admissibility (log §34.3z¹⁰⁸).

1. A minimal ARBITRARY system violating A′: fixed global selectors (singleton admissible sets) for which no good word
   of the full instance has a deletion chain down to (1, 1). We report which persistence law it breaks.
2. Random MONOTONE systems at sizes beyond the CEGAR runs, checked for A′ with selector choice (z3 inner search of
   monotone_good_words.py over all exhaustions). Sampler: random facts z(c) ≤ p / u ≤ z(c), closed under the order
   (down for ≤ p, up for ≥ u), rejected on a cross conflict or a no-witness violation."""
import itertools, random, sys
from good_words import good
from deletion_lemma import full_chain
from monotone_good_words import Universe, inner, all_exhaustions

def find_arbitrary(nP, nU, trials, seed=7):
    rnd = random.Random(seed); P = tuple(f"p{i}" for i in range(nP)); U = tuple(f"u{j}" for j in range(nU))
    cells = [(frozenset(A), frozenset(B)) for a in range(1, nP + 1) for A in itertools.combinations(P, a)
             for b in range(1, nU + 1) for B in itertools.combinations(U, b)]
    for _ in range(trials):
        f1 = {c: rnd.choice(sorted(c[0])) for c in cells}; f2 = {c: rnd.choice(sorted(c[1])) for c in cells}
        G = [w for w in itertools.permutations(P + U) if good(w, P, U, f1, f2)]
        memo = {}
        if not any(full_chain(w, P, U, f1, f2, memo) for w in G):
            # persistence violations: f1(A,B)=p must stay admissible on (A',B') ⊇ in order; with singleton sets this
            # means f1(A',B') = p whenever p ∈ A' ⊆ A, B ⊆ B' (law 1); dually f2 (law 2)
            v1 = [(c, c2) for c in cells for c2 in cells if c2 != c and c2[0] <= c[0] and c[1] <= c2[1]
                  and f1[c] in c2[0] and f1[c2] != f1[c]]
            v2 = [(c, c2) for c in cells for c2 in cells if c2 != c and c[0] <= c2[0] and c2[1] <= c[1]
                  and f2[c] in c2[1] and f2[c2] != f2[c]]
            return f1, f2, len(G), len(v1), len(v2)
    return None

def sample_monotone(un, rnd, nfacts=6, tries=200):
    cells = un.cells
    for _ in range(tries):
        SP = {c: set() for c in cells}; SU = {c: set() for c in cells}
        for _ in range(nfacts):
            c = rnd.choice(cells)
            if rnd.random() < 0.5:
                p = rnd.choice(un.P)
                for c2 in cells:
                    if c2[0] >= c[0] and c2[1] <= c[1]: SP[c2].add(p)      # z(c2) <= z(c) <= p
            else:
                u = rnd.choice(un.U)
                for c2 in cells:
                    if c2[0] <= c[0] and c2[1] >= c[1]: SU[c2].add(u)      # u <= z(c) <= z(c2)
        if all(not (SP[c] and SU[c]) and not c[0] <= SP[c] and not c[1] <= SU[c] for c in cells):
            return SP, SU
    return None

def check_A_prime(nP, nU, SP, SU):
    for st in all_exhaustions(nP, nU):
        un = Universe(st)
        res = inner(un, {c: SP[c] for c in un.cells}, {c: SU[c] for c in un.cells})
        if res is not None and res != 'unknown': return True
    return False

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'arbitrary':
        for nP, nU in [(3, 2), (2, 3)]:
            r = find_arbitrary(nP, nU, 2000)
            if r:
                f1, f2, ng, v1, v2 = r
                print(f"arbitrary singleton system violating A′ at |P|={nP} |U|={nU}: {ng} good words of the full instance, "
                      f"none with a deletion chain; persistence-law violations: law 1 {v1}, law 2 {v2}", flush=True)
    else:
        nP, nU, n = map(int, mode.split('x'))
        rnd = random.Random(11); un0 = Universe(all_exhaustions(nP, nU)[0]); ok = 0; tot = 0
        for k in range(n):
            s = sample_monotone(un0, rnd, nfacts=rnd.randint(3, 10))
            if s is None: continue
            tot += 1; r = check_A_prime(nP, nU, *s); ok += r
            nonempty = sum(1 for c in un0.cells if s[0][c] or s[1][c])
            print(f"  monotone sample {k}: {nonempty} constrained cells, A′ {'holds' if r else 'FAILS'}", flush=True)
        print(f"random monotone systems |P|={nP} |U|={nU}: A′ holds in {ok}/{tot}", flush=True)
