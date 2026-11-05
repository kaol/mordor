"""Compatibility of Sperner good words under enlargement (log §34.3z¹⁰⁶, brief Part III).

Words over P ⊔ U (as in `Sperner.lean`): an ordering starting with a U-letter and ending with a P-letter. Its cells
are its proper prefixes, cell = (A, B) with A = P-letters not yet read, B = U-letters read. A word is good when the
selector f1 is a bijection onto P on its first |P| cells and f2 a bijection onto U on its last |U| cells.
Selectors are GLOBAL (defined on every cell of a fixed universe), as they would be when derived from one F:
f1(A, B) ∈ A, f2(A, B) ∈ B. We test, for random global selectors:
  (R) restriction: deleting a P-letter from a good word of (P ∪ {p}, U) gives a good word of (P, U)?
  (E) extension: every good word of (P, U) extends (by inserting p) to a good word of (P ∪ {p}, U)?
  (C) a compatible chain: good words w_2 ⊂ w_3 ⊂ … ⊂ w_N for P_2 ⊂ … ⊂ P_N = P* (each a restriction of the next)?
Odd counts (`Sperner.odd_goods`) are checked as a control."""
import itertools, random, sys
def cells(word, P, U):
    out = []
    for t in range(1, len(word)):
        pre = word[:t]
        out.append((frozenset(x for x in P if x not in pre), frozenset(x for x in U if x in pre)))
    return out
def valid(word, P, U): return word[0] in U and word[-1] in P
def good(word, P, U, f1, f2):
    if not valid(word, P, U): return False
    cs = cells(word, P, U); kP, kU = len(P), len(U)
    first = [f1[c] for c in cs[:kP]]; last = [f2[c] for c in cs[len(cs) - kU:]]
    return sorted(first) == sorted(P) and sorted(last) == sorted(U)
def goods(P, U, f1, f2): return [w for w in itertools.permutations(list(P) + list(U)) if good(w, P, U, f1, f2)]
def run(nP, nU, trials, seed=0):
    rnd = random.Random(seed); Pstar = [f"p{i}" for i in range(nP)]; Ustar = [f"u{j}" for j in range(nU)]
    allcells = [(frozenset(A), frozenset(B)) for a in range(1, nP + 1) for A in itertools.combinations(Pstar, a)
                for b in range(1, nU + 1) for B in itertools.combinations(Ustar, b)]
    stats = dict(R_fail=0, R_tot=0, E_fail=0, E_tot=0, C_fail=0, odd_fail=0)
    for _ in range(trials):
        f1 = {c: rnd.choice(sorted(c[0])) for c in allcells}; f2 = {c: rnd.choice(sorted(c[1])) for c in allcells}
        G = {}
        for a in range(1, nP + 1):
            P = tuple(Pstar[:a]); G[a] = goods(P, Ustar, f1, f2)
            if len(G[a]) % 2 == 0: stats['odd_fail'] += 1
        for a in range(1, nP):
            p = Pstar[a]; small = set(G[a])
            for w in G[a + 1]:
                stats['R_tot'] += 1
                if tuple(x for x in w if x != p) not in small: stats['R_fail'] += 1
            restr = {tuple(x for x in w if x != p) for w in G[a + 1]}
            for w in G[a]:
                stats['E_tot'] += 1
                if w not in restr: stats['E_fail'] += 1
        # compatible chain from size 1 to nP
        layer = set(G[nP])
        for a in range(nP - 1, 0, -1):
            p = Pstar[a]; layer = {tuple(x for x in w if x != p) for w in layer} & set(G[a])
        if not layer: stats['C_fail'] += 1
    return stats
if __name__ == '__main__':
    for nP, nU, tr in [(3, 1, 300), (3, 2, 200), (4, 2, 60), (4, 3, 15)]:
        print(f"|P*|={nP} |U|={nU} trials={tr}: {run(nP, nU, tr)}", flush=True)
