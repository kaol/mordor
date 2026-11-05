"""Deletion lemma for Sperner good words (log §34.3z¹⁰⁸).

Conjecture (D): for global selectors f1(A,B) ∈ A, f2(A,B) ∈ B and a good word w of (A, B) with |A| + |B| ≥ 3, some
letter x (keeping A, B nonempty) can be deleted so that w − x is a good word of (A − x, B − x).
(D) iterated gives a compatible chain down to (1, 1) — i.e. Lemma A′ of §34.3z¹⁰⁷ — for ANY selectors.
We test (D) per good word, and the weaker (D′): SOME good word of (A, B) admits a full deletion chain."""
import itertools, random, sys
from good_words import cells, good, valid
def deletable(w, A, B, f1, f2):
    out = []
    for x in w:
        A2 = tuple(a for a in A if a != x); B2 = tuple(b for b in B if b != x)
        if not A2 or not B2: continue
        w2 = tuple(y for y in w if y != x)
        if good(w2, A2, B2, f1, f2): out.append((x, w2, A2, B2))
    return out
def full_chain(w, A, B, f1, f2, memo):
    if len(A) == 1 and len(B) == 1: return True
    key = w
    if key in memo: return memo[key]
    r = any(full_chain(w2, A2, B2, f1, f2, memo) for _, w2, A2, B2 in deletable(w, A, B, f1, f2))
    memo[key] = r; return r
def run(nP, nU, trials, seed=1):
    rnd = random.Random(seed); P = tuple(f"p{i}" for i in range(nP)); U = tuple(f"u{j}" for j in range(nU))
    allcells = [(frozenset(Ac), frozenset(Bc)) for a in range(1, nP + 1) for Ac in itertools.combinations(P, a)
                for b in range(1, nU + 1) for Bc in itertools.combinations(U, b)]
    st = dict(words=0, D_fail=0, chain_fail_word=0, Dprime_fail=0)
    example = None
    for _ in range(trials):
        f1 = {c: rnd.choice(sorted(c[0])) for c in allcells}; f2 = {c: rnd.choice(sorted(c[1])) for c in allcells}
        G = [w for w in itertools.permutations(P + U) if good(w, P, U, f1, f2)]
        memo = {}; anyok = False
        for w in G:
            st['words'] += 1
            if not deletable(w, P, U, f1, f2):
                st['D_fail'] += 1
                if example is None: example = (w, {c: f1[c] for c in allcells}, {c: f2[c] for c in allcells})
            ok = full_chain(w, P, U, f1, f2, memo)
            if not ok: st['chain_fail_word'] += 1
            anyok |= ok
        if not anyok: st['Dprime_fail'] += 1
    return st, example
if __name__ == '__main__':
    for nP, nU, tr in [(2, 2, 500), (3, 2, 300), (2, 3, 300), (3, 3, 60), (4, 2, 60)]:
        st, ex = run(nP, nU, tr)
        print(f"random global selectors |P|={nP} |U|={nU} trials={tr}: {st}", flush=True)
        if ex and nP + nU == 4:
            w, f1, f2 = ex
            print("   smallest D-failure word:", w)
