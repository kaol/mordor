"""The double-cone chain map of RelativeCut (log §34.3z³⁷) on the ladder (log §34.3z⁵⁸).

D = ℕ (⊥ = 0), C = {⊤}, F(n, ⊤) = n + 1: a witness-free cut of the chain ℕ ∪ {ω} (DCC, not ACC). The labelling
z(ρ, σ) = F(min ρ, max σ) = min ρ + 1 is a `RelativeCut.Labelling` on an infinite D. Faces are nonempty finite
subsets of ℕ (chains of D ⊕ (C ∖ ⊤)). G σ τ = #words over τ ∪ {⊤} labelled exactly σ, plus, when 0 ∉ τ, over
τ ∪ {0} (mod 2), as in `RelativeCut.G`. Checks, over all faces τ ⊆ {0..N}:
  * G is locally finite, and G ∂ = ∂ G (the chain-map identity `RelativeCut.chain`);
  * G is exactly the shift τ ↦ τ + 1 (the only word with distinct labels lists τ increasingly after ⊤), so every
    diagonal entry G(τ, τ) is 0 and the diagonal sum is 0;
  * the column of {0} has total 1 (the single word ⊤ 0, label 1): the quantity `ConeSperner.trace_chain` equates with
    the trace on a finite cone.
So on an infinite cone the Hopf trace formula fails although G is a locally finite chain map with finite diagonal sum."""
import itertools, sys
from collections import Counter
N = int(sys.argv[1]) if len(sys.argv) > 1 else 6
TOP = 'T'
def words(alph):
    for w in itertools.permutations(alph):
        if w[0] == TOP and w[-1] != TOP: yield w
def labels(w):           # cut t: pre = w[:t+1], post = w[t+1:]; label = min(post D-letters) + 1
    return [min(x for x in w[t + 1:] if x != TOP) + 1 for t in range(len(w) - 1)]
def G(tau):              # column of G at tau: Counter of sigma (frozenset) -> count mod 2
    col = Counter()
    for alph in [tuple(tau) + (TOP,)] + ([tuple(tau) + (0,)] if 0 not in tau else []):
        for w in words(alph):
            L = labels(w)
            if len(set(L)) == len(L): col[frozenset(L)] += 1
    return {s: c % 2 for s, c in col.items() if c % 2}
def bd(tau):             # simplicial boundary over F2, non-augmented
    return Counter(frozenset(tau - {x}) for x in tau) if len(tau) > 1 else Counter()
def add(*cs):
    out = Counter()
    for c in cs:
        for k, v in c.items(): out[k] += v
    return {k: v % 2 for k, v in out.items() if v % 2}
faces = [frozenset(s) for r in range(1, 4) for s in itertools.combinations(range(N + 1), r)]
ok = True; diag = 0; shift = True
for tau in faces:
    Gt = G(tau)
    lhs = add(*[Counter({s: v * m for s, v in G(f).items()}) for f, m in bd(tau).items() if m % 2])   # G ∂ τ
    rhs = add(*[Counter({f: m * v for f, m in bd(s).items()}) for s, v in Gt.items()])               # ∂ G τ
    if lhs != rhs: ok = False; print("chain map fails at", sorted(tau), lhs, rhs); break
    diag += Gt.get(tau, 0)
    shift &= Gt == {frozenset(x + 1 for x in tau): 1}
print(f"faces of size ≤ 3 in {{0..{N}}}: {len(faces)};  G∂ = ∂G: {ok};  G = shift: {shift};  diagonal sum: {diag % 2};"
      f"  column of {{0}}: {G(frozenset({0}))}")
