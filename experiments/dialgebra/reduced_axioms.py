"""Reduced axiom systems for the Cut Lemma (external proposal, log §34.3l).

For all pairs (a, b) of monotone self-maps on small lattices: does R(a, b) (the least down-set ∋ ⊥ closed under a
and b⁻¹) fail join-closure, under which map-level laws? Laws tested (all universally quantified):
  cross   y ≤ a z ∧ b y ≤ z ⟹ b y ≤ a z       (holds for every bifunction-derived pair, Source.cross)
  semi    b a ≤ a b
  stab    m = μa is b-fixed and n = νb is a-fixed (L1, L2)
  derived (a, b) arises from some monotone F (realizability CSP, brute force over F on tiny lattices)

  python3 reduced_axioms.py"""
import itertools, sys, collections, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import laws as Lw
from amalgam import stages


def mons(L):
    R = range(L.n)
    return [t for t in itertools.product(R, repeat=L.n) if all(L.le[t[i]][t[j]] for i in R for j in R if L.le[i][j])]


def run(L):
    R, le, J = range(L.n), L.le, L.join
    M = mons(L); cnt = collections.Counter()
    for a in M:
        for b in M:
            s = stages(L, a, b)
            closed = all(J[x][y] in s for x in s for y in s)
            cross = all(le[b[y]][a[z]] for y in R for z in R if le[y][a[z]] and le[b[y]][z])
            semi = all(le[b[a[x]]][a[b[x]]] for x in R)
            m = L.lfp(lambda x: a[x]); n = L.gfp(lambda y: b[y])
            stab = b[m] == m and a[n] == n
            for name, cond in (('all', True), ('cross', cross), ('cross+stab', cross and stab),
                               ('cross+stab+semi', cross and stab and semi), ('semi', semi)):
                if cond: cnt[(name, closed)] += 1
    print(f"{L.name}: {len(M)} monotone maps, {len(M)**2} pairs")
    for name in ('all', 'cross', 'cross+stab', 'semi', 'cross+stab+semi'):
        print(f"   {name:16s} pairs {cnt[(name, True)] + cnt[(name, False)]:7d}   R not join-closed: {cnt[(name, False)]}")
    sys.stdout.flush()


if __name__ == '__main__':
    for L in [Lw.B2, Lw.N5, Lw.M3, Lw.chain(5)]: run(L)
