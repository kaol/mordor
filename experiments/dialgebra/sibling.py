"""Local exchange for R(F): which one-step sibling joins carry the join delay (log §34.3z¹¹, Strategy A).

R(F) is the set reachable from ⊥ by finite paths of moves u → v with v ∈ S(u) = ↓u ∪ ↓a(u) ∪ B(u), B(u) = {v : b(v) ≤ u}.
S is monotone in u, so (induction on path length) R is join-closed iff for every w ∈ R the generators
G(w) = {w, a(w)} ∪ Max B(w) have pairwise joins in R.  Pair types: wa, wb, ab, bb.
Sibling delay of a pair at w: s(g ⊔ h) − (s(w) + 1), s = stage of first membership (clipped at 0).
Hill-climb maximises the delay of one type at a time; also reports how often w ≤ a(w) fails on R.

  python3 sibling.py STEPS RESTARTS spec..."""
import sys, os, random, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from amalgam_sample import LT, sampler, analyse

TYPES = ('wa', 'wb', 'ab', 'bb')


def sib(L, F):
    d, a, b, s = analyse(L, F)
    leq, J, n = L.leq, L.join, L.n
    out = {t: 0 for t in TYPES}; notup = 0
    if d is None: return None, out, 0
    for w in s:
        B = [v for v in range(n) if leq[b[v], w]]
        MB = [v for v in B if not any(u != v and leq[v, u] for u in B)]
        notup += not leq[w, a[w]]
        gens = [('w', w), ('a', a[w])] + [('b', v) for v in MB]
        for (t1, g), (t2, h) in itertools.combinations(gens, 2):
            t = ''.join(sorted(t1 + t2, key='wab'.index))
            if t not in out: continue
            z = int(J[g, h]); out[t] = max(out[t], s[z] - (s[w] + 1))
    return d, out, notup


def climb(L, rng, steps, typ):
    n, leq, J, M = L.n, L.leq, L.join, L.meet
    F = sampler(L, rng, 0.3)
    def obj(F):
        d, o, _ = sib(L, F)
        return (99,) if d is None else (o[typ], d)
    best = obj(F); cells = list(itertools.product(range(n), range(n)))
    for _ in range(steps):
        x, y = rng.choice(cells); lo, hi = L.bot, L.top
        for (u, v), w in F.items():
            if (u, v) == (x, y): continue
            if leq[u, x] and leq[v, y]: lo = J[lo, w]
            if leq[x, u] and leq[y, v]: hi = M[hi, w]
        old = F[(x, y)]; F[(x, y)] = rng.choice([z for z in range(n) if leq[lo, z] and leq[z, hi]])
        v = obj(F)
        if v >= best: best = v
        else: F[(x, y)] = old
    return best, dict(F)


if __name__ == '__main__':
    steps, restarts = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(11)
    for spec in sys.argv[3:]:
        Ls = LT.parse(spec); Ls = Ls if isinstance(Ls, list) else [Ls]
        agg = {t: 0 for t in TYPES}; agg_d = 0; nu = 0
        for L in Ls:
            for typ in TYPES:
                for _ in range(restarts):
                    (v, *rest), F = climb(L, rng, steps, typ)
                    if v == 99: print('R NOT JOIN-CLOSED', L.name, F); continue
                    d, o, notup = sib(L, F)
                    agg[typ] = max(agg[typ], o[typ]); agg_d = max(agg_d, d); nu += notup > 0
        print(f"{spec}: {len(Ls)} lattices; max sibling delay by type {agg}; max join delay {agg_d}; "
              f"runs with some w ∈ R, w ≰ a(w): {nu}", flush=True)
