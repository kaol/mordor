"""Exact maximum length of a *forced* term-d run on a fixed lattice (log §34.3z¹³⁴).

TermEnc (term_sat.py, meets on) plus: at every non-goal stage every bad pair has exactly one C-maximal separator.
A forced run is followed by every selection policy that adds, per bad pair, a nonempty set of C-maximal separators
(all, one, lookahead, potentials, random), so these maxima are lower bounds for the maximum of every such policy.
Every model is decoded and re-checked with forced_check.forced.
  python3 forced_sat.py (pencil K | linear K SEED COUNT) [depth=D]
"""
import sys, time, random, itertools
import separator_stages as ss
from term_sat import TermEnc, decode, lat_of
from forced_check import forced

class ForcedEnc(TermEnc):
    def select(self, m, x, y, mxd):
        b = self.v('b', m, x, y)
        for s, s2 in itertools.combinations(mxd, 2): self.cl([-b, -mxd[s], -mxd[s2]])
        return mxd

def max_length(L, kmax=14, budget=None, depth=1):
    t0 = time.time(); best = 0
    for k in range(1, kmax + 1):
        E = ForcedEnc(L, k, depth, True); r = E.S.solve()
        if r:
            F, D = decode(E); n, w = forced(L, F, D, depth)
            assert n >= k and all(v == 1 for v in w[:k]), f"model does not reproduce ({n}, {w})"
        E.S.delete()
        if not r: return best, round(time.time() - t0, 1)
        best = k
        if budget and time.time() - t0 > budget: return best, None
    return best, None

if __name__ == '__main__':
    args = sys.argv[1:]; DEP = 1
    if args[-1].startswith('depth='): DEP = int(args.pop().removeprefix('depth='))
    if args[0] == 'pencil':
        import pencil_family
        L = pencil_family.family(int(args[1]))[0]
        print(f"near-pencil on {args[1]} points: |L| = {L.n}, max forced term{DEP} run (k, s) = "
              f"{max_length(L, budget=500, depth=DEP)}", flush=True)
    else:
        from finite_landmarks import linear_space
        k = int(args[1]); rng = random.Random(int(args[2]))
        for _ in range(int(args[3])):
            L = lat_of(linear_space(k, rng), k)
            if L.height != 3: continue
            print(f"linear space on {k} points: |L| = {L.n}, max forced term{DEP} run (k, s) = "
                  f"{max_length(L, budget=500, depth=DEP)}", flush=True)
