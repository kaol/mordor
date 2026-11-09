"""Selection rules for the residue (log §34.3z¹⁴¹).

At tight stages with no diagonal top element, does the interval cell IC(m) hold at the top element chosen by:
  'latest'   : largest entry stage st(m);   'earliest': smallest entry stage;
  'hi b(m)'  : largest height of b(m);      'lo b(m)' : smallest height of b(m);
  'some'     : any top element (the exact statement TightIC)?
Ties: the rule succeeds if IC holds at every tied element ('all-tied') / at some tied element ('some-tied').
  python3 residue_select.py SEED SECONDS
"""
import sys, random, time, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, b_of

def ic(L, F, m):
    return any(y != m and L.le[m][y] and (L.le[F[m][y]][m] or L.le[y][F[m][y]]) for y in range(L.n))

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter()
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 2 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F); B = [b_of(L, F, y) for y in range(L.n)]
        for k in range(st[L.top] - 1):
            R = [z for z in range(L.n) if st[z] <= k]
            if max(L.rank[z] for z in R) != k: continue
            M = [z for z in R if L.rank[z] == k]
            if any(L.le[m][F[m][m]] for m in M): continue
            T['residue stages'] += 1
            for nm, key in (('latest', lambda m: -st[m]), ('earliest', lambda m: st[m]),
                            ('hi b(m)', lambda m: -L.rank[B[m]]), ('lo b(m)', lambda m: L.rank[B[m]])):
                best = min(key(m) for m in M); tied = [m for m in M if key(m) == best]
                T[(nm, 'all-tied', all(ic(L, F, m) for m in tied))] += 1
                T[(nm, 'some-tied', any(ic(L, F, m) for m in tied))] += 1
            T[('some', any(ic(L, F, m) for m in M))] += 1
    print(dict(sorted(T.items(), key=str)), flush=True)
