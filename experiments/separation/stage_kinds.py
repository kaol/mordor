"""Which stage-0 separator kinds start a terminating 2-stage RM run at height 3? (log §34.3z¹³⁸)

Kinds: R = the response F(x, y), M = a maximal separator (RM = both), suffix d / u = in D / outside D. For each
height-3 hard witness (respmax_hard_witnesses_*.json) and 199 mutations, the set of stage-0 kinds that begin a
terminating response-or-maximal run of at most 2 stages.
  python3 stage_kinds.py respmax_hard_witnesses_*.json
"""
import sys, json, itertools, collections, random
import separator_stages as ss, exist_cegar as ec
ec.RESPMAX = True
def kind(L, F, D, x, y, s):
    r = 'R' if s == F[x][y] else ''
    m = 'M' if ec.static_maxsep(L, s, y) else ''
    return (r + m) + ('d' if D[s] else 'u')
def two_stage(L, F, D):
    T0 = ss.mclose(L, {L.bot, L.top}); out = []
    b0 = ss.bad_pairs(L, F, D, T0)
    if not b0 or any(L.le[y][F[x][y]] for x, y in b0): return None
    (x0, y0), = b0
    for s0 in ec.seps(L, F, x0, y0):
        T1 = ss.mclose(L, set(T0) | {s0}); b1 = ss.bad_pairs(L, F, D, T1)
        k0 = kind(L, F, D, x0, y0, s0)
        if not b1 or any(L.le[y][F[x][y]] for x, y in b1): out.append((k0,)); continue
        for ch in itertools.product(*[ec.seps(L, F, x, y) for x, y in b1]):
            T2 = ss.mclose(L, set(T1) | set(ch)); b2 = ss.bad_pairs(L, F, D, T2)
            if not b2 or any(L.le[y][F[x][y]] for x, y in b2):
                out.append((k0, tuple(sorted(kind(L, F, D, x, y, s) for (x, y), s in zip(b1, ch)))))
    return out
tally = collections.Counter(); rng = random.Random(1); tot = 0
ws = [w for f in sys.argv[1:] for w in json.load(open(f))]
for w in ws:
    L = ss.Lat(w['sets'])
    if L.height != 3: continue
    F, D = w['F'], w['D']
    for rep in range(200):
        if rep:
            g = {(a, b): F[a][b] for a in range(L.n) for b in range(L.n)}
            for _ in range(rng.randint(1, 3)):
                a, b = rng.randrange(L.n), rng.randrange(L.n); g[(a, b)] = rng.randrange(L.n) if rng.random() < .5 else 0
            F2 = ss.make_F(L, g)
        else: F2 = F
        r = two_stage(L, F2, D)
        if r is None: continue
        tot += 1
        firsts = set(t[0] for t in r)
        tally[('stage-0 kinds that work', tuple(sorted(firsts)))] += 1
print('instances', tot)
for k, v in tally.most_common(): print(v, k)
