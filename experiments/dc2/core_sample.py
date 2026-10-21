"""Sample minimal level-0 closure cores (randomized deletion order) for one thick pattern, at k = 0 and at k ≥ 1,
then report the union of one core from each with the smallest width."""
import sys, random, itertools
import dc2_lazy as d, dc2_eager as e, plane_full as P
from narrow import pat_of
from thick_patterns import width
B, T = d.B, d.T
fmt = lambda c: f"{''.join('⊥' if t == B else '⊤' for t in c[0][:2])}{c[0][2]},{''.join('⊥' if t == B else '⊤' for t in c[1][:2])}{c[1][2]}"
tag = sys.argv[1]; N = int(sys.argv[2]) if len(sys.argv) > 2 else 15
d.CLOSED1 = P.fibre; d.SEL0 = True; d.DPAT = pat_of(tag)
if len(sys.argv) > 3:
    import pattern_full as PF
    Z = set(PF.parse_cell(c) for c in sys.argv[3].split(';')); d.ZERO0 = lambda x, y: (x, y) in Z
pools = {}
for k, m in ((0, 0), (1, 2), (2, 2)):
    cs = set()
    for s in range(N):
        d.SHUFFLE = random.Random(s)
        cs.add(frozenset(e.run(k, m, 2, verbose=False)))
    pools[(k, m)] = cs
    print((k, m), len(cs), 'distinct cores', sorted(len(c) for c in cs), flush=True)
best = None
for combo in itertools.product(*pools.values()):
    u = frozenset().union(*combo)
    w = width(sorted(u, key=str))
    if best is None or (w, len(u)) < best[0]: best = ((w, len(u)), u)
print('best union width', best[0][0], 'cells', best[0][1])
print(';'.join(fmt(c) for c in sorted(best[1], key=str)))
