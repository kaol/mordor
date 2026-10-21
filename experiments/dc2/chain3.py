"""Width-3 closed level-0 sets (unions of three maximal chains) for the hard thick patterns."""
import itertools, sys
import dc2_lazy as d, plane_full as P
from chain_search import test, maximal_chains
from thick_patterns import width
from narrow import pat_of
B, T = d.B, d.T
fmt = lambda c: f"{''.join('⊥' if t == B else '⊤' for t in c[0][:2])}{c[0][2]},{''.join('⊥' if t == B else '⊤' for t in c[1][:2])}{c[1][2]}"
d.CLOSED1 = P.fibre
for tag in sys.argv[1:]:
    pat = pat_of(tag); d.DPAT = pat
    Dset = {p for p, v in pat.items() if v}
    cells = [(x, y) for x in pat for y in pat if x in Dset and y not in Dset]
    chains = maximal_chains(cells)
    found = None
    for trip in itertools.combinations(chains, 3):
        cs = set().union(*map(set, trip))
        if width(sorted(cs, key=str)) <= 3 and test(cs, [(1, 2), (2, 2)]): found = sorted(cs, key=str); break
    print(tag, 'none' if not found else f"width 3, {len(found)} cells: " + ';'.join(fmt(c) for c in found), flush=True)
