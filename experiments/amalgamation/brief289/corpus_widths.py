"""Room coordinates of the corpora (no search): |L| range, height, largest antichain (Dilworth via bank.width)."""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(HERE, 'separation')); sys.path.insert(0, os.path.join(HERE, 'amalg'))
from tight_probe import lattices
import bank
for spec in [s.split() for s in sys.argv[1].split('+')]:
    ws, ns, hs = [], [], set()
    for L in lattices(spec):
        if L.rank[L.top] < 3: continue
        ws.append(bank.width(L)); ns.append(L.n); hs.add(L.height)
    print(' '.join(spec), f': {len(ns)} lattices, |L| {min(ns)}-{max(ns)}, heights {sorted(hs)}, width {min(ws)}-{max(ws)}')
