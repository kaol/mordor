"""Does the N = 5 whole-chain core generalize as base + uniform step + top?  Witness clauses only at pattern cells."""
import sys
from omega_window import *
N2 = ('nb', 2)
NREF = int(sys.argv[1]) if len(sys.argv) > 1 else 5
WIN = 1   # positions within WIN of an end are anchored to that end

def cfg(N): return ((G1,), (G2,) + (N2,) * (N - 1))

def chainpos(cell):
    return [t[1] for p in cell for t in p[:-1] if t not in ('b', 't') and t[0] == 1]

def relform(cell, N):
    ps = chainpos(cell)
    if not ps: return ('base', cell)
    lo, hi = min(ps), max(ps)
    if lo <= WIN: mode, ref = 'bot', 0
    elif hi >= N - 1 - WIN: mode, ref = 'top', N - 1
    else: mode, ref = 'mid', hi
    f = lambda t: t if t in ('b', 't') or t[0] != 1 else ('C', t[1] - ref)
    x, y = cell
    return (mode, (tuple(f(t) for t in x[:-1]) + (x[-1],), tuple(f(t) for t in y[:-1]) + (y[-1],)))

core = run(cfg(NREF), core=True)
pats = set(relform(c, NREF) for c in core)
print(f"N={NREF} core {len(core)} cells -> {len(pats)} patterns "
      f"(base {sum(1 for p in pats if p[0]=='base')}, bot {sum(1 for p in pats if p[0]=='bot')}, "
      f"mid {sum(1 for p in pats if p[0]=='mid')}, top {sum(1 for p in pats if p[0]=='top')})", flush=True)
SPAN = int(sys.argv[2]) if len(sys.argv) > 2 else None
for N in range(2, 10):
    sel = lambda x, y, N=N: relform((x, y), N) in pats
    run(cfg(N), witsel=sel, span=SPAN, label=f"pattern-only span={SPAN} N={N}")
for N in range(2, 10):
    run(cfg(N), span=SPAN, label=f"all witness, span={SPAN} N={N}")
