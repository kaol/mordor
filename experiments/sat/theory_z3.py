"""Usage: python3 theory_z3.py H poset|lat TIMEOUT_MS [nocomm] [chain]
# T_H: universal first-order theory of "polar realizable commuting pair on a bounded poset/lattice of height <= h".
# Unsat  => CL on ALL (incl. infinite) lattices of height <= h (realizability criterion holds on complete lattices;
#           finite-height lattices are complete; intervals have height <= H).
"""
import sys
from z3 import *
H = int(sys.argv[1]); lattice = sys.argv[2] == "lat"; tmo = int(sys.argv[3]); opts = sys.argv[4:] if len(sys.argv) > 4 else []
h = H + 1  # forbid chains of H+2 elements: edge-height <= H
P = DeclareSort('P'); le = Function('le', P, P, BoolSort())
F = Function('F', P, P, P); a = Function('a', P, P); b = Function('b', P, P)
bot, top = Consts('bot top', P)
x, y, z, x2, y2 = Consts('x y z x2 y2', P)
lt = lambda p, q: And(le(p, q), p != q)
ax = [ForAll([x], le(x, x)), ForAll([x, y], Implies(And(le(x, y), le(y, x)), x == y)),
      ForAll([x, y, z], Implies(And(le(x, y), le(y, z)), le(x, z))),
      ForAll([x], And(le(bot, x), le(x, top))), bot != top,
      ForAll([x, x2, y], Implies(le(x, x2), And(le(F(x, y), F(x2, y)), le(F(y, x), F(y, x2))))),
      ForAll([x], F(x, a(x)) == a(x)), ForAll([y], F(b(y), y) == b(y)),
      ForAll([x, y], Implies(Not(le(y, a(x))), F(x, y) != y)),
      ForAll([x, y], Implies(Not(le(b(y), x)), F(x, y) != x)),
      a(bot) == bot, b(bot) == bot, a(top) == top, b(top) == top]
if 'nocomm' not in opts: ax.append(ForAll([x], a(b(x)) == b(a(x))))
if 'chain' in opts: ax.append(ForAll([x, y], Or(le(x, y), le(y, x))))
xs = Consts(' '.join(f'c{i}' for i in range(h+1)), P)
ax.append(ForAll(list(xs), Not(And([lt(xs[i], xs[i+1]) for i in range(h)]))))
if lattice:
    j = Function('j', P, P, P); m = Function('m', P, P, P)
    ax += [ForAll([x, y], And(le(x, j(x, y)), le(y, j(x, y)))),
           ForAll([x, y, z], Implies(And(le(x, z), le(y, z)), le(j(x, y), z))),
           ForAll([x, y], And(le(m(x, y), x), le(m(x, y), y))),
           ForAll([x, y, z], Implies(And(le(z, x), le(z, y)), le(z, m(x, y))))]
s = Solver(); s.set("timeout", tmo); s.add(ax)
r = s.check(); print(f"edge-height<={H} {opts} ({'lattice' if lattice else 'poset'}): {r}", s.reason_unknown() if r == unknown else "")
if r == sat:
    M = s.model(); print("model size", len(M.get_universe(P)))
