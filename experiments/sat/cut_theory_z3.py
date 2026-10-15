"""Usage: python3 cut_theory_z3.py H TIMEOUT_MS [chain] [poset]
The universal theory C_H: a lattice with no chain of H+2 elements, a down-set D with bot in D and top not in D,
monotone F, and for all x in D, y not in D: F(x,y) not<= x and F(x,y) not>= y.
Unsat  =>  the Cut Lemma, hence semi-CL and CL, on ALL lattices of edge-height <= H (infinite ones included)."""
import sys
from z3 import *
H = int(sys.argv[1]); tmo = int(sys.argv[2]); opts = sys.argv[3:]
P = DeclareSort('P'); le = Function('le', P, P, BoolSort()); Dp = Function('D', P, BoolSort())
F = Function('F', P, P, P); j = Function('j', P, P, P); m = Function('m', P, P, P)
bot, top = Consts('bot top', P); x, y, z, x2, y2 = Consts('x y z x2 y2', P)
lt = lambda p, q: And(le(p, q), p != q)
ax = [ForAll([x], le(x, x)), ForAll([x, y], Implies(And(le(x, y), le(y, x)), x == y)),
      ForAll([x, y, z], Implies(And(le(x, y), le(y, z)), le(x, z))), ForAll([x], And(le(bot, x), le(x, top))),
      ForAll([x, x2, y], Implies(le(x, x2), And(le(F(x, y), F(x2, y)), le(F(y, x), F(y, x2))))),
      ForAll([x, y], Implies(And(Dp(y), le(x, y)), Dp(x))), Dp(bot), Not(Dp(top)),
      ForAll([x, y], Implies(And(Dp(x), Not(Dp(y))), And(Not(le(F(x, y), x)), Not(le(y, F(x, y))))))]
if "poset" not in opts:
    ax += [ForAll([x, y], And(le(x, j(x, y)), le(y, j(x, y)))), ForAll([x, y, z], Implies(And(le(x, z), le(y, z)), le(j(x, y), z))),
           ForAll([x, y], And(le(m(x, y), x), le(m(x, y), y))), ForAll([x, y, z], Implies(And(le(z, x), le(z, y)), le(z, m(x, y))))]
if "chain" in opts: ax.append(ForAll([x, y], Or(le(x, y), le(y, x))))
cs = Consts(' '.join(f'c{i}' for i in range(H + 2)), P)
ax.append(ForAll(list(cs), Not(And([lt(cs[i], cs[i+1]) for i in range(H + 1)]))))
s = Solver(); s.set("timeout", tmo); s.add(ax); r = s.check()
print(f"C_{H} {opts}: {r}", s.reason_unknown() if r == unknown else "")
if r == sat: print("  model size", len(s.model().get_universe(P)))
