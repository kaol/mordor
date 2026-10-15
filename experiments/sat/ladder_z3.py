# Sharpness Theorem's Ladder Construction (§22.3), verified over ALL complete chains with a limit point,
# via the realizability criterion (valid on complete lattices: Tarski gives row/column fixed points).
from z3 import *
C = DeclareSort('C'); le = Function('le', C, C, BoolSort())
bot, top, lam = Consts('bot top lam', C); s = Function('s', C, C)
x, y, z, x2, y2 = Consts('x y z x2 y2', C)
lt = lambda p, q: And(le(p, q), p != q)
def axioms(escape=True):
    ax = [ForAll([x], le(x, x)), ForAll([x, y], Implies(And(le(x, y), le(y, x)), x == y)),
          ForAll([x, y, z], Implies(And(le(x, y), le(y, z)), le(x, z))), ForAll([x, y], Or(le(x, y), le(y, x))),
          ForAll([x], And(le(bot, x), le(x, top))), lt(bot, lam),
          ForAll([x, y], Implies(And(lt(x, lam), lt(y, lam), le(x, y)), le(s(x), s(y)))),
          ForAll([x], Implies(lt(x, lam), And(lt(x, s(x)), le(s(x), lam))))]
    if escape: ax.append(ForAll([x], Implies(lt(x, lam), lt(s(x), lam))))   # the ladder: s(x) < lam
    return ax
mx = lambda p, q: If(le(p, q), q, p)
def F(p, q): return If(lt(q, lam), p, If(lt(p, lam), s(p), mx(p, q)))
a = lambda p: If(lt(p, lam), p, top)
b = lambda q: If(lt(q, lam), bot, q)
props = {
 "F monotone in x": Implies(le(x, x2), le(F(x, y), F(x2, y))),
 "F monotone in y": Implies(le(y, y2), le(F(x, y), F(x, y2))),
 "pin F(x,a x)=a x": F(x, a(x)) == a(x),
 "pin F(b y,y)=b y": F(b(y), y) == b(y),
 "excl y!<=a x => F(x,y)!=y": Implies(Not(le(y, a(x))), F(x, y) != y),
 "excl b y!<=x => F(x,y)!=x": Implies(Not(le(b(y), x)), F(x, y) != x),
 "commute a(b x)=b(a x)": a(b(x)) == b(a(x)),
 "polar": And(a(bot) == bot, a(top) == top, b(bot) == bot, b(top) == top),
 "m!=n (bot!=top)": bot != top,
}
for esc in (True, False):
    print("ladder axiom s(x)<lam:", esc)
    for k, p in props.items():
        sv = Solver(); sv.set("timeout", 60000); sv.add(axioms(esc)); sv.add(Not(p))
        r = sv.check(); print(f"   {k:28s} {'PROVED' if r == unsat else r}")
# the ladder forces infinitude: no model with <= N elements
for N in (2, 5):
    els = Consts(' '.join(f'e{i}' for i in range(N)), C)
    sv = Solver(); sv.add(axioms(True)); sv.add(ForAll([x], Or([x == e for e in els])))
    print(f"ladder axioms with <= {N} elements:", sv.check())
