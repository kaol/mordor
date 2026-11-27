# bank.py replay predicate (W0 + n1 models only, as bank.py restricts): LfpMin's W0 consequence.
# In W0 (Tb at every row of Z) no high column has its least pre-fixed point in Z; LfpMin's hypothesis NoFix has no W0 model,
# so on the bank LfpMin itself is 'outside hypothesis' everywhere. holds(m): no high y with b(y) in Z (A6), and CertAtom.
from rstages import a_of
def b_of(m, y):
    v = m.bot
    while m.F[v][y] != v: v = m.F[v][y]
    return v
def hyp(m): return True
def holds(m):
    hi = [y for y in range(m.n) if m.h[y] >= 3]
    return all(b_of(m, y) not in m.Z for y in hi) and any(m.fixed(q) for q in m.atoms)
