"""Regression check of the brief's M3 example (log §34.3z⁶²): F(x, y) = 0 for y < 1 and c for y = 1 on M3 = {0, p, q, c, 1}.
Checks monotonicity, computes a (gfp of rows) and b (lfp of columns), Z = b⁻¹(0), and that b⁻¹(Z) ≠ Z; also that the
cut Z has a witness (finite lattices always do)."""
E = ['0', 'p', 'q', 'c', '1']
le = lambda x, y: x == y or x == '0' or y == '1'
F = lambda x, y: 'c' if y == '1' else '0'
assert all(le(F(x, y), F(x2, y2)) for x in E for y in E for x2 in E for y2 in E if le(x, x2) and le(y, y2))
def lfp(f):
    x = '0'
    while f(x) != x: x = f(x)
    return x
def gfp(f):
    x = '1'
    while f(x) != x: x = f(x)
    return x
a = {x: gfp(lambda t: F(x, t)) for x in E}
b = {y: lfp(lambda t: F(t, y)) for y in E}
Z = {y for y in E if b[y] == '0'}
print("a =", a); print("b =", b); print("Z =", sorted(Z))
print("p, q in Z, p ∨ q = 1 in Z:", '1' in Z)
print("b⁻¹(Z) == Z:", {y for y in E if b[y] in Z} == Z, "(b(1) =", b['1'], ")")
print("witnesses of the cut Z:", [(x, y) for x in Z for y in set(E) - Z if le(F(x, y), x) or le(y, F(x, y))])
