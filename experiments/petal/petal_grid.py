"""The growing-root petal grid as a finite order-constraint model (log §34.3z⁶⁴), z3.

Elements (a preorder; values may coincide): ⊥, ⊤; base row r and base column s; petal meets p_i (in D) and joins u_j
(outside D); rows r_i = r ⊓ p_i and columns s_j = s ⊔ u_j as glb/lub among the model's elements; values
z(x, y) = F(x, y) for every row x ∈ {r, r_0..r_{n-1}} and column y ∈ {s, s_0..s_{n-1}}; capturers c_i (maximal in D,
pairwise incomparable) of the D-valued diagonal pivots z(r_i, s_i), and d_i (minimal outside D) of the others.
Constraints: D a down-set; F monotone on all pairs of named cells (conditional on the model's order); no-witness at
every cell (z ≰ row, col ≰ z); fresh capture (z_ii ≤ c_i, d_i ≤ z_ii); triangular non-capture from the accumulation
process (i < j: z_jj ≰ c_i, d_i ≰ z_jj, and the new capturer is not an earlier one).
For every homogeneous side pattern (sides of the boundary corners z(r_i, s), z(r, s_j), of the diagonal, of the
upper and of the lower off-diagonal cells) it reports SAT (the pattern survives every local constraint) or UNSAT.
Option `inherit`: every earlier capturer is in every later row support (m_{A_j} ≤ c_i, i < j), with the extra cells
F(c_i, s_j). `captured`/parity is NOT encoded (it is global); rect_* and capturer_*_escapes are consequences of the encoding."""
import itertools, sys
from z3 import *
n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
INHERIT = 'inherit' in sys.argv     # the inherited-capturer case: m_{A_j} ≤ c_i for i < j, with the cells F(c_i, s_j)
rows = ['r'] + [f"r{i}" for i in range(n)]; cols = ['s'] + [f"s{j}" for j in range(n)]
Z = {(x, y): f"z_{x}_{y}" for x in rows for y in cols}
if INHERIT: Z.update({(f"c{i}", f"s{j}"): f"w_{i}_{j}" for i in range(n) for j in range(n) if i < j})
E = ['bot', 'top', 'r', 's'] + [f"p{i}" for i in range(n)] + [f"u{j}" for j in range(n)] + rows[1:] + cols[1:] \
    + list(Z.values()) + [f"c{i}" for i in range(n)] + [f"d{i}" for i in range(n)]
le = {(a, b): Bool(f"le_{a}_{b}") for a in E for b in E}
inD = {a: Bool(f"D_{a}") for a in E}
lt = lambda a, b: And(le[a, b], Not(le[b, a]))
base = [inD['bot'], Not(inD['top']), inD['r'], Not(inD['s'])]
for a in E:
    base += [le[a, a], le['bot', a], le[a, 'top']]
    for b in E:
        base.append(Implies(And(le[a, b], inD[b]), inD[a]))
        for c in E: base.append(Implies(And(le[a, b], le[b, c]), le[a, c]))
for i in range(n):
    base += [inD[f"p{i}"], Not(inD[f"u{i}"])]
    ri, si = f"r{i}", f"s{i}"
    base += [le[ri, 'r'], le[ri, f"p{i}"]] + [Implies(And(le[w, 'r'], le[w, f"p{i}"]), le[w, ri]) for w in E]
    base += [le['s', si], le[f"u{i}", si]] + [Implies(And(le['s', w], le[f"u{i}", w]), le[si, w]) for w in E]
for (x, y), z in Z.items():
    base += [Not(le[z, x]), Not(le[y, z])]
    for (x2, y2), z2 in Z.items():
        if (x, y) != (x2, y2): base.append(Implies(And(le[x, x2], le[y, y2]), le[z, z2]))
if INHERIT:
    base += [le[f"r{j}", f"c{i}"] for i in range(n) for j in range(n) if i < j]
piv = [Z[f"r{i}", f"s{i}"] for i in range(n)]
for i in range(n):
    c, d = f"c{i}", f"d{i}"
    base += [inD[c], Not(inD[d])] + [Implies(lt(c, w), Not(inD[w])) for w in E] + [Implies(lt(w, d), inD[w]) for w in E]
    base += [Implies(inD[piv[i]], le[piv[i], c]), Implies(Not(inD[piv[i]]), le[d, piv[i]])]
    for j in range(i + 1, n):
        base += [Implies(And(inD[piv[i]], inD[piv[j]]), And(Not(le[piv[j], f"c{i}"]), Not(le[f"c{i}", f"c{j}"]), Not(le[f"c{j}", f"c{i}"]))),
                 Implies(And(Not(inD[piv[i]]), Not(inD[piv[j]])), And(Not(le[f"d{i}", piv[j]]), Not(le[f"d{i}", f"d{j}"]), Not(le[f"d{j}", f"d{i}"])))]
s = Solver(); s.add(base)
print(f"n = {n} petals per side{', inherited capturers' if INHERIT else ''}; base model:", s.check())
names = ['corner rows z(r_i,s)', 'corner cols z(r,s_j)', 'diagonal', 'upper z(r_i,s_j) i<j', 'lower i>j']
groups = [[Z[f"r{i}", 's'] for i in range(n)], [Z['r', f"s{j}"] for j in range(n)], piv,
          [Z[f"r{i}", f"s{j}"] for i in range(n) for j in range(n) if i < j],
          [Z[f"r{i}", f"s{j}"] for i in range(n) for j in range(n) if i > j]]
surv = []
for pat in itertools.product((True, False), repeat=5):
    s.push(); s.add([inD[z] == t for g, t in zip(groups, pat) for z in g]); r = s.check(); s.pop()
    tag = ' '.join(f"{nm}:{'D' if t else 'U'}" for nm, t in zip(names, pat))
    if r == sat: surv.append(tag)
    print(f"  {'SAT  ' if r == sat else 'UNSAT'} {tag}", flush=True)
print(f"{len(surv)} of 32 homogeneous patterns survive every local constraint")
