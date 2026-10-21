"""Canonical-Ramsey reduction for Cut on M_ω × M_ω × C_n (M_ω: bot, top, atoms).

Let F be monotone and witness-free for a cut D.  By the Erdős–Rado canonical Ramsey theorem (applied jointly
to the finitely many cell patterns, value coordinates and D-memberships) there is an infinite set S of atoms on which:
D-membership depends only on the order pattern; each value coordinate at a cell over M_S is ⊥, ⊤, a fixed atom
outside S, one of the cell's atoms, or a fresh atom g(t) ∉ S determined injectively by an increasing sub-tuple t of
the cell's atoms.  Witness-freeness only compares values with S-atoms, and monotonicity only ever *requires*
equalities between non-S atoms, so all constants may be merged into one atom κ and all fresh generators into one g
(merging only adds equalities).  The canonical problem is finite; UNSAT => every F has a witness: Cut holds.
"""
import itertools, sys
from pysat.solvers import Cadical153
B, T = 'b', 't'

def run(n, Dfun, label, maxk=4):
    # canonical cells: coordinates in {b,t} ∪ atom labels 0..k-1 (contiguous), layers
    def atoms_of(cell):
        return sorted({v for p in cell for v in p[:2] if isinstance(v, int)})
    def canon(cell):
        A = atoms_of(cell); r = {a: i for i, a in enumerate(A)}
        f = lambda v: r[v] if isinstance(v, int) else v
        return tuple((f(p[0]), f(p[1]), p[2]) for p in cell), A   # A: concrete atoms in label order
    vals = [B, T] + list(range(maxk))
    cells = []
    for x1, x2, y1, y2 in itertools.product(vals, repeat=4):
        labs = sorted({v for v in (x1, x2, y1, y2) if isinstance(v, int)})
        if labs != list(range(len(labs))): continue
        for l1 in range(n):
            for l2 in range(n):
                x, y = (x1, x2, l1), (y1, y2, l2)
                if Dfun(x) and not Dfun(y): cells.append((x, y))
    cellset = set(cells)
    def options(cell):
        k = len(atoms_of(cell))
        opts = [B, T, 'k'] + [('a', j) for j in range(k)]
        for r in range(1, k + 1):
            for t in itertools.combinations(range(k), r):
                opts.append(('g', t))
        return opts
    var = {}; cnt = [0]
    def V(*key):
        if key not in var: cnt[0] += 1; var[key] = cnt[0]
        return var[key]
    S = Cadical153()
    for c in cells:
        for coord in (0, 1):
            lits = [V(c, coord, o) for o in options(c)]
            S.add_clause(lits)
            for a, b in itertools.combinations(lits, 2): S.add_clause([-a, -b])
        lits = [V(c, 2, l) for l in range(n)]
        S.add_clause(lits)
        for a, b in itertools.combinations(lits, 2): S.add_clause([-a, -b])
    def sym(o, A):   # option -> concrete symbol given concrete atoms A (label order)
        if o in (B, T, 'k'): return o
        if o[0] == 'a': return ('A', A[o[1]])
        return ('g', tuple(A[i] for i in o[1]))
    cle = lambda u, v: u == v or u == B or v == T
    # no witness
    for c in cells:
        x, y = c
        for coord_val_le_x, name in ((True, 'lx'), (False, 'gy')):
            pass
        Lx = []; Gy = []
        A = list(range(len(atoms_of(c))))
        for coord in (0, 1):
            lx = V(c, 'lx', coord); gy = V(c, 'gy', coord)
            for o in options(c):
                s = sym(o, A)
                # value_coord <= x_coord ?
                xv = x[coord]; yv = y[coord]
                le = (s == B) or (xv == T) or (s == ('A', xv) if isinstance(xv, int) else False) or (s == T and xv == T)
                ge = (yv == B) or (s == T) or (s == ('A', yv) if isinstance(yv, int) else False)
                if le: S.add_clause([-V(c, coord, o), lx])
                else: S.add_clause([-V(c, coord, o), -lx])
                if ge: S.add_clause([-V(c, coord, o), gy])
                else: S.add_clause([-V(c, coord, o), -gy])
            Lx.append(lx); Gy.append(gy)
        for l in range(n):
            if l <= x[2]: S.add_clause([-Lx[0], -Lx[1], -V(c, 2, l)])
            if y[2] <= l: S.add_clause([-Gy[0], -Gy[1], -V(c, 2, l)])
    # monotonicity along covers; concrete atoms of c are 2,4,6,..; new atoms odd
    npairs = 0
    for c in cells:
        x, y = c
        k = len(atoms_of(c))
        conc = lambda v: 2 * v + 2 if isinstance(v, int) else v
        xc = (conc(x[0]), conc(x[1]), x[2]); yc = (conc(y[0]), conc(y[1]), y[2])
        Ac = [2 * i + 2 for i in range(k)]
        newatoms = [2 * i + 2 for i in range(k)] + [2 * i + 1 for i in range(k + 1)]
        def up(p):
            res = []
            for i in (0, 1):
                if p[i] == B:
                    for a in newatoms:
                        q = list(p); q[i] = a; res.append(tuple(q))
                elif p[i] != T:
                    q = list(p); q[i] = T; res.append(tuple(q))
            if p[2] + 1 < n:
                q = list(p); q[2] += 1; res.append(tuple(q))
            return res
        succ = [(x2, yc) for x2 in up(xc) if Dfun(x2)] + [(xc, y2) for y2 in up(yc) if not Dfun(y2)]
        for dconc in succ:
            dcan, Ad = canon(dconc)
            if dcan not in cellset: continue
            npairs += 1
            for coord in (0, 1):
                dopts = options(dcan)
                dsym = {o: sym(o, Ad) for o in dopts}
                for o in options(c):
                    s = sym(o, Ac)
                    if s == B: continue
                    if s == T:
                        S.add_clause([-V(c, coord, o), V(dcan, coord, T)]); continue
                    S.add_clause([-V(c, coord, o), V(dcan, coord, T)] +
                                 [V(dcan, coord, v) for v in dopts if dsym[v] == s])
            for l in range(n):
                for l2 in range(l):
                    S.add_clause([-V(c, 2, l), -V(dcan, 2, l2)])
    r = S.solve()
    print(f"{label}: {'SAT' if r else 'UNSAT -> Cut holds'}  [{len(cells)} canonical cells, {npairs} covers]", flush=True)
    return r, S, var

if __name__ == "__main__":
    plane = lambda p: p[0] != T and p[1] != T
    run(1, plane, "M_ω×M_ω, D = no ⊤ coordinate")
    thick = lambda p: p[0] != T and p[1] != T and (p[2] == 0 or (p[0] == B and p[1] == B))
    run(2, thick, "M_ω×M_ω×C2, D0 = no ⊤, D1 = {⊥}")
