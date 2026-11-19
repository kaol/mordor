"""Minimal unsat cores of the local RowCell lemma (log §34.3z²⁰⁸): which hypothesis instances a proof uses.

Fixed lattice L, m of rank 2, w ≱ m, y = m ⊔ w, x an atom with x ≤ w, x ≠ w, x ∥ m.  Hard: F monotone, F(m, y) = w,
F(⊥, w) = x, row x has no interval cell (z > x with F(x,z) ≤ x or z ≤ F(x,z); cells above m are impossible by heights).
Guarded instances: T1b(z) [b(z) = ⊥ ⇒ rank z ≤ 1], Ax(z) [a(x) ≠ z, rank z > 2], Bx(z, g) [b(z) ≠ g ≤ x, rank z > 2],
G(z, g) [y greatest: F(m, z) ≠ g when z ≰ y and z ≤ m ⊔ g].  For each triple whose guarded problem is UNSAT but which is
SAT without guards, print a deletion-minimal core.   python3 core_rowcell.py sweep N MAX [limit=K]
"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
LIM = next((int(a[6:]) for a in sys.argv if a.startswith('limit=')), 30)
args = [a for a in sys.argv[1:] if not a.startswith('limit=')]
shown = 0; C = collections.Counter()
for L in lattices(args):
    n = L.n; le = L.le; jn = L.join; rk = L.rank; bot = rk.index(0)
    nm = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
    for m in range(n):
        if rk[m] != 2: continue
        for w in range(n):
            if le[m][w]: continue
            y = jn[m][w]
            for x in range(n):
                if rk[x] != 1 or not le[x][w] or x == w or le[x][m]: continue
                E = Enc(L, 1); fle, yle, ic = helpers(E, L); f = lambda a, b, v: E.v('f', a, b, v)
                A = lambda a_, g: E.v('A', a_, g); B = lambda y_, g: E.v('B', y_, g)
                E.S.add_clause([f(m, y, w)]); E.S.add_clause([f(bot, w, x)])
                for z in range(n):
                    if le[x][z] and z != x: E.S.add_clause([-fle(x, z, x)]); E.S.add_clause([-yle(x, z)])
                guards = {}
                def guard(tag, clause):
                    s_ = E.v('g', *tag); guards[s_] = tag; E.S.add_clause([-s_] + clause)
                for z in range(n):
                    if rk[z] > 1: guard(('T1b', z), [-B(z, bot)])
                    if rk[z] > 2:
                        guard(('Ax', z), [-A(x, z)])
                        for g in range(n):
                            if le[g][x]: guard(('Bx', z, g), [-B(z, g)])
                    if not le[z][y]:
                        for g in range(n):
                            if le[z][jn[m][g]]: guard(('G', z, g), [-f(m, z, g)])
                if not E.S.solve(): E.S.delete(); continue            # inconsistent without the hypotheses
                core = list(guards)
                if E.S.solve(assumptions=core): C['counterexample'] += 1; E.S.delete(); continue
                core = E.S.get_core() or core
                i = 0
                while i < len(core):                                  # deletion-minimise
                    trial = core[:i] + core[i + 1:]
                    if not E.S.solve(assumptions=trial): core = trial
                    else: i += 1
                tags = sorted(guards[s_] for s_ in core)
                shape = tuple(sorted(collections.Counter(t[0] for t in tags).items()))
                C[('core shape', shape)] += 1
                if shown < LIM and shape != (('T1b', 1),):
                    shown += 1
                    print(f'|L|={n} m={nm(m)} w={nm(w)} y={nm(y)} x={nm(x)} lattice={[nm(i) for i in range(n)]}')
                    for t in tags: print('   ', t[0], *[nm(v) for v in t[1:]])
                E.S.delete()
for k_, v in sorted(C.items(), key=str): print(k_, v)
