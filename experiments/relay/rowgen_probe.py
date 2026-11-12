"""Witness localization in the row-generated closure (log §34.3z¹⁴⁸).

Finite shadow of the brief's `star_forest_row_generated_cell`: on a finite lattice L with a star-forest cut D,
does every monotone F have a witness (x ∈ D, y ∉ D, F(x, y) ≤ x or y ≤ F(x, y)) whose column y lies in the closure W
of {⊤} under y ↦ F(r, y) for the rows r in R?   R = 'blocks': ⊥ and the blocks of D (the brief's W);
R = 'D': every row of D.  SAT search for a counterexample: F monotone, D a star forest of height ≤ 2, a set W'
containing ⊤ and closed under the rows (any closed superset of the least W), and witness-freeness at every column of
W' ∖ D. A model refutes localization on that lattice (the least W ⊆ W' carries no witness either). Every model is
re-checked against the least closure computed in Python. Also reported: whether D is a single star (a bouquet).
Option 'anycut': D any proper down-set.
  python3 rowgen_probe.py [anycut] (blocks | D) (sweep P NMAX | closure K M SEED COUNT)
"""
import sys, itertools, random, collections, json
from pysat.solvers import Cadical153
sys.path.insert(0, '../separation'); sys.path.insert(0, '../amalgamation')
import separator_stages as ss
from relay_probe import Enc, lattices

ANYCUT = False   # 'anycut': D any proper down-set (no rank or star-forest condition)

def build(L, mode):
    E = Enc(L); n = L.n; le = L.le; bot, top = L.bot, L.top; rk = L.rank
    f = lambda x, y, v: E.v('f', x, y, v); d = lambda e: E.v('d', e); W = lambda e: E.v('W', e)
    for x in range(n):
        for y in range(n):
            lits = [f(x, y, v) for v in range(n)]; E.cl(lits)
            for p, q in itertools.combinations(lits, 2): E.cl([-p, -q])
    for x in range(n):
        for x2 in L.covers_up[x]:
            for y in range(n):
                for v in range(n): E.cl([-f(x, y, v)] + [f(x2, y, w) for w in range(n) if le[v][w]])
    for y in range(n):
        for y2 in L.covers_up[y]:
            for x in range(n):
                for v in range(n): E.cl([-f(x, y, v)] + [f(x, y2, w) for w in range(n) if le[v][w]])
    E.cl([d(bot)]); E.cl([-d(top)])
    for e in range(n):
        for c in L.covers_up[e]: E.cl([-d(c), d(e)])
        if rk[e] > 2 and not ANYCUT: E.cl([-d(e)])
    blk = lambda e: E.v('blk', e)
    for e in range(n): E.iff_and(blk(e), [d(e)] + [-d(g) for g in range(n) if g != e and le[e][g]])
    atoms = [e for e in range(n) if rk[e] == 1]
    for m in (range(n) if not ANYCUT else []):              # star forest
        for p, q in itertools.combinations([t for t in atoms if le[t][m]], 2):
            for n1 in range(n):
                if n1 == m or not le[p][n1]: continue
                for n2 in range(n):
                    if n2 == m or not le[q][n2]: continue
                    E.cl([-blk(m), -blk(n1), -blk(n2)])
    E.cl([W(top)])
    for r in range(n):                                      # closure under the rows
        row = ([] if r == bot else [-blk(r)]) if mode == 'blocks' else ([] if r == bot else [-d(r)])
        for y in range(n):
            for e in range(n): E.cl(row + [-W(y), -f(r, y, e), W(e)])
    for y in range(n):                                      # witness-freeness on W ∖ D
        for x in range(n):
            for e in range(n):
                if le[e][x] or le[y][e]: E.cl([-W(y), d(y), -d(x), -f(x, y, e)])
    return E

def least_W(L, F, D, mode):
    rows = [r for r in range(L.n) if r == L.bot or (D[r] and (mode == 'D' or not any(D[g] and g != r and L.le[r][g] for g in range(L.n))))]
    W = {L.top}; st = [L.top]
    while st:
        y = st.pop()
        for r in rows:
            e = F[r][y]
            if e not in W: W.add(e); st.append(e)
    return W

if __name__ == '__main__':
    if 'anycut' in sys.argv: sys.argv.remove('anycut'); ANYCUT = True
    mode = sys.argv[1]; T = collections.Counter(); best = None
    for L in lattices(sys.argv[2:]):
        if L.height < 2: continue
        E = build(L, mode)
        if E.S.solve():
            m = set(x for x in E.S.get_model() if x > 0); n = L.n
            F = [[next(v for v in range(n) if E.vars[('f', x, y, v)] in m) for y in range(n)] for x in range(n)]
            D = [E.vars[('d', e)] in m for e in range(n)]
            W = least_W(L, F, D, mode)
            assert not any(D[x] and not D[y] and (L.le[F[x][y]][x] or L.le[y][F[x][y]]) for x in range(n) for y in W)
            blocks = [e for e in range(n) if D[e] and not any(D[g] and g != e and L.le[e][g] for g in range(n))]
            pts = [e for e in range(n) if L.rank[e] == 1 and D[e]]
            shared = [p for p in pts if sum(L.le[p][m] for m in blocks) >= 2]
            T[('SAT', 'stars with ≥2 blocks', len(shared))] += 1
            if best is None or n < best[0].n: best = (L, F, D, W)
        else: T['UNSAT'] += 1
        E.S.delete()
    print(f"rows {mode}{' (any cut)' if ANYCUT else ' (star forests)'}: {dict(sorted(T.items(), key=str))}", flush=True)
    if best:
        L, F, D, W = best; w_ = max(x.bit_length() for x in L.S)
        nm = lambda i: '{' + ''.join(str(j) for j in range(w_) if L.S[i] >> j & 1) + '}'
        print(f"smallest: |L| = {L.n}, height {L.height}, D = {[nm(i) for i in range(L.n) if D[i]]}, least W = {sorted(nm(i) for i in W)}", flush=True)
        json.dump(dict(sets=L.S, F=F, D=D), open(f"rowgen_{mode}_min{L.n}.json", 'w'))
