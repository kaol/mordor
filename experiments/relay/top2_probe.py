"""Two top escapes (log §34.3z¹⁵¹).

Lean `Clipped.top_escape`: at a maximal proper non-member c (necessarily a coatom) every clipped escape (x, y),
x ∈ D, y ∉ D, x, y ≤ c, F(x, y) ⊓ c ≤ x, F(x, y) ≰ c, has c ⊔ F(x, y) = ⊤. Question: do top escapes at two distinct
coatoms c, c' ∉ D force a cell at a combined column? SAT search on a fixed lattice: F monotone, D a down-set
(option 'forest': a star forest of height ≤ 2), coatoms c ≠ c' ∉ D, escape cells (x, y) below c and (x', y') below
c', and witness-freeness (all rows of D) at the columns y, y', y ⊓ y', y ⊔ y' (those outside D).
A model shows that no cell is forced at these columns. Models are re-checked.
  python3 top2_probe.py [forest] (sweep P NMAX | closure K M SEED COUNT)
"""
import sys, itertools, collections, json
sys.path.insert(0, '../separation'); sys.path.insert(0, '../amalgamation')
import separator_stages as ss
from relay_probe import Enc, lattices

def build(L, forest):
    E = Enc(L); n = L.n; le = L.le; meet, join = L.meet, L.join; bot, top = L.bot, L.top; rk = L.rank
    f = lambda x, y, v: E.v('f', x, y, v); d = lambda e: E.v('d', e)
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
        if forest and rk[e] > 2: E.cl([-d(e)])
    if forest:
        blk = lambda e: E.v('blk', e)
        for e in range(n): E.iff_and(blk(e), [d(e)] + [-d(g) for g in range(n) if g != e and le[e][g]])
        atoms = [e for e in range(n) if rk[e] == 1]
        for m in range(n):
            for p, q in itertools.combinations([t for t in atoms if le[t][m]], 2):
                for n1 in range(n):
                    if n1 == m or not le[p][n1]: continue
                    for n2 in range(n):
                        if n2 == m or not le[q][n2]: continue
                        E.cl([-blk(m), -blk(n1), -blk(n2)])
    coat = [e for e in range(n) if top in L.covers_up[e]]
    C1, C2 = E.onehot('c1'), E.onehot('c2')
    for e in range(n):
        if e not in coat: E.cl([-C1(e)]); E.cl([-C2(e)])
        E.cl([-C1(e), -d(e)]); E.cl([-C2(e), -d(e)]); E.cl([-C1(e), -C2(e)])
    X1, Y1, X2, Y2 = E.onehot('x1'), E.onehot('y1'), E.onehot('x2'), E.onehot('y2')
    for (C, X, Y) in ((C1, X1, Y1), (C2, X2, Y2)):
        for c in coat:
            for x in range(n):
                for y in range(n):
                    ctx = [-C(c), -X(x), -Y(y)]
                    if not (le[x][c] and le[y][c]): E.cl(ctx); continue
                    E.cl(ctx + [d(x)]); E.cl(ctx + [-d(y)])
                    for v in range(n):                                   # F(x,y) ⊓ c ≤ x and F(x,y) ≰ c
                        if not le[meet[v][c]][x] or le[v][c]: E.cl(ctx + [-f(x, y, v)])
    cols = lambda y1, y2: {y1, y2, meet[y1][y2], join[y1][y2]}
    for y1 in range(n):
        for y2 in range(n):
            for y in cols(y1, y2):
                for x in range(n):
                    for v in range(n):
                        if le[v][x] or le[y][v]: E.cl([-Y1(y1), -Y2(y2), -d(x), d(y), -f(x, y, v)])
    return E

if __name__ == '__main__':
    args = sys.argv[1:]; forest = 'forest' in args; args = [a for a in args if a != 'forest']
    T = collections.Counter(); best = None
    for L in lattices(args):
        if L.height < 2: continue
        E = build(L, forest)
        if E.S.solve():
            m = set(x for x in E.S.get_model() if x > 0); n = L.n
            F = [[next(v for v in range(n) if E.vars[('f', x, y, v)] in m) for y in range(n)] for x in range(n)]
            D = [E.vars[('d', e)] in m for e in range(n)]
            pk = {k: next(e for e in range(n) if E.vars[(k, e)] in m) for k in ('c1', 'c2', 'x1', 'y1', 'x2', 'y2')}
            y1, y2 = pk['y1'], pk['y2']
            for y in {y1, y2, L.meet[y1][y2], L.join[y1][y2]}:
                assert D[y] or not any(D[x] and (L.le[F[x][y]][x] or L.le[y][F[x][y]]) for x in range(n))
            T['SAT'] += 1
            if best is None or n < best[0].n: best = (L, F, D, pk)
        else: T['UNSAT'] += 1
        E.S.delete()
    print(f"two top escapes{' (star forest)' if forest else ''}: {dict(T)}", flush=True)
    if best:
        L, F, D, pk = best; w_ = max(x.bit_length() for x in L.S)
        nm = lambda i: '{' + ''.join(str(j) for j in range(w_) if L.S[i] >> j & 1) + '}'
        print(f"smallest: |L| = {L.n}, height {L.height}, D = {[nm(i) for i in range(L.n) if D[i]]}, "
              + ', '.join(f'{k} = {nm(v)}' for k, v in pk.items()), flush=True)
        json.dump(dict(sets=L.S, F=F, D=D, pick=pk), open(f"top2{'_forest' if forest else ''}_min{L.n}.json", 'w'))
