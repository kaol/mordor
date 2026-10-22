"""Pattern-wise narrowed closure for DC2 on M_ω² × C₂ (§34.3z⁸).

For one thick level-0 pattern of D: the closed level-0 cells C0 (a chain or low-width set) and the closed level-1
cells (minimal fibre cells found by selector cores at small sizes, read as shapes in a generic atom a, instantiated for
every L1 atom).  L1 := atoms at C0 cells, L2 := new atoms at closed level-1 cells; every other cell of level ≤ 1 takes
{⊥, ⊤} ∪ L1 ∪ L2 ∪ {o}.  Exhaustive check with |L1| ≤ 2·width(C0), |L2| ≤ 2·width(closed level-1 cells over k atoms).
The choice of closed sets only affects which instances are checked, never soundness."""
import sys
import dc2_lazy as d, dc2_eager as e, plane_full as P, pattern_full as PF
from thick_patterns import patterns, width
B, T = d.B, d.T
A = ('a', 0)


def pat_of(tag):
    return next(p for p in patterns() if ''.join('1' if p[q] else '0' for q in [(B, T, 0), (B, T, 1), (T, B, 0), (T, B, 1)]) == tag)


def find_shapes(tag, cells, sizes=((1, 2), (1, 4), (2, 2), (2, 4))):
    d.DPAT = pat_of(tag); d.CLOSED0 = lambda x, y: (x, y) in set(cells)
    d.CLOSED1 = lambda x, y: False; d.SEL1 = P.fibre
    shapes = set()
    for k, m in sizes:
        r = e.run(k, m, 2, verbose=False)
        assert isinstance(r, list), r
        for x, y in r:
            (a,) = {t for p in (x, y) for t in p[:2] if t not in (B, T)}
            sub = lambda p: tuple(A if t == a else t for t in p[:2]) + (p[2],)
            shapes.add((sub(x), sub(y)))
    d.SEL1 = None
    return sorted(shapes, key=str)


def inst(shapes, a):
    sub = lambda p: tuple(a if t == A else t for t in p[:2]) + (p[2],)
    return [(sub(x), sub(y)) for x, y in shapes]


def run(tag, cells, ks=None, shapes=None):
    if shapes is None: shapes = find_shapes(tag, cells)
    print(f"pattern {tag}: {len(cells)} closed level-0 cells, {len(shapes)} level-1 shapes", flush=True)
    d.DPAT = pat_of(tag); d.CLOSED0 = lambda x, y: (x, y) in set(cells)
    kmax = 2 * width(cells)
    for k in (ks if ks is not None else range(0, kmax + 1)):
        closed1 = set(c for i in range(k) for c in inst(shapes, ('a', i)))
        d.CLOSED1 = lambda x, y, closed1=closed1: (x, y) in closed1
        m = 2 * width(sorted(closed1, key=str)) if k else 0
        d.run(k, m, 2)
    return shapes


if __name__ == "__main__":
    import os
    if os.environ.get('BLOCK_MAXL1'): d.BLOCK_MAXL1 = int(os.environ['BLOCK_MAXL1'])
    if os.environ.get('PREC_L2') == '0': d.PREC_L2 = False
    # argv: tag, closed level-0 cells, [atom-free level-0 cells (case split) | -], [k list]
    if len(sys.argv) > 3 and sys.argv[3] != '-':
        Z = set(PF.parse_cell(c) for c in sys.argv[3].split(';')); d.ZERO0 = lambda x, y: (x, y) in Z
        print('case split: atom-free level-0 cells', len(Z), flush=True)
    ks = [int(a) for a in sys.argv[4].split(',')] if len(sys.argv) > 4 else None
    run(sys.argv[1], [PF.parse_cell(c) for c in sys.argv[2].split(';')], ks=ks)
