"""Full DC2 check for one thick level-0 pattern of D on M_ω² × C₂ with a fixed closed set C0 of level-0 cells.
L1 := atoms at C0 cells (|L1| ≤ 2·width(C0)); other level-0 cells take {⊥, ⊤} ∪ L1 ∪ L2 ∪ {o}; level-1 fibre cells
closed, |L2| ≤ fibre width bound.  Sound by the restriction argument of §34.3z⁶–⁷."""
import sys, time
import dc2_lazy as d, plane_full as P
from thick_patterns import patterns, width
B, T = d.B, d.T

def parse_cell(s):
    # '⊥⊥0,⊥⊤0' -> ((b,b,0),(b,t,0))
    m = {'⊥': B, '⊤': T}
    a, b = s.split(',')
    return ((m[a[0]], m[a[1]], int(a[2])), (m[b[0]], m[b[1]], int(b[2])))

if __name__ == "__main__":
    tag = sys.argv[1]; cells = [parse_cell(c) for c in sys.argv[2].split(';')]
    kmax = 2 * width(cells)
    pat = next(p for p in patterns() if ''.join('1' if p[q] else '0' for q in [(B, T, 0), (B, T, 1), (T, B, 0), (T, B, 1)]) == tag)
    d.DPAT = pat; d.CLOSED1 = P.fibre; d.CLOSED0 = lambda x, y: (x, y) in set(cells)
    print(f"pattern {tag}: closed {len(cells)} cells, |L1| ≤ {kmax}", flush=True)
    ks = [int(a) for a in sys.argv[3].split(',')] if len(sys.argv) > 3 else range(0, kmax + 1)
    for k in ks:
        m = P.l2_width_bound(k, 2) if k else 0
        d.run(k, m, 2)
