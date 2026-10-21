"""For each thick level-0 pattern, search closed sets of level-0 cells of small width (chains first, then antichains of
two chains) that still make the small instances UNSAT.  Width w of the closed set bounds |L1| ≤ 2w."""
import itertools, sys
import dc2_lazy as d, dc2_eager as e, plane_full as P
from thick_patterns import patterns, ple, width
B, T = d.B, d.T

def test(closed, sizes):
    d.CLOSED0 = lambda x, y: (x, y) in closed
    for k, m in sizes:
        if e.run(k, m, 2, verbose=False): return False
    return True

def maximal_chains(cells):
    le = lambda c, c2: c != c2 and ple(c[0], c2[0]) and ple(c[1], c2[1])
    mins = [c for c in cells if not any(le(c2, c) for c2 in cells)]
    out = []
    def ext(ch):
        last = ch[-1]
        nxt = [c for c in cells if le(last, c) and not any(le(last, c3) and le(c3, c) for c3 in cells)]
        if not nxt: out.append(ch); return
        for c in nxt: ext(ch + [c])
    for c in mins: ext([c])
    return out

if __name__ == "__main__":
    d.CLOSED1 = P.fibre; d.SEL0 = False
    sizes = [(1, 2), (2, 2)]
    for pat in patterns():
        d.DPAT = pat
        tag = ''.join('1' if pat[p] else '0' for p in [(B, T, 0), (B, T, 1), (T, B, 0), (T, B, 1)])
        Dset = {p for p, v in pat.items() if v}
        cells = [(x, y) for x in pat for y in pat if x in Dset and y not in Dset]
        chains = maximal_chains(cells)
        found = None
        for ch in chains:
            if test(set(ch), sizes): found = (1, ch); break
        if not found:
            for c1, c2 in itertools.combinations(chains, 2):
                cs = set(c1) | set(c2)
                if width(sorted(cs)) <= 2 and test(cs, sizes): found = (2, sorted(cs)); break
        fmt = lambda c: f"({''.join('⊥' if t == B else '⊤' for t in c[0][:2])}{c[0][2]},{''.join('⊥' if t == B else '⊤' for t in c[1][:2])}{c[1][2]})"
        print(tag, f"{len(chains)} maximal chains;", 'none of width ≤ 2' if not found else f"width {found[0]}: " + ' '.join(fmt(c) for c in found[1]), flush=True)
