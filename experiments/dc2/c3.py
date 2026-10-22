"""DC2 on M_ω² × C_n for general n (§34.3z¹¹): level-0 patterns, low-width closures, narrowing, lazy check."""
import itertools, sys, random
import dc2_lazy as d, dc2_eager as e, plane_full as P
from thick_patterns import width
from chain_search import maximal_chains
B, T = d.B, d.T
cle = d.cle
ple = lambda p, q: cle(p[0], q[0]) and cle(p[1], q[1]) and p[2] <= q[2]

def level0_points(n): return [(u, v, l) for u in (B, T) for v in (B, T) for l in range(n)]

def all_patterns(n):
    P0 = level0_points(n)
    for bits in itertools.product((0, 1), repeat=len(P0)):
        D = {p for p, b in zip(P0, bits) if b}
        if (B, B, 0) not in D or (T, T, n - 1) in D: continue
        if any(q in D and p not in D for p in P0 for q in P0 if ple(p, q)): continue
        yield {p: (p in D) for p in P0}

def tag(pat, n): return ''.join('1' if pat[p] else '0' for p in level0_points(n))

def swap_pat(pat): return {(p[1], p[0], p[2]): v for p, v in pat.items()}

def test(closed, n, sizes):
    d.CLOSED0 = lambda x, y: (x, y) in closed
    for k, m in sizes:
        if e.run(k, m, n, verbose=False): return False
    return True

def low_width_closure(pat, n, maxw=4, sizes=((0, 0), (1, 2), (2, 2))):
    d.DPAT = pat; d.CLOSED1 = P.fibre; d.SEL0 = False; d.ZERO0 = None
    Dset = {p for p, v in pat.items() if v}
    cells = [(x, y) for x in pat for y in pat if x in Dset and y not in Dset]
    chains = maximal_chains(cells)
    for w in range(1, maxw + 1):
        for combo in itertools.combinations(chains, w):
            cs = set().union(*map(set, combo))
            if width(sorted(cs, key=str)) <= w and test(cs, n, sizes): return w, sorted(cs, key=str)
    return None, cells

def find_shapes(pat, cells, n, sizes=((1, 2), (1, 4), (2, 2))):
    d.DPAT = pat; d.CLOSED0 = lambda x, y: (x, y) in set(cells)
    d.CLOSED1 = lambda x, y: False; d.SEL1 = P.fibre
    A = ('a', 0); shapes = set()
    for k, m in sizes:
        r = e.run(k, m, n, verbose=False)
        assert isinstance(r, list), r
        for x, y in r:
            (a,) = {t for p in (x, y) for t in p[:2] if t not in (B, T)}
            sub = lambda p: tuple(A if t == a else t for t in p[:2]) + (p[2],)
            shapes.add((sub(x), sub(y)))
    d.SEL1 = None
    return sorted(shapes, key=str)

def inst(shapes, a):
    A = ('a', 0)
    sub = lambda p: tuple(a if t == A else t for t in p[:2]) + (p[2],)
    return [(sub(x), sub(y)) for x, y in shapes]

if __name__ == "__main__":
    n = int(sys.argv[1])
    pats = list(all_patterns(n))
    reps, seen = [], set()
    for p in pats:
        t = tag(p, n)
        if t in seen: continue
        seen.add(t); seen.add(tag(swap_pat(p), n)); reps.append(p)
    print(f"n={n}: {len(pats)} level-0 patterns, {len(reps)} up to coordinate swap", flush=True)
    for p in reps[:int(sys.argv[2])] if len(sys.argv) > 2 else reps:
        w, cs = low_width_closure(p, n)
        print(tag(p, n), 'closure width', w, 'cells', len(cs), flush=True)
