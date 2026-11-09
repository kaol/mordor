"""Exhaustive descent-free search over all closure systems on P points (log §34.3z¹³⁶).

For every Moore family on P points (up to point permutation) whose lattice has at most NMAX elements and height ≥ 3,
exist_cegar.no_descent decides whether some monotone F and cut D admit NO maximum-gap-descending run, with maximal or
(--general) general separators. Each found instance is re-checked with general_sep.exist_desc.
  python3 nodesc_sweep.py [--general] [--all-heights] P NMAX SECONDS_PER_LATTICE [SHARD NSHARDS]
"""
import sys, itertools, time, json
import separator_stages as ss
import exist_cegar as ec
from general_sep import exist_desc, gseps

def moore_families(P):
    full = (1 << P) - 1; seen = set()
    others = [s for s in range(full)]
    for mask in range(1 << len(others)):
        fam = {full} | {others[i] for i in range(len(others)) if mask >> i & 1}
        if any((a & b) not in fam for a in fam for b in fam): continue
        canon = min(tuple(sorted(sum(1 << p[i] for i in range(P) if s >> i & 1) for s in fam))
                    for p in itertools.permutations(range(P)))
        if canon in seen: continue
        seen.add(canon); yield sorted(fam, key=lambda x: (bin(x).count('1'), x))

HMIN = 3

if __name__ == "__main__":
    if '--general' in sys.argv: sys.argv.remove('--general'); ec.GENERAL = True
    if '--all-heights' in sys.argv: sys.argv.remove('--all-heights'); HMIN = 0
    P, NMAX, secs = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    shard, nsh = (int(sys.argv[4]), int(sys.argv[5])) if len(sys.argv) > 5 else (0, 1)
    sepf = gseps if ec.GENERAL else (lambda L, F, x, y: ss.max_separators(L, F[x][y], y))
    cnt = 0; found = []; undecided = 0; t0 = time.time()
    for i, fam in enumerate(moore_families(P)):
        if len(fam) > NMAX or i % nsh != shard: continue
        L = ss.Lat(fam)
        if L.height < HMIN: continue
        cnt += 1; r, it = ec.no_descent(L, secs)
        if r is None or r == 'cap': undecided += 1; print(f"undecided: |L| = {L.n}, height {L.height}, {r}", flush=True); continue
        if r:
            F, D = r; ok = exist_desc(L, F, D, sepf, limit=10 ** 7) is False
            found.append((L.n, L.height)); print(f"FOUND: |L| = {L.n}, height {L.height}, verified {ok}, sets {fam}", flush=True)
            json.dump(dict(sets=L.S, F=F, D=D, general=ec.GENERAL), open(f"nodesc_sweep_{'g' if ec.GENERAL else 'm'}_{L.n}_{i}.json", 'w'))
    print(f"{'general' if ec.GENERAL else 'maximal'} separators, closure systems on {P} points, |L| ≤ {NMAX}, height ≥ {HMIN}, "
          f"shard {shard}/{nsh}: {cnt} lattices, descent-free instances on {len(found)} {sorted(found)}, undecided {undecided}, "
          f"{time.time() - t0:.0f} s", flush=True)

def max_sweep(P, NMAX, secs):
    """Exact maximum existential minimum (exist_cegar.maximum) over the same lattices; returns {height: Counter}."""
    import collections
    out = collections.defaultdict(collections.Counter)
    for fam in moore_families(P):
        if len(fam) > NMAX: continue
        L = ss.Lat(fam)
        if L.height < 2: continue
        b, how, _ = ec.maximum(L, 2 * L.height + 2, secs)
        out[L.height][(b, how.startswith('exact'))] += 1
    return out
