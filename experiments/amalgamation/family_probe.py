"""Configuration-family transfer for bad fibres (log §34.3z¹⁹⁰).

Models: for every qualifying m of every lattice, the SAT models of 'noic_fi' and of the refuting claims 'stabletop'
and 'pairjump' (each of the latter contains a bad stage-k configuration). For each bad configuration (p, c) at stage
k (no y ∈ S(p, c; m) comparable with F(c, y)) and each y ∈ S: the row value t = F(c, y) and c′ = F(p, t). Transfer:
c′ = c (t stays in the bad fibre) or (p, c′) is a stage-k configuration with t ∈ S(p, c′; m). Orbit: iterate
y ↦ F(c, y) while it stays in S; record where it exits and whether the exit configuration is good.
   python3 family_probe.py [rmin=R] (closure … | sweep …)
"""
import sys, collections, json, signal
sys.argv += ['multi', 'nopostlayer']
sys.path.insert(0, '../separation')
from rstages import stages, b_of, a_of
from tight_probe import lattices
import single_claims as sc

C = collections.Counter(); best = {}
def report(*_):
    for k_, v in sorted(C.items(), key=str): print(k_, v)
    for k_, v in sorted(best.items()): print('MIN', k_, v)
    sys.stdout.flush(); sys.exit(0)
signal.signal(signal.SIGTERM, report)
def keep(tag, n, d):
    if tag not in best or n < best[tag]:
        best[tag] = n; json.dump(d, open(f'fam_{tag}_min{n}.json', 'w'))

for L in lattices([a for a in sys.argv[1:] if a not in ('multi', 'nopostlayer') and not a.startswith('rmin=')]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        for claim in ('noic_fi', 'stabletop', 'pairjump'):
            F = sc.query(L, m, claim, False)
            if not F: continue
            n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F)
            inR = lambda x, j: st[x] is not None and st[x] <= j
            new = lambda x, j: inR(x, j) and not inR(x, j - 1) and h[x] == j
            fib = lambda p, c: [v for v in range(n) if le[c][v] and v != c and not le[m][v] and F[p][v] == c]
            cfgs = {(p, c) for c in range(n) if new(c, k) for p in range(n)
                    if inR(p, k - 1) and h[p] == k - 1 and le[p][c] and p != c and F[p][c] == p and fib(p, c)}
            good = {pc: any(le[F[pc[1]][y]][y] or le[y][F[pc[1]][y]] for y in fib(*pc)) for pc in cfgs}
            mp = b_of(L, F, m)
            C[('model', claim, 'configurations', min(len(cfgs), 4), 'bad', min(sum(not g for g in good.values()), 3), 'TopFibre', any(good.values()))] += 1
            for (p, c), g in good.items():
                if g: continue
                S = fib(p, c)
                C[('bad config', claim, 'same-source good config', any(good[q] for q in cfgs if q[0] == p), 'some good config', any(good.values()),
                   'c = m′', c == mp)] += 1
                if not any(good[q] for q in cfgs if q[0] == p):
                    keep('nosamesource', n, dict(sets=L.S, F=F, m=m, p=p, c=c))
                    rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
                    ts = {F[c][y] for y in S}
                    for (p2, c2), g2 in good.items():
                        if not g2: continue
                        C[('cross-source good config vs bad (p, c)', claim, 'p′ vs p', rl(p2, p), 'c′ vs c', rl(c2, c), 'b(p′) = b(p)', b_of(L, F, p2) == b_of(L, F, p),
                           'c′ below some row value t = F(c, y)', any(le[c2][t] for t in ts), 'fibres meet', bool(set(fib(p2, c2)) & set(S)), 'c′ = m′', c2 == mp)] += 1
                exits = []
                for y in S:
                    t = F[c][y]; c2 = F[p][t]
                    kind = ('stays (c′ = c)' if c2 == c else
                            'to a configuration (p, c′), t ∈ S(p, c′)' if (p, c2) in cfgs and t in fib(p, c2) else
                            'c′ not a configuration top' if (p, c2) not in cfgs else 't ∉ S(p, c′)')
                    C[('bad fibre column', claim, 'transfer', kind, 'good target', good.get((p, c2)) if (p, c2) in cfgs and c2 != c else None,
                       't comparable in row c′', (le[F[c2][t]][t] or le[t][F[c2][t]]) if kind.startswith('to') else None)] += 1
                    if kind not in ('stays (c′ = c)', 'to a configuration (p, c′), t ∈ S(p, c′)'):
                        keep('transfer_' + kind.split()[0] + '_' + kind.split()[1], n, dict(sets=L.S, F=F, m=m, p=p, c=c, y=y))
                    # orbit within the bad fibre
                    seen = []; z = y
                    while z in S and z not in seen: seen.append(z); z = F[c][z]
                    if z in S: exits.append(('cycles in S', None)); C[('orbit from y', claim, 'cycles inside S')] += 1; continue
                    c3 = F[p][z]
                    ok = (p, c3) in cfgs and z in fib(p, c3)
                    exits.append((ok, good.get((p, c3)) if ok else None))
                    C[('orbit from y', claim, 'exits to a configuration (p, F(p, z)) with z in its fibre', ok, 'its goodness', good.get((p, c3)) if ok else None,
                       'm ≤ exit', le[m][z])] += 1
                    if not (ok and good[(p, c3)]): keep('orbit_' + ('noconfig' if not ok else 'badexit'), n, dict(sets=L.S, F=F, m=m, p=p, c=c, y=y))
                C[('bad config: some fibre orbit exits to a good same-source configuration', claim, any(e == (True, True) for e in exits))] += 1
                if not any(e == (True, True) for e in exits): keep('noescape', n, dict(sets=L.S, F=F, m=m, p=p, c=c))
report()
