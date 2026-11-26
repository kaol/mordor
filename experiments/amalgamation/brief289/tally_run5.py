"""Tally run5_lead.txt per corpus segment (lattice numbers are sequential over the '+'-joined corpora)."""
import sys, re, collections
SEG = [('closure 5 11 4 30', 1, 30), ('tall 8 4 1 12', 31, 42), ('tall 10 4 2 20', 43, 62), ('tall 12 4 1 8', 63, 70), ('tall 10 6 1 8', 71, 78)]
rows = []
for line in open(sys.argv[1]):
    m = re.match(r'\s+lattice #(\d+) n=(\d+) h=(\d+) \[(\d+)s\]: (.*)', line)
    if m: rows.append((int(m[1]), int(m[2]), int(m[3]), m[5]))
for name, a, b in SEG:
    R = [r for r in rows if a <= r[0] <= b]
    if not R: print(f'{name}: not reached'); continue
    C = collections.defaultdict(collections.Counter)
    for _, n, h, rest in R:
        for tok in rest.split():
            if ':' not in tok or '/' not in tok: continue
            k, v = tok.split(':', 1); C[k.split('/')[0]][v] += 1
    ns = [r[1] for r in R]; hs = sorted(set(r[2] for r in R))
    print(f'{name}: {len(R)}/{b - a + 1} lattices, |L| {min(ns)}-{max(ns)}, heights {hs}: ' + '; '.join(f'{k} {dict(v)}' for k, v in C.items()))
