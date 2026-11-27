import re, glob, collections, os
def stat(f):
    if not os.path.exists(f): return None
    T = open(f).read().splitlines()
    sat = [l for l in T if re.search(r': SAT$', l)]; uns = [l for l in T if 'UNSAT' in l and 'lattice' in l]
    ns = [int(re.search(r'n=(\d+)', l).group(1)) for l in sat + uns]
    hs = sorted({int(re.search(r'h=(\d+)', l).group(1)) for l in sat + uns})
    br = collections.Counter(re.sub(r'.*branch (\w+), N = (\d+).*', r'\1 N\2', l) for l in T if 'model:' in l)
    return len(sat), len(sat) + len(uns), ns, hs, br
rows = [('closure 6 12 1 40', 'R3_A2_closure_6_12_1_40', 'M_CGone_closure_6_12_1_40'),
        ('closure 8 10 1 300 maxn 45 (capped)', 'R3_A2_closure_8_10_1_300', None),
        ('closure 5 11 4 30', None, 'M_CGone_closure_5_11_4_30'),
        ('tall 13 4 1 8 maxn 45', 'R3_A2_tall_13_4_1_8', 'M_CGone_tall_13_4_1_8'),
        ('tall 14 4 2 20 maxn 45 (capped)', 'R3_A2_tall_14_4_2_20', 'M_CGone_tall_14_4_2_20'),
        ('tall 10 6 1 8 maxn 45 (M 6)', 'R3_A2_tall_10_6_1_8', 'M_CGone_tall_10_6_1_8'),
        ('tall 10 7 1 5 maxn 50 (M 7)', 'R3_A2_tall_10_7_1_5', 'M_CGone_tall_10_7_1_5')] + \
       [('tall 12 4 1 8 maxn 45, exact %s' % E, 'R3_A2_%s_tall_12_4_1_8' % E, 'M_CGone_%s_tall_12_4_1_8' % E) for E in ('E3', 'E4', 'E5', 'E6')] + \
       [('closure 6 12 1 40, UNB only (any |A|)', 'R3_any_closure_6_12_1_40', 'M_CGone_any_closure_6_12_1_40'),
        ('tall 10 6 1 8 maxn 45, |A| = 3', 'R3_A3_tall_10_6_1_8', None)]
print('| corpus | candidate R3 SAT / lattices (H, \\|L\\|) | mutant CGone SAT / lattices (branch, N of its models) |')
print('|---|---|---|')
tot = [0, 0, 0, 0]
for name, c, m in rows:
    cs = stat('run5/%s.txt' % c) if c else None; ms = stat('run5/%s.txt' % m) if m else None
    def fm(s, br=False):
        if s is None: return '—'
        a, b, ns, hs, bb = s
        t = '%d / %d (H %s, \\|L\\| %s)' % (a, b, ','.join(map(str, hs)) or '-', ('%d-%d' % (min(ns), max(ns))) if ns else '-')
        if br and bb: t += ' ' + ', '.join('%s:%d' % kv for kv in sorted(bb.items()))
        return t
    print('| %s | %s | %s |' % (name, fm(cs), fm(ms, True)))
    if cs and 'any' not in name and '|A| = 3' not in name: tot[0] += cs[0]; tot[1] += cs[1]
    if ms and 'any' not in name: tot[2] += ms[0]; tot[3] += ms[1]
print()
print('TOTAL |A| = 2 rows: candidate %d / %d, mutant %d / %d' % tuple(tot))
