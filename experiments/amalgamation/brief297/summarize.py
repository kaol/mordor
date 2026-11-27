"""Summarize every run output: per file the SAT/UNSAT counts, heights, |L| range, and the branch/N of SAT models."""
import glob, re, collections, sys
for f in sorted(glob.glob('run*/*.txt')):
    if f.endswith('_wall.txt') or 'fp_' in f or 'hand_out' in f: continue
    T = open(f).read().splitlines()
    sat = [l for l in T if re.search(r': SAT$', l)]; uns = [l for l in T if 'UNSAT' in l and 'lattice' in l]
    ns = [int(re.search(r'n=(\d+)', l).group(1)) for l in sat + uns]
    hs = sorted({int(re.search(r'h=(\d+)', l).group(1)) for l in sat + uns})
    br = collections.Counter(l.strip().replace('model: ', '') for l in T if 'model:' in l)
    print('%-48s SAT %3d / %3d  |L| %s  H %s  %s' % (f, len(sat), len(sat) + len(uns), ('%d-%d' % (min(ns), max(ns))) if ns else '-', hs, dict(br) if br else ''))
