"""Free replay (no search): TwoRowTb and desc1 on every distinct stored model. World W0^2 / desc1 as in meet_probe.py.
FAIL = a stored model of the world with NoFix (a counterexample)."""
import sys; sys.path.insert(0, '.'); from world import *
from collections import Counter
C = Counter()
for name, w in dedup(load_all()):
    if not (w.base() and all(w.Ta(x) for x in w.Z if x != w.bot)): C['outside base/Ta'] += 1; continue
    le, h, F, meet = w.le, w.h, w.F, w.L.meet
    if any(le[w.lam(m)][m] for m in w.M2): C['outside (some m in M2 with lambda(m) <= m)'] += 1; continue
    for mode in ('two', 'desc1'):
        ok = True
        for q in w.atoms:
            dq = w.desc(q)
            cols = set(y for y in dq if h[y] >= 3) if mode == 'desc1' else \
                   set(meet[z1][z2] for x2 in w.Z if le[q][x2] for z1 in dq for z2 in w.desc(x2) if h[meet[z1][z2]] >= 3)
            ok = ok and all(not le[F[q][y]][q] for y in cols)
        if not ok: C[(mode, 'outside world')] += 1; continue
        C[(mode, 'in world', 'NoFix FAIL' if w.nofix() else 'pass')] += 1
        if w.nofix(): print('  stored model in', mode, '& NoFix:', name)
for k in sorted(C, key=str): print(k, C[k])
