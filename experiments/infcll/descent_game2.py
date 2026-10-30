"""Strengthened descent game (k = 3): per-row end labels E_B for every row that is a label or contracting.
Successor constraints for a move along row A (w = w(A, c)):
  labels grow downward; rows B >= A holding columns contract; E_B(w) comparable to E_B(c) for B >= A (squeeze);
  E_A(w) = E_A(c) (the A-orbit continues through w); label rows have E_B = their label.
Optional cross-row fact X (B >= B', both descending at w): the B-orbit lies below the B'-orbit, so if the B'-orbit ends
with label l then E_B ... (not used unless --cross).
Bounded-depth adversary search."""
import itertools, sys, numpy as np
sys.setrecursionlimit(10000)
k = 3
G = frozenset(range(k))
ROWS = [frozenset(A) for r in range(1, k + 1) for A in itertools.combinations(range(k), r)]
LABS = [A for A in ROWS if A != G]
LI = {l: i for i, l in enumerate(LABS)}
LT, NC = 6, 7
def vle(x, y):
    if x[0] == 'L' and y[0] == 'L': return y[1] <= x[1]
    if x[0] == 'L': return True
    if y[0] == 'L': return False
    return not (x == 'nc' and y == 'lt')
def opts(A): return [('L', al) for al in LABS if not A <= al] + ['lt', 'nc']
profiles = []
for vals in itertools.product(*[opts(A) for A in ROWS]):
    p = dict(zip(ROWS, vals))
    if p[G] == 'nc': continue
    if all(not (A2 <= A) or A2 == A or vle(p[A], p[A2]) for A in ROWS for A2 in ROWS): profiles.append(vals)
Ks, Es = [], []
for vals in profiles:
    kinds = [LI[v[1]] if v[0] == 'L' else (LT if v == 'lt' else NC) for v in vals]
    choices = []
    for A, v in zip(ROWS, vals):
        if v[0] == 'L': choices.append([LI[v[1]]])
        elif v == 'lt': choices.append([LI[al] for al in LABS if not A <= al])
        else: choices.append([-1])
    for ev in itertools.product(*choices):
        Ks.append(kinds); Es.append(ev)
K = np.array(Ks, dtype=np.int8); E = np.array(Es, dtype=np.int8); N = len(K)
print("states", N, flush=True)
SUP = np.zeros((8, 8), bool)      # SUP[a][b]: kind b is a label containing label a (for a label); a non-label: anything
for a in range(6):
    for b in range(6): SUP[a][b] = LABS[a] <= LABS[b]
SUP[LT, :] = True; SUP[NC, :] = True
COMP = np.zeros((7, 7), bool)     # index 6 = undefined (-1)
for a in range(6):
    for b in range(6): COMP[a][b] = LABS[a] <= LABS[b] or LABS[b] <= LABS[a]
dead = ~(K == LT).any(1)
supsets = {ai: [bi for bi, B in enumerate(ROWS) if ROWS[ai] <= B] for ai in range(7)}
def succ_mask(s, a):
    m = np.ones(N, bool)
    for b in range(7):
        m &= SUP[K[s, b]][K[:, b]]
    for b in supsets[a]:
        m &= K[:, b] != NC
        m &= COMP[E[s, b]][E[:, b]]
    m &= E[:, a] == E[s, a]
    return m
memo = {}
def adv(s, d):
    if dead[s]: return True
    if d == 0: return False
    key = (s, d)
    if key in memo: return memo[key]
    res = True
    for a in range(7):
        if K[s, a] != LT: continue
        idx = np.flatnonzero(succ_mask(s, a))
        if dead[idx].any(): continue
        if d - 1 == 0 or not any(adv(int(t), d - 1) for t in idx): res = False; break
    memo[key] = res
    return res
init = np.flatnonzero(~(K == NC).any(1))
print("initial states", len(init), flush=True)
for D in range(1, int(sys.argv[1]) + 1):
    wins = [int(s) for s in init if adv(int(s), D)]
    print(f"depth {D}: adversary wins from {len(wins)} initial states", flush=True)
    if wins:
        s = wins[0]
        print("  example:", {tuple(sorted(ROWS[b])): (sorted(LABS[K[s, b]]) if K[s, b] < 6 else ('lt' if K[s, b] == LT else 'nc'))
                            for b in range(7)}, "E:", {tuple(sorted(ROWS[b])): sorted(LABS[E[s, b]]) for b in range(7) if E[s, b] >= 0})
        break
