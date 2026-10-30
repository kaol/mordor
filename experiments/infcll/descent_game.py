"""Abstract descent game for max-only CLL (k rows-generators).
State at a column c: profile p (row -> ('L', alpha) | 'lt' (column < c) | 'nc' (column not <= c)) and E = end label
of the meet-row orbit. Prover picks a contracting row A ('lt'); w = w(A,c) < c. Adversary picks a consistent state at w
with: labels grow downward (label alpha at (B,c) => label beta >= alpha at (B,w)); rows B >= A holding columns are 'lt';
E(w) comparable to E(c); E = meet-row label when the meet row is a label. Prover must always be able to move
(DCC then refutes any counterexample realizing the invariant)."""
import itertools, sys
k = int(sys.argv[1])
G = frozenset(range(k))
ROWS = [frozenset(A) for r in range(1, k + 1) for A in itertools.combinations(range(k), r)]
LABS = [A for A in ROWS if A != G]
FULL = G
def vle(x, y):   # value order of row values at the same column, for B >= B' : value(B) <= value(B')
    if x[0] == 'L' and y[0] == 'L': return y[1] <= x[1]
    if x[0] == 'L': return True
    if y[0] == 'L': return False
    return not (x == 'nc' and y == 'lt')       # B' contracting => B contracting
def opts(A):
    return [('L', al) for al in LABS if not A <= al] + ['lt', 'nc']
profiles = []
for vals in itertools.product(*[opts(A) for A in ROWS]):
    p = dict(zip(ROWS, vals))
    if p[FULL] == 'nc': continue                      # meet row: label or contracting (orbit descends)
    if all(not (A2 <= A) or A2 == A or vle(p[A], p[A2]) for A in ROWS for A2 in ROWS): profiles.append(vals)
print("consistent profiles", len(profiles), flush=True)
states = []
for vals in profiles:
    p = dict(zip(ROWS, vals))
    for E in LABS:
        if p[FULL][0] == 'L' and p[FULL][1] != E: continue
        states.append((vals, E))
print("states", len(states), flush=True)
idx = {s: i for i, s in enumerate(states)}
def comparable(a, b): return a <= b or b <= a
def next_ok(s, A, t):
    (pv, E), (qv, E2) = s, t
    if not comparable(E, E2): return False
    for B, x, y in zip(ROWS, pv, qv):
        if x[0] == 'L' and not (y[0] == 'L' and x[1] <= y[1]): return False
        if A <= B and y == 'nc': return False
    return True
# group target states by E for speed
byE = {}
for i, (qv, E2) in enumerate(states): byE.setdefault(E2, []).append(i)
safe = [True] * len(states)
moves = {}
for i, s in enumerate(states):
    pv, E = s
    ms = []
    for A, x in zip(ROWS, pv):
        if x == 'lt':
            succ = [j for E2 in LABS if comparable(E, E2) for j in byE.get(E2, []) if next_ok(s, A, states[j])]
            ms.append((A, succ))
    moves[i] = ms
print("moves computed", flush=True)
changed = True; it = 0
while changed:
    changed = False; it += 1
    for i in range(len(states)):
        if not safe[i]: continue
        if not any(all(safe[j] for j in succ) for A, succ in moves[i]):
            safe[i] = False; changed = True
init = [i for i, (pv, E) in enumerate(states) if 'nc' not in pv]
bad_init = [i for i in init if not safe[i]]
print(f"k={k}: iterations {it}; safe {sum(safe)}/{len(states)}; initial states {len(init)}, unsafe initial {len(bad_init)}")
if bad_init:
    pv, E = states[bad_init[0]]
    print("an unsafe initial state:", {tuple(sorted(A)): v for A, v in zip(ROWS, pv)}, "E =", sorted(E))
