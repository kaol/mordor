"""Role-promotion operator on the verified certificates, and seeded ground tests (log §34.3z⁹⁷).

P(T; R, C) = {F(r, c) : r ∈ R, c ∈ C ∪ T} ∪ {F(r, c) : r ∈ R ∪ T, c ∈ C}  (R, C = rows / columns used in T).
1. One round P(T4) against the 69 new H = 5 terms: which are explained, which are the exceptions, and why.
2. Iterated promotion with the H = 4 roles fixed and T growing only by certificate terms: coverage of T5.
3. Seeded ground tests with experiments/sat/cut_ground.Ground (no term expansion): H = 5 with the term sets
   T4, T4 ∪ P(T4), T5 (control). UNSAT means that term set alone refutes the Cut axioms at edge-height ≤ 5.
4. Size of the H = 6 pool P(T5) and a checkpoint file for an external run."""
import sys, os, time, pickle, collections
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'sat'))
from classify import parse, parse_term, tok, depth
def load(path, name): return {k: parse_term(tok(v))[0] for k, v in parse(path, name).items()}
T4 = set(load("../../lean/Mordor/CutHeight4.lean", "tv4").values())
T5d = load("../../lean/Mordor/CutHeight5.lean", "tv5"); T5 = set(T5d.values()); idx5 = {t: k for k, t in T5d.items()}
def roles(S):
    R, C = set(), set()
    for t in S:
        if not isinstance(t, str): R.add(t[1]); C.add(t[2])
    return R, C
def P(T, R, C): return {("F", r, c) for r in R for c in C | T} | {("F", r, c) for r in R | T for c in C}
R4, C4 = roles(T4)
new = {t for t in T5 - T4 if not isinstance(t, str)}
P4 = P(T4, R4, C4)
expl = new & P4; exc = new - P4
print(f"|P(T4)| = {len(P4)}; new H=5 terms explained by one round: {len(expl)} of {len(new)}")
cov = set(T4); rounds = 0
while True:
    add = {t for t in new - cov if (t[1] in R4 and (t[2] in cov)) or (t[2] in C4 and (t[1] in cov))}
    if not add: break
    cov |= add; rounds += 1
print(f"iterated promotion (H=4 roles fixed, T grows by certificate terms): covers {len(cov & new)} of {len(new)} "
      f"in {rounds} rounds")
rest = sorted(new - cov, key=lambda t: idx5[t])
print(f"exceptions ({len(rest)}): neither coordinate in its H=4 role")
for t in rest:
    r, c = t[1], t[2]
    def tag(x, R): return "role" if x in R else ("T4" if x in T4 else f"new#{idx5[x]}")
    print(f"   term {idx5[t]:2d} depth {depth(t)}: row {tag(r, R4)}, column {tag(c, C4)}")
# ---- seeded ground tests -------------------------------------------------------------------------------------
from cut_ground import Ground
def to_pairs(S):
    order = sorted([t for t in S if not isinstance(t, str)], key=depth)
    ix = {"⊥": 0, "⊤": 1}; pairs = []
    def ensure(t):
        if t in ix: return ix[t]
        a = ensure(t[1]); b = ensure(t[2]); pairs.append((a, b)); ix[t] = 1 + len(pairs); return ix[t]
    for t in order: ensure(t)
    return pairs, ix
def ground_test(H, S, label):
    pairs, ix = to_pairs(S)
    assert pairs[0] == (0, 1), "first term must be F(⊥, ⊤)"
    G = Ground(H, True, False, False, None, 'fit', False, None)
    c = G.add_term((0, 1), 1); G.add_ih(c); G.S.add_clause([-G.d(c)])      # as cut_ground.run(wlog=True)
    for st in pairs[1:]: G.add_term(st, max(G.depth[st[0]], G.depth[st[1]]) + 1)
    t0 = time.time(); M = G.solve()
    print(f"H={H} seeded with {label}: {len(G.terms)} terms -> {'UNSAT' if M is None else 'SAT'} ({time.time()-t0:.1f}s)",
          flush=True)
    return M is None
if 'ground' in sys.argv:
    ground_test(5, T5, "T5 (control)")
    ground_test(5, T4, "T4")
    ground_test(5, T4 | P4, "T4 ∪ P(T4)")
R5, C5 = roles(T5); P5 = P(T5, R5, C5) | T5
print(f"H=6 role pool P(T5) ∪ T5: {len(P5)} terms")
pairs, _ = to_pairs(P5)
with open("p5_pool.pkl", "wb") as fh: pickle.dump([None, None] + pairs, fh)
print("wrote p5_pool.pkl (checkpoint format of cut_ground.run: [⊥, ⊤, F(⊥,⊤), ...])")
