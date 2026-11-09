"""Weak Veinott monotonicity and pinning of the interface windows (log §34.3z¹²⁶; brief Part B).

Instances as in selection_falsify.py (crossing interval [w, v], G witness-free on the crossing cells of S, all windows
nonempty). For p < q in S (product order) weak Veinott (Kukushkin 2009) asks: for all z ∈ W(q), t ∈ W(p),
z ∨ t ∈ W(q) or z ∧ t ∈ W(p). Internal pin: crossing cells (x, y), (a₁, y), (a₂, y) of S with x ≤ a₁, a₂, a₁ ∥ a₂,
and z₁ ∧ z₂ ≤ x for all z₁ ∈ W(a₁, y), z₂ ∈ W(a₂, y) (Lean `InterfaceTrace.internal_pin`). Pinned windows: v is added
to the window of each upper cell of an internal pin when v is admissible there (traces, safety).
Dual pin: (x, b₁), (x, b₂) ≤ (x, y), b₁ ∥ b₂, z₁ ∨ z₂ ≥ y for all admissible values (forces w on a lower cell);
pinned windows then also admit w on those lower cells.
General pins (Lean `general_pin`, `general_pin_dual`) replace both: p ≤ q₁, q₂ with no admissible lower value below
any admissible meet z₁ ∧ z₂ (z_i ≠ v), dually for joins; pinned windows add v (resp. w) where admissible.
Reported per instance class: weak Veinott, selectable, internal pin present; and after pinning: selectable, weak
Veinott.
  python3 veinott_audit.py SEED N
"""
import sys, random, itertools, json, collections
from z3 import *
sys.path.insert(0, '../separation')
import separator_stages as ss
from selection_falsify import chain, B2, C4

def windows(L, G, D, w, v):
    n = L.n; le = L.le; cells = [(x, y) for x in range(n) for y in range(n)]
    I = lambda z: le[w][z] and le[z][v]
    S = [p for p in cells if I(G[p[0]][p[1]])]; Sset = set(S)
    cross = lambda p: D[p[0]] and not D[p[1]]
    for (x, y) in S:
        if cross((x, y)) and (le[G[x][y]][x] or le[y][G[x][y]]): return None
    if not any(cross(p) for p in S): return None
    pl = lambda p, q: le[p[0]][q[0]] and le[p[1]][q[1]]
    def lo(p):
        z = L.bot
        for q in cells:
            if q not in Sset and pl(q, p): z = L.join[z][G[q[0]][q[1]]]
        return z
    def hi(p):
        z = L.top
        for q in cells:
            if q not in Sset and pl(p, q): z = L.meet[z][G[q[0]][q[1]]]
        return z
    W = {}; tr = {}
    for p in S:
        l, u = lo(p), hi(p); tr[p] = (l, u)
        if cross(p):
            x, y = p
            W[p] = {z for z in range(n) if le[l][z] and le[z][u] and I(z) and z not in (w, v) and not le[z][x] and not le[y][z]}
        else: W[p] = {z for z in range(n) if le[l][z] and le[z][u]}
    return S, W, tr, cross, pl

def selectable(L, S, W, pl):
    n = L.n; s = Solver(); Z = {p: Int(f"z_{p[0]}_{p[1]}") for p in S}
    LE = Function('LE', IntSort(), IntSort(), BoolSort())
    for a in range(n):
        for b in range(n): s.add(LE(a, b) == L.le[a][b])
    for p in S: s.add(Or([Z[p] == z for z in W[p]]))
    for p in S:
        for q in S:
            if p != q and pl(p, q): s.add(LE(Z[p], Z[q]))
    return s.check() == sat

def weak_veinott(L, S, W, pl):
    for p in S:
        for q in S:
            if p == q or not pl(p, q): continue
            for z in W[q]:
                for t in W[p]:
                    if L.join[z][t] not in W[q] and L.meet[z][t] not in W[p]: return False
    return True

def internal_pins(L, S, W, cross):
    le = L.le; pins = []
    Sc = [p for p in S if cross(p)]
    for (x, y) in Sc:
        for (a1, y1), (a2, y2) in itertools.combinations([q for q in Sc if q[1] == y], 2):
            if not (le[x][a1] and le[x][a2]) or le[a1][a2] or le[a2][a1]: continue
            if all(le[L.meet[z1][z2]][x] for z1 in W[(a1, y)] for z2 in W[(a2, y)]): pins.append(((x, y), (a1, y), (a2, y)))
    return pins

def dual_pins(L, S, W, cross):
    """Order dual: crossing cells (x, b₁), (x, b₂) ≤ (x, y), b₁ ∥ b₂, with z₁ ∨ z₂ ≥ y for all admissible z_i."""
    le = L.le; pins = []
    Sc = [p for p in S if cross(p)]
    for (x, y) in Sc:
        for (x1, b1), (x2, b2) in itertools.combinations([q for q in Sc if q[0] == x], 2):
            if not (le[b1][y] and le[b2][y]) or le[b1][b2] or le[b2][b1]: continue
            if all(le[y][L.join[z1][z2]] for z1 in W[(x, b1)] for z2 in W[(x, b2)]): pins.append(((x, y), (x, b1), (x, b2)))
    return pins

def general_pins(L, S, W, pl, v, w):
    """Lean `general_pin`: p ≤ q₁, q₂ (q₁ ∥ q₂) with no t ∈ W(p) below z₁ ∧ z₂ for all z_i ∈ W(q_i) ∖ {v};
    `general_pin_dual`: q₁, q₂ ≤ p with no t ∈ W(p) above z₁ ∨ z₂ for all z_i ∈ W(q_i) ∖ {w}."""
    le = L.le; up = []; dn = []
    for p in S:
        above = [q for q in S if q != p and pl(p, q)]; below = [q for q in S if q != p and pl(q, p)]
        for q1, q2 in itertools.combinations(above, 2):
            if pl(q1, q2) or pl(q2, q1): continue
            if all(not le[t][L.meet[z1][z2]] for t in W[p] for z1 in W[q1] - {v} for z2 in W[q2] - {v}): up.append((p, q1, q2))
        for q1, q2 in itertools.combinations(below, 2):
            if pl(q1, q2) or pl(q2, q1): continue
            if all(not le[L.join[z1][z2]][t] for t in W[p] for z1 in W[q1] - {w} for z2 in W[q2] - {w}): dn.append((p, q1, q2))
    return up, dn

def run(seed, N):
    rng = random.Random(seed); tally = collections.Counter(); examples = {}
    for _ in range(N):
        if rng.random() < 0.3: L = rng.choice([C4, B2])
        else: L = ss.Lat(ss.closure_system(rng.choice([3, 4]), rng.choice([3, 5, 8]), rng))
        n = L.n
        g = {(a, b): rng.randrange(n) for a in range(n) for b in range(n) if rng.random() < 0.15}
        G = ss.make_F(L, g); D = ss.Dof(L, [i for i in range(n) if i != L.top and rng.random() < 0.35] or [0])
        for w in range(n):
            for v in range(n):
                if not (D[w] and not D[v] and L.le[w][v] and w != v): continue
                if not any(z not in (w, v) and L.le[w][z] and L.le[z][v] for z in range(n)): continue
                r = windows(L, G, D, w, v)
                if r is None: continue
                S, W, tr, cross, pl = r
                if any(not W[p] for p in S): tally['some window empty (external pin or trace-forced)'] += 1; continue
                wv = weak_veinott(L, S, W, pl); sel = selectable(L, S, W, pl); pins = internal_pins(L, S, W, cross)
                dpins = dual_pins(L, S, W, cross)
                gup, gdn = general_pins(L, S, W, pl, v, w)
                key = f"WV={wv} selectable={sel} general_pin={bool(gup or gdn)}"
                if gup or gdn:
                    W2 = {p: set(W[p]) for p in S}; rounds = 0
                    while True:                      # iterate pinning to a fixed point
                        rounds += 1; changed = False
                        for _, q1, q2 in gup:
                            for q in (q1, q2):
                                l, u = tr[q]; x, y = q
                                if v not in W2[q] and L.le[l][v] and L.le[v][u] and not L.le[v][x] and not L.le[y][v]:
                                    W2[q].add(v); changed = True
                        for _, q1, q2 in gdn:
                            for q in (q1, q2):
                                l, u = tr[q]; x, y = q
                                if w not in W2[q] and L.le[l][w] and L.le[w][u] and not L.le[w][x] and not L.le[y][w]:
                                    W2[q].add(w); changed = True
                        if rounds == 1: once = selectable(L, S, W2, pl)
                        if not changed: break
                        gup, gdn = general_pins(L, S, W2, pl, v, w)
                    key += (f" | pinned once: selectable={once}; pinned to fixed point ({rounds} rounds): "
                            f"selectable={selectable(L, S, W2, pl)} WV={weak_veinott(L, S, W2, pl)}")
                tally[key] += 1
                if key not in examples or n < examples[key][0]: examples[key] = (n, w, v, [i for i in range(n) if D[i]])
    for k, c in sorted(tally.items(), key=lambda kv: -kv[1]):
        print(f"{c:6d}  {k}" + (f"   (smallest |L| = {examples[k][0]})" if k in examples else ""))

if __name__ == '__main__':
    run(int(sys.argv[1]), int(sys.argv[2]))
