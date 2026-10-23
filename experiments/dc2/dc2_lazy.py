"""Lazy (CEGAR) check of the depth-2 closure conjecture DC2 on M_ω² × C_n (§34.3z⁶–⁷).

Instance (k, m), sound relaxation of the depth-2 instance:
  master  D on points over S1 = {⊥, ⊤} ∪ L1 (|L1| = k, every L1 atom occurs at a level-0 cell), and F on all pairs
          over S1: values at level-0 pairs in {⊥, ⊤} ∪ L1, at level-1 pairs in {⊥, ⊤} ∪ L1 ∪ L2 (pool of m atoms,
          unused allowed); monotone and witness-free on cells.
  block b for each L2 atom b used at a cell: points over S1 ∪ {b}; pairs that involve b get values in
          {⊥, ⊤} ∪ L1 ∪ {b, o}; master values are projected by π_b (other L2 atoms ↦ o).  Pairs with two distinct
          L2 atoms are dropped.
Soundness: a real witness-free (F, D) with |L1| = k and |L2| ≤ m maps to a master model (non-cell pairs valued ⊥),
and for each b its restriction to cells over S1 ∪ {b}, composed with π_b (atoms ∉ L1 ∪ {b} ↦ o), is a block model:
π_b maps atoms to atoms, hence is monotone, and o ≤ x_i ⟺ x_i = ⊤ ⟺ v ≤ x_i for every coordinate x_i of a block
cell and every atom v ∉ L1 ∪ {b}.  A block core is a conjunction of projected master facts; its negation, for every
b′ in the pool, guarded by "b′ is used", is a valid master lemma.  Master UNSAT ⟹ no counterexample with these
(k, ≤ m)."""
import itertools, sys, time
from pysat.solvers import Cadical153

B, T, O = 'b', 't', 'o'
cle = lambda u, v: u == v or u == B or v == T

class Inst:
    def __init__(self, k, m, n):
        self.k, self.m, self.n = k, m, n
        self.L1 = [('a', i) for i in range(k)]
        self.L2 = [('c', j) for j in range(m)]
        self.c1 = [B, T] + self.L1
        self.P1 = [(u, v, l) for u in self.c1 for v in self.c1 for l in range(n)]

    @staticmethod
    def ple(p, q): return cle(p[0], q[0]) and cle(p[1], q[1]) and p[2] <= q[2]

    def covers(self, p, coords):
        out = []
        for i in range(2):
            for c in coords:
                if c != p[i] and cle(p[i], c) and not any(e not in (p[i], c) and cle(p[i], e) and cle(e, c) for e in coords):
                    q = list(p); q[i] = c; out.append(tuple(q))
        if p[2] + 1 < self.n: out.append((p[0], p[1], p[2] + 1))
        return out

class Vars:
    def __init__(self): self.d = {}; self.n = 0
    def __call__(self, *k):
        if k not in self.d: self.n += 1; self.d[k] = self.n
        return self.d[k]

_AMO = [0]

def onehot(S, lits, V=None):
    """exactly one of lits; pairwise at-most-one for short lists, sequential counter (aux vars from V) otherwise"""
    S.add_clause(lits)
    if V is None or len(lits) <= 6:
        for a, b in itertools.combinations(lits, 2): S.add_clause([-a, -b])
        return
    _AMO[0] += 1; tag = _AMO[0]
    prev = None
    for j, x in enumerate(lits):
        sj = V('amo', tag, j)                      # some literal among lits[0..j] is true
        S.add_clause([-x, sj])
        if prev is not None:
            S.add_clause([-prev, sj]); S.add_clause([-prev, -x])
        prev = sj

def pair_constraints(S, V, x, y, dom, dmx, dmy, wit=True):
    """one-hot values and witness-freeness at pair (x, y), guarded by cell(x, y)"""
    for i in range(2): onehot(S, [V('v', x, y, i, a) for a in dom], V)
    onehot(S, [V('v', x, y, 2, l) for l in range(len(LAYERS))])
    if not wit: return
    g = [-dmx, dmy]
    if WIT != 'hi': S.add_clause(g + [V('v', x, y, i, a) for i in range(2) for a in dom if not cle(a, x[i])] + [V('v', x, y, 2, l) for l in LAYERS if l > x[2]])
    if WIT != 'lo': S.add_clause(g + [V('v', x, y, i, a) for i in range(2) for a in dom if not cle(y[i], a)] + [V('v', x, y, 2, l) for l in LAYERS if l < y[2]])

def mono(S, V, c1, c2, dom1, dom2, guard):
    """F(c1) ≤ F(c2) under guard (a list of literals whose falsity enables the constraint)"""
    for i in range(2):
        for a in dom1:
            if a == B: continue
            S.add_clause(guard + [-V('v', *c1, i, a), V('v', *c2, i, T)] + ([V('v', *c2, i, a)] if a in dom2 and a != T else []))
    for l in LAYERS:
        for l2 in LAYERS:
            if l2 < l: S.add_clause(guard + [-V('v', *c1, 2, l), -V('v', *c2, 2, l2)])

def precedence(S, V, tag, positions, atoms):
    """value-precedence symmetry breaking: atom j occurs at a position only after atom j-1 occurred strictly earlier.
    positions: list of (x, y, i); sound whenever all constraints are invariant under permuting `atoms`."""
    for j, a in enumerate(atoms):
        prev = None
        for t, (x, y, i) in enumerate(positions):
            occ = V('v', x, y, i, a)
            u = V('prec', tag, j, t)              # atom j occurs at some position ≤ t
            S.add_clause([-occ, u])
            if prev is not None: S.add_clause([-prev, u])
            S.add_clause([-u, occ] + ([prev] if prev is not None else []))
            if j > 0:
                S.add_clause([-occ] + ([V('prec', tag, j - 1, t - 1)] if t > 0 else []))
            prev = u

LAYERS = []
WIT = 'both'      # sanity switch: 'lo' / 'hi' keeps only one half of the witness condition
SKIP_BLOCKS = False
MINIMIZE = True
PREC_L2 = True    # value precedence on L2 (memory-heavy); False keeps only the used-prefix symmetry break
BLOCK_MAXL1 = None  # drop block pairs with more than this many distinct L1 atoms (sound relaxation of blocks)
MAXL1 = None      # drop pairs (master and block) with more than MAXL1 distinct L1 atoms (sound relaxation)
DUMP = None
ALL_BLOCKS = True
SYM = True        # close native lemmas under permutations of L1
DPAT = None       # optional dict point -> bool fixing D on level-0 points
CARRY0 = None     # predicate on closed level-0 pairs whose value must contain an L1 atom (case split)
ZERO0 = None      # predicate on level-0 pairs forced atom-free (case split): domain {⊥, ⊤}
SHUFFLE = None    # random.Random for randomized core minimization order
SEL1 = None       # predicate: level-1 pairs that get a closure selector (core extraction)
SEL0 = False      # selectors on level-0 closure (core extraction)
CLOSED1 = None    # predicate on level-1 pairs; None = all closed.  Open level-1 pairs get + o; L2 = atoms at closed ones.
CLOSED0 = None    # predicate on level-0 pairs; None = all closed.  Open level-0 pairs get the full domain + o.

def build_master(I):
    S = Cadical153(); V = Vars()
    dm = lambda p: V('D', p)
    for p in I.P1:
        for q in I.covers(p, I.c1): S.add_clause([-dm(q), dm(p)])
    S.add_clause([dm((B, B, 0))]); S.add_clause([-dm((T, T, I.n - 1))])
    if DPAT:
        for p, v in DPAT.items(): S.add_clause([dm(p) if v else -dm(p)])
    lev0 = lambda p: p[0] in (B, T) and p[1] in (B, T)
    def dom(x, y):
        if not (lev0(x) and lev0(y)):
            if SEL1 is not None and SEL1(x, y): return [B, T] + I.L1 + I.L2 + [O]
            return [B, T] + I.L1 + I.L2 + ([] if CLOSED1 is None or CLOSED1(x, y) else [O])
        if ZERO0 is not None and ZERO0(x, y): return [B, T]
        if SEL0: return [B, T] + I.L1 + I.L2 + [O]
        if CLOSED0 is None or CLOSED0(x, y): return [B, T] + I.L1
        return [B, T] + I.L1 + I.L2 + [O]
    nl1 = lambda *ps: len({t for p in ps for t in p[:2] if t not in (B, T) and t[0] == 'a'})
    pairs = [(x, y) for x in I.P1 for y in I.P1 if not I.ple(y, x) and (MAXL1 is None or nl1(x, y) <= MAXL1)]
    pset = set(pairs)
    for x, y in pairs:
        pair_constraints(S, V, x, y, dom(x, y), dm(x), dm(y))
        for x2 in I.covers(x, I.c1):
            if (x2, y) in pset: mono(S, V, (x, y), (x2, y), dom(x, y), dom(x2, y), [-dm(x2), dm(y)])
        for y2 in I.covers(y, I.c1):
            if (x, y2) in pset: mono(S, V, (x, y), (x, y2), dom(x, y), dom(x, y2), [-dm(x), dm(y)])
    # cell indicators, L1 atoms used at level-0 cells (exact k), 'used' and 'isL2' indicators
    for x, y in pairs:
        cv = V('cell', x, y)
        S.add_clause([-cv, dm(x)]); S.add_clause([-cv, -dm(y)]); S.add_clause([cv, -dm(x), dm(y)])
    for a in I.L1:
        lits = []
        for x, y in pairs:
            if lev0(x) and lev0(y) and (SEL0 or CLOSED0 is None or CLOSED0(x, y)):
                for i in range(2):
                    z = V('u1', a, x, y, i); lits.append(z)
                    if SEL0: S.add_clause([-z, V('sel0', x, y)])
                    S.add_clause([-z, V('cell', x, y)]); S.add_clause([-z, V('v', x, y, i, a)])
        S.add_clause(lits)
    for b in I.L2:
        u = V('used', b); lits = []
        for x, y in pairs:
            if not (lev0(x) and lev0(y)) and ((SEL1 is not None and SEL1(x, y)) or CLOSED1 is None or CLOSED1(x, y)):
                for i in range(2):
                    z = V('u2', b, x, y, i); lits.append(z)
                    if SEL1 is not None and SEL1(x, y): S.add_clause([-z, V('sel1', x, y)])
                    S.add_clause([-z, V('cell', x, y)]); S.add_clause([-z, V('v', x, y, i, b)])
                    S.add_clause([z, -V('cell', x, y), -V('v', x, y, i, b)])
        for z in lits: S.add_clause([-z, u])
        S.add_clause([-u] + lits)
    for x, y in pairs:
        if I.L2[0:1] and I.L2[0] not in dom(x, y): continue
        for i in range(2):
            z = V('isL2', x, y, i)
            S.add_clause([-z] + [V('v', x, y, i, b) for b in I.L2])
            for b in I.L2: S.add_clause([z, -V('v', x, y, i, b)])
    if CARRY0 is not None:
        for x, y in pairs:
            if lev0(x) and lev0(y) and CARRY0(x, y):
                S.add_clause([-V('cell', x, y)] + [V('v', x, y, i, a) for i in range(2) for a in I.L1])
    if SEL1 is not None:
        for x, y in pairs:
            if not (lev0(x) and lev0(y)) and SEL1(x, y):
                for i in range(2): S.add_clause([-V('sel1', x, y), -V('v', x, y, i, O)])
    if SEL0:
        for x, y in pairs:
            if lev0(x) and lev0(y):
                for i in range(2):
                    for a in I.L2 + [O]: S.add_clause([-V('sel0', x, y), -V('v', x, y, i, a)])
    # symmetry breaking: value precedence for L1 (all pairs) and for L2 (level-1 pairs)
    allpos = [(x, y, i) for x, y in pairs for i in range(2)]
    precedence(S, V, 'L1', allpos, I.L1)
    if PREC_L2: precedence(S, V, 'L2', [(x, y, i) for x, y, i in allpos if not (lev0(x) and lev0(y))], I.L2)
    for j in range(I.m - 1): S.add_clause([-V('used', I.L2[j + 1]), V('used', I.L2[j])])
    return S, V, pairs, dom

def build_block(I):
    """block for the generic L2 atom 'b'; master facts enter as assumptions on ('D', p) and projected ('v', ...)"""
    S = Cadical153(); V = Vars()
    bb = ('c', 'b')
    cb = I.c1 + [bb]
    Pb = [(u, v, l) for u in cb for v in cb for l in range(I.n)]
    dm = lambda p: V('D', p)
    for p in Pb:
        for q in I.covers(p, cb): S.add_clause([-dm(q), dm(p)])
    hasb = lambda p: bb in p[:2]
    pdom = [B, T] + I.L1 + [bb, O]
    nl1 = lambda *ps: len({t for p in ps for t in p[:2] if t not in (B, T) and t[0] == 'a'})
    lim = BLOCK_MAXL1 if BLOCK_MAXL1 is not None else MAXL1
    Pb = [p for p in Pb if lim is None or nl1(p) <= lim]
    pairs = [(x, y) for x in Pb for y in Pb if not I.ple(y, x) and (lim is None or nl1(x, y) <= lim)]
    pset = set(pairs)
    for x, y in pairs:
        pair_constraints(S, V, x, y, pdom, dm(x), dm(y), wit=hasb(x) or hasb(y))
    for x, y in pairs:
        for x2 in I.covers(x, cb):
            if (x2, y) in pset and (hasb(x) or hasb(y) or hasb(x2)): mono(S, V, (x, y), (x2, y), pdom, pdom, [-dm(x2), dm(y)])
        for y2 in I.covers(y, cb):
            if (x, y2) in pset and (hasb(x) or hasb(y) or hasb(y2)): mono(S, V, (x, y), (x, y2), pdom, pdom, [-dm(x), dm(y)])
    return S, V, bb

def sym_maps(src, dst, cap=24):
    """injective maps src → dst (all of them, up to cap)"""
    out = []
    for img in itertools.permutations(dst, len(src)):
        out.append(dict(zip(src, img)))
        if len(out) >= cap: break
    return out

def add_lemma(S, V, I, dom, core, amap, bb):
    """Add, for every pool atom b2, the master lemma ¬(core) with L1 atoms renamed by amap.  A projected value 'o'
    at (cell, coord) stands for: an L1 atom outside the image of amap, an L2 atom ≠ b2, or o itself — one clause per
    combination of alternatives (CNF of the negated disjunction)."""
    mp = lambda t: amap.get(t, t)
    mpt = lambda p: tuple(mp(t) for t in p[:2]) + (p[2],)
    img = set(amap.values())
    for b2 in I.L2:
        base = [-V('used', b2)]
        alts = []
        for f in core:
            if f[0] == 'D':
                base.append(-V('D', mpt(f[1])) if f[2] else V('D', mpt(f[1])))
                continue
            _, x, y, i, pa = f
            x, y = mpt(x), mpt(y)
            base.append(-V('cell', x, y))
            if i == 2: base.append(-V('v', x, y, i, pa))
            elif pa == bb: base.append(-V('v', x, y, i, b2))
            elif pa == O:
                ldom = dom(x, y)
                choice = [[-V('v', x, y, i, a)] for a in I.L1 if a not in img]
                if any(b in ldom for b in I.L2): choice.append([-V('isL2', x, y, i), V('v', x, y, i, b2)])
                if O in ldom: choice.append([-V('v', x, y, i, O)])
                alts.append(choice)
            else: base.append(-V('v', x, y, i, mp(pa)))
        for combo in itertools.product(*alts):
            S.add_clause(base + [l for c in combo for l in c])

def run(k, m, n, verbose=True, maxit=100000, preload=()):
    global LAYERS
    LAYERS = list(range(n))
    I = Inst(k, m, n)
    S, V, pairs, dom = build_master(I)
    BS, BV, bb = build_block(I)
    it = 0; lemmas = 0; t0 = time.time(); coresz = []
    bb0 = ('c', 'b')
    for k0, cores in preload:                       # lift cores from instances with k0 ≤ k L1 atoms
        src = [('a', i) for i in range(k0)]
        for amap in sym_maps(src, I.L1, cap=10**6):
            for core in cores: add_lemma(S, V, I, dom, core, amap, bb0)
    lev0 = lambda p: p[0] in (B, T) and p[1] in (B, T)
    while True:
        it += 1
        if not S.solve():
            if verbose: print(f"k={k} m={m} n={n}: UNSAT after {it} iterations, {lemmas} lemma families, {time.time()-t0:.0f}s", flush=True)
            return False
        M = set(l for l in S.get_model() if l > 0)
        val = {}
        for x, y in pairs:
            for i in range(3):
                for a in (dom(x, y) if i < 2 else LAYERS):
                    if V('v', x, y, i, a) in M: val[(x, y, i)] = a
        Dm = {p: V('D', p) in M for p in I.P1}
        cellm = {(x, y): Dm[x] and not Dm[y] for x, y in pairs}
        used = [b for b in I.L2 if V('used', b) in M]
        found = False
        for b in ([] if SKIP_BLOCKS else used):
            # assumptions: D on P1, projected values on P1 pairs that are cells (non-cells are irrelevant to the block)
            ass = {}
            for p in I.P1: ass[BV('D', p) if Dm[p] else -BV('D', p)] = ('D', p, Dm[p])
            for x, y in pairs:
                if not cellm[(x, y)]: continue
                for i in range(2):
                    a = val[(x, y, i)]
                    pa = bb if a == b else (O if a in I.L2 else a)
                    ass[BV('v', x, y, i, pa)] = ('v', x, y, i, pa)
                ass[BV('v', x, y, 2, val[(x, y, 2)])] = ('v', x, y, 2, val[(x, y, 2)])
            if BS.solve(assumptions=list(ass)): continue
            cur = list(BS.get_core())
            if MINIMIZE:
                i = 0
                while i < len(cur):
                    trial = cur[:i] + cur[i + 1:]
                    if not BS.solve(assumptions=trial):
                        c = set(BS.get_core()); cur = [l for l in trial if l in c]
                    else: i += 1
            core = [ass[l] for l in cur]
            found = True; lemmas += 1
            coresz.append(len(core))
            if DUMP is not None: DUMP.append(core)
            for amap in (sym_maps(I.L1, I.L1) if SYM else [{a: a for a in I.L1}]):
                add_lemma(S, V, I, dom, core, amap, bb)
            if not ALL_BLOCKS: break
        if not found:
            if verbose: print(f"k={k} m={m} n={n}: SAT (relaxed) after {it} iterations; used L2 = {len(used)}", flush=True)
            return True
        if verbose and it % 50 == 0: print(f"  it={it} lemmas={lemmas} avg core={sum(coresz[-50:])/max(1,len(coresz[-50:])):.1f} {time.time()-t0:.0f}s", flush=True)

if __name__ == "__main__":
    n = int(sys.argv[1])
    for k, m in [tuple(map(int, a.split(','))) for a in sys.argv[2:]]:
        run(k, m, n)
