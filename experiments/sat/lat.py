# Lattice utilities + exact SAT encoding of the Mordor realizability CSP.
import itertools
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

class Lattice:
    def __init__(self, n, leq, name=""):
        self.n, self.leq, self.name = n, leq, name
        self.bot = next(x for x in range(n) if all(leq[x][y] for y in range(n)))
        self.top = next(x for x in range(n) if all(leq[y][x] for y in range(n)))
        self.covers = [(x, y) for x in range(n) for y in range(n)
                       if x != y and leq[x][y] and not any(z not in (x, y) and leq[x][z] and leq[z][y] for z in range(n))]
        # check lattice: joins exist
        for x in range(n):
            for y in range(n):
                ubs = [z for z in range(n) if leq[x][z] and leq[y][z]]
                j = [z for z in ubs if all(leq[z][w] for w in ubs)]
                assert len(j) == 1, (name, x, y)
    def interval(self, z, w):
        els = [x for x in range(self.n) if self.leq[z][x] and self.leq[x][w]]
        return Lattice(len(els), [[self.leq[p][q] for q in els] for p in els], f"{self.name}[{z},{w}]")

def from_relation(n, rel, name=""):
    leq = [[x == y for y in range(n)] for x in range(n)]
    for x, y in rel: leq[x][y] = True
    for k in range(n):
        for i in range(n):
            if leq[i][k]:
                for j in range(n):
                    if leq[k][j]: leq[i][j] = True
    return Lattice(n, leq, name)

def chain(n): return from_relation(n, [(i, i+1) for i in range(n-1)], f"C{n}")
def E(k):  # bot=0, top=1, column i: 2+3i < 3+3i < 4+3i
    rel = []
    for i in range(k):
        a, b, c = 2+3*i, 3+3*i, 4+3*i
        rel += [(0, a), (a, b), (b, c), (c, 1)]
    return from_relation(2+3*k, rel, f"E{k}")
def powerset(k):
    n = 1 << k
    return from_relation(n, [(x, y) for x in range(n) for y in range(n) if x & y == x], f"B{k}")
def product(L1, L2):
    els = [(p, q) for p in range(L1.n) for q in range(L2.n)]
    leq = [[L1.leq[a][c] and L2.leq[b][d] for (c, d) in els] for (a, b) in els]
    return Lattice(len(els), leq, f"{L1.name}x{L2.name}")
def M(k): return from_relation(k+2, [(0, i) for i in range(2, k+2)] + [(i, 1) for i in range(2, k+2)], f"M{k}")
def N5(): return from_relation(5, [(0, 2), (2, 3), (3, 1), (0, 4), (4, 1)], "N5")

class Enc:
    """Realizability CSP (pins + strong exclusions + monotonicity) as CNF, one-hot."""
    def __init__(self, L, polar=True, commute=True, extra=None):
        self.L = L; n = L.n; self.nv = 0; self.cl = []
        nv = lambda: self._new()
        self.F = [[[self._new() for v in range(n)] for y in range(n)] for x in range(n)]
        self.A = [[self._new() for v in range(n)] for x in range(n)]
        self.B = [[self._new() for v in range(n)] for x in range(n)]
        for x in range(n):
            for y in range(n): self.exactly_one(self.F[x][y])
            self.exactly_one(self.A[x]); self.exactly_one(self.B[x])
        leq = L.leq
        # monotonicity along cover arcs in both coordinates
        for (x, x2) in L.covers:
            for y in range(n):
                for p in range(n):
                    for q in range(n):
                        if not leq[p][q]:
                            self.cl.append([-self.F[x][y][p], -self.F[x2][y][q]])
                            self.cl.append([-self.F[y][x][p], -self.F[y][x2][q]])
        for x in range(n):
            for v in range(n):
                self.cl.append([-self.A[x][v], self.F[x][v][v]])          # pin F(x,a(x))=a(x)
                self.cl.append([-self.B[x][v], self.F[v][x][v]])          # pin F(b(y),y)=b(y)
                for y in range(n):
                    if not leq[y][v]:  # y not<= a(x)  => F(x,y) != y
                        self.cl.append([-self.A[x][v], -self.F[x][y][y]])
                    if not leq[v][y]:  # x=y here is the column variable; handled below
                        pass
        for y in range(n):
            for u in range(n):
                for x in range(n):
                    if not leq[u][x]:  # b(y)=u not<= x => F(x,y) != x
                        self.cl.append([-self.B[y][u], -self.F[x][y][x]])
        if polar:
            b, t = L.bot, L.top
            self.cl += [[self.A[b][b]], [self.A[t][t]], [self.B[b][b]], [self.B[t][t]]]
        if commute:
            C = [[self._new() for _ in range(n)] for _ in range(n)]
            D = [[self._new() for _ in range(n)] for _ in range(n)]
            for x in range(n):
                self.exactly_one(C[x]); self.exactly_one(D[x])
                for u in range(n):
                    for w in range(n):
                        self.cl.append([-self.B[x][u], -self.A[u][w], C[x][w]])
                        self.cl.append([-self.A[x][u], -self.B[u][w], D[x][w]])
                for w in range(n):
                    self.cl.append([-C[x][w], D[x][w]]); self.cl.append([C[x][w], -D[x][w]])
        if extra: extra(self)
    def _new(self):
        self.nv += 1; return self.nv
    def exactly_one(self, lits):
        self.cl.append(list(lits))
        for i in range(len(lits)):
            for j in range(i+1, len(lits)):
                self.cl.append([-lits[i], -lits[j]])
    def solver(self):
        s = Cadical153(bootstrap_with=self.cl); return s
    def decode(self, model):
        ms = set(l for l in model if l > 0); n = self.L.n
        F = [[next(v for v in range(n) if self.F[x][y][v] in ms) for y in range(n)] for x in range(n)]
        a = [next(v for v in range(n) if self.A[x][v] in ms) for x in range(n)]
        b = [next(v for v in range(n) if self.B[x][v] in ms) for x in range(n)]
        return F, a, b

# ---- independent semantic checker (no CSP) ----
def fixpoints(L, f): return [x for x in range(L.n) if f(x) == x]
def least(L, S): return next(x for x in S if all(L.leq[x][y] for y in S))
def greatest(L, S): return next(x for x in S if all(L.leq[y][x] for y in S))
def derived(L, F):
    n = L.n
    a = [greatest(L, fixpoints(L, lambda y: F[x][y])) for x in range(n)]
    b = [least(L, fixpoints(L, lambda x: F[x][y])) for y in range(n)]
    return a, b
def monotone(L, F):
    return all(L.leq[F[x][y]][F[x2][y]] and L.leq[F[y][x]][F[y][x2]] for (x, x2) in L.covers for y in range(L.n))
def semantic(L, F):
    a, b = derived(L, F)
    m = least(L, fixpoints(L, lambda x: a[x])); nn = greatest(L, fixpoints(L, lambda y: b[y]))
    comm = all(a[b[x]] == b[a[x]] for x in range(L.n))
    return a, b, m, nn, comm

# ---- families and helpers shared by the round-22 scripts ----
def moore_family(k):
    """All lattices with <= k join-irreducibles, up to isomorphism, as closure systems on a k-set."""
    full = (1 << k) - 1; seen = set()
    for mask in range(1 << full):
        fam = [i for i in range(full) if mask >> i & 1] + [full]; fs = set(fam)
        if any((x & y) not in fs for x in fam for y in fam): continue
        c = min(tuple(sorted(sum(1 << p[i] for i in range(k) if s >> i & 1) for s in fam))
                for p in itertools.permutations(range(k)))
        if c in seen: continue
        seen.add(c); els = sorted(fam)
        yield Lattice(len(els), [[(p & q) == p for q in els] for p in els], "moore" + str(els))

def closure_lattice(gens, k):
    full = (1 << k) - 1; fam = {full} | set(gens); ch = True
    while ch:
        ch = False
        for p in list(fam):
            for q in list(fam):
                if (p & q) not in fam: fam.add(p & q); ch = True
    els = sorted(fam)
    return Lattice(len(els), [[(p & q) == p for q in els] for p in els], "closure" + str(els))

def downsets(L):
    n = L.n
    for mask in range(1, (1 << n) - 1):
        if all((mask >> y & 1) for x in range(n) if mask >> x & 1 for y in range(n) if L.leq[y][x]):
            yield {x for x in range(n) if mask >> x & 1}

def D_cols(k):  # height-3 column lattice: k columns of 2-chains
    rel = []
    for i in range(k): rel += [(0, 2+2*i), (2+2*i, 3+2*i), (3+2*i, 1)]
    return from_relation(2+2*k, rel, f"D{k}")

def add_composites(e):
    """C[x] = a(b(x)), D[x] = b(a(x)) as one-hot vectors; returns (C, D)."""
    n = e.L.n
    C = [[e._new() for _ in range(n)] for _ in range(n)]; D = [[e._new() for _ in range(n)] for _ in range(n)]
    for x in range(n):
        e.exactly_one(C[x]); e.exactly_one(D[x])
        for u in range(n):
            for w in range(n):
                e.cl.append([-e.B[x][u], -e.A[u][w], C[x][w]]); e.cl.append([-e.A[x][u], -e.B[u][w], D[x][w]])
    return C, D

def polar_violator(L, relation="commute"):
    """relation: 'commute' (a.b = b.a), 'ba<=ab' (b.a <= a.b pointwise), 'ab<=ba'.
    Returns a semantically re-checked violator F (m != n) or None."""
    def extra(e):
        if relation == "commute": return
        C, D = add_composites(e)
        for x in range(L.n):
            for p in range(L.n):
                for q in range(L.n):
                    # C = a.b, D = b.a ; 'ba<=ab' forbids D[x]=q, C[x]=p with not q<=p
                    bad = (not L.leq[q][p]) if relation == "ba<=ab" else (not L.leq[p][q])
                    if bad: e.cl.append([-C[x][p], -D[x][q]])
    e = Enc(L, polar=True, commute=(relation == "commute"), extra=extra); s = e.solver()
    if not s.solve(): return None
    F, a, b = e.decode(s.get_model()); a2, b2, m, nn, c = semantic(L, F)
    assert monotone(L, F) and (a2, b2) == (a, b) and m != nn
    assert (relation != "commute") or c
    return F

def CL_holds(L, relation="commute"):
    """CL(L) iff no interval [z,w] (z<w) carries a realizable polar pair (interval-quantified Pair-Level Reduction)."""
    for z in range(L.n):
        for w in range(L.n):
            if z != w and L.leq[z][w]:
                I = L.interval(z, w)
                if I.n >= 3 and polar_violator(I, relation) is not None: return False, (z, w)
    return True, None
