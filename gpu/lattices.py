"""lattices.py: the static (Mu) side of the Mordor GPU census. Pure numpy/python, no torch.

A lattice is a finite bounded poset given by its order matrix; everything the engine needs is derived here once:
covers, join/meet tables, a linear extension, down-sets, the monotone self-maps Mon(L) and the exact number of
monotone bifunctions F : L×L → L (the census total, used as a prediction and as an L1 check).

Spec strings (see `parse`): C5, M3, N5, B3, E2, D3, Pi4, C3xC3, N5xC2, all6 (every lattice with exactly 6 elements,
up to isomorphism), all<=6. Elements are 0..n-1; the constructors put ⊥ first and ⊤ last where convenient, but
consumers must use L.bot / L.top."""
import itertools, functools
import numpy as np


class Lat:
    def __init__(self, leq, name):
        leq = np.asarray(leq, dtype=bool); n = leq.shape[0]
        self.n, self.leq, self.name = n, leq, name
        assert (np.diag(leq)).all() and not (leq & leq.T & ~np.eye(n, dtype=bool)).any(), f"{name}: not a partial order"
        assert ((leq.astype(np.int64) @ leq.astype(np.int64) > 0) <= leq).all(), f"{name}: not transitive"
        self.bot = int(np.flatnonzero(leq.all(1))[0]); self.top = int(np.flatnonzero(leq.all(0))[0])
        lt = leq & ~np.eye(n, dtype=bool)
        self.covers = [(x, y) for x in range(n) for y in range(n)
                       if lt[x, y] and not (lt[x] & lt[:, y]).any()]                 # x ⋖ y
        self.join = np.zeros((n, n), dtype=np.int64); self.meet = np.zeros((n, n), dtype=np.int64)
        for x in range(n):
            for y in range(n):
                ub = np.flatnonzero(leq[x] & leq[y]); lub = [z for z in ub if leq[z, ub].all()]
                lb = np.flatnonzero(leq[:, x] & leq[:, y]); glb = [z for z in lb if leq[lb, z].all()]
                assert len(lub) == 1 and len(glb) == 1, f"{name}: not a lattice at ({x},{y})"
                self.join[x, y], self.meet[x, y] = lub[0], glb[0]
        self.order = sorted(range(n), key=lambda x: (int(leq[:, x].sum()), x))    # a linear extension
        self.lower = {y: [x for (x, z) in self.covers if z == y] for y in range(n)}
        self.height = self._height()

    def _height(self):
        h = {}
        for x in self.order: h[x] = max([h[z] + 1 for z in self.lower[x]], default=0)
        return h[self.top]

    def __repr__(self): return f"Lat({self.name}, n={self.n})"

    @functools.cached_property
    def mon(self):
        """All monotone self-maps of L as an (M, n) int64 array (rows in lexicographic order of the linear extension)."""
        out, f = [], [0] * self.n
        def rec(i):
            if i == self.n: out.append(list(f)); return
            x = self.order[i]
            for v in range(self.n):
                if all(self.leq[f[z], v] for z in self.lower[x]): f[x] = v; rec(i + 1)
        rec(0)
        return np.asarray(out, dtype=np.int64)

    @functools.cached_property
    def n_bifunctions(self):
        return self.count_bifunctions()

    def count_bifunctions(self, max_states=2_000_000):
        """Exact number of monotone F : L×L → L, i.e. monotone maps x ↦ F(x, ·) from L into Mon(L) (pointwise order).
        DP along the linear extension; state = rows of elements that still have an unprocessed upper cover."""
        Mon = self.mon; M = len(Mon)
        rle = (self.leq[Mon[:, None, :], Mon[None, :, :]]).all(2)                  # (M, M): r ≤ s pointwise
        order = self.order; pos = {x: i for i, x in enumerate(order)}
        last_use = {x: max([pos[y] for (z, y) in self.covers if z == x], default=-1) for x in order}
        states = {(): 1}; live = []                                                # live: elements in the state, in order
        for i, x in enumerate(order):
            need = [live.index(z) for z in self.lower[x]]
            nlive = live + [x]; keep = [j for j, z in enumerate(nlive) if last_use[z] > i]
            new = {}
            for st, c in states.items():
                ok = np.ones(M, dtype=bool)
                for j in need: ok &= rle[st[j]]
                for r in np.flatnonzero(ok):
                    key = tuple((st + (int(r),))[j] for j in keep)
                    new[key] = new.get(key, 0) + c
            states, live = new, [nlive[j] for j in keep]
            if len(states) > max_states: return None                               # too wide for this DP
        return sum(states.values())


def from_relation(n, rel, name):
    leq = np.eye(n, dtype=bool)
    for x, y in rel: leq[x, y] = True
    for k in range(n): leq |= leq[:, k:k + 1] & leq[k:k + 1, :]
    return Lat(leq, name)


def chain(n): return from_relation(n, [(i, i + 1) for i in range(n - 1)], f"C{n}")
def M(k): return from_relation(k + 2, [(0, i) for i in range(1, k + 1)] + [(i, k + 1) for i in range(1, k + 1)], f"M{k}")
def N5(): return from_relation(5, [(0, 1), (1, 2), (2, 4), (0, 3), (3, 4)], "N5")
def B(k):
    n = 1 << k; return Lat([[x & y == x for y in range(n)] for x in range(n)], f"B{k}")
def E(k):   # ⊥ = 0, columns of 3-chains, ⊤ = last  (the log's E_k)
    n = 3 * k + 2; rel = []
    for i in range(k): a = 1 + 3 * i; rel += [(0, a), (a, a + 1), (a + 1, a + 2), (a + 2, n - 1)]
    return from_relation(n, rel, f"E{k}")
def D(k):   # ⊥, columns of 2-chains, ⊤  (height-3 column lattices)
    n = 2 * k + 2; rel = []
    for i in range(k): a = 1 + 2 * i; rel += [(0, a), (a, a + 1), (a + 1, n - 1)]
    return from_relation(n, rel, f"D{k}")
def product(A, Bl):
    els = [(p, q) for p in range(A.n) for q in range(Bl.n)]
    return Lat([[A.leq[a, c] and Bl.leq[b, d] for (c, d) in els] for (a, b) in els], f"{A.name}x{Bl.name}")
def Pi(k):
    def parts(s):
        if not s: yield []; return
        for p in parts(s[1:]):
            yield [[s[0]]] + p
            for i in range(len(p)): yield p[:i] + [[s[0]] + p[i]] + p[i + 1:]
    P = sorted((frozenset(frozenset(b) for b in p) for p in parts(list(range(k)))), key=lambda p: -len(p))
    return Lat([[all(any(b <= c for c in q) for b in p) for q in P] for p in P], f"Pi{k}")


def all_lattices(n):
    """Every lattice with exactly n ≥ 2 elements, up to isomorphism (bounded posets on n−2 inner elements, filtered)."""
    k = n - 2; seen, out = set(), []
    pairs = [(i, j) for i in range(k) for j in range(i + 1, k)]
    for mask in range(1 << len(pairs)):
        rel = np.eye(k, dtype=bool)
        for t, (i, j) in enumerate(pairs):
            if mask >> t & 1: rel[i, j] = True
        if ((rel.astype(int) @ rel.astype(int) > 0) & ~rel).any(): continue
        leq = np.zeros((n, n), dtype=bool); leq[0, :] = True; leq[:, n - 1] = True; leq[1:n - 1, 1:n - 1] = rel
        try: L = Lat(leq, "")
        except AssertionError: continue
        canon = min(tuple(rel[np.ix_(p, p)].ravel()) for p in itertools.permutations(range(k)))
        if canon in seen: continue
        seen.add(canon); L.name = f"L{n}_{len(out)}"; out.append(L)
    return out


def parse(spec):
    """'C5', 'M3', 'N5', 'B3', 'E2', 'D3', 'Pi4', products 'C3xC3', 'L6_12' (the names all_lattices gives), families
    'all6' and 'all<=6' (a list)."""
    if spec.startswith('all<='): return [L for n in range(3, int(spec[5:]) + 1) for L in all_lattices(n)]
    if spec.startswith('all'): return all_lattices(int(spec[3:]))
    if 'x' in spec:
        parts = [parse(s) for s in spec.split('x')]
        L = parts[0]
        for Q in parts[1:]: L = product(L, Q)
        return L
    if spec[0] == 'L' and '_' in spec:                                            # 'L6_12': all_lattices(6)[12]
        n, i = map(int, spec[1:].split('_')); return all_lattices(n)[i]
    if spec == 'N5': return N5()
    if spec.startswith('Pi'): return Pi(int(spec[2:]))
    kind, k = spec[0], int(spec[1:])
    return {'C': chain, 'M': M, 'B': B, 'E': E, 'D': D}[kind](k)
