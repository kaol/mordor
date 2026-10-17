"""engine.py: batched observation of monotone bifunctions F : L×L → L on a GPU (PyTorch: ROCm/HIP, CUDA or CPU).

Two drivers share one observation function and one result monoid:
  census  exact enumeration of every monotone F (level-synchronous over a linear extension of L; a row of F is an
          element of Mon(L), and row(x) ≥ row(z) pointwise for every lower cover z ⋖ x is the only constraint).
  mcmc    heat-bath Glauber dynamics on monotone F (uniform stationary law), many chains in parallel, for lattices
          whose census is out of reach.
observe(P, F) is pure: per F it computes the derived pair a(x) = νY.F(x,Y), b(y) = μX.F(X,y) (Kleene iteration from
⊤ / ⊥, at most height+1 steps), m = μ(a), n = ν(b), the composites φ = a∘b, ψ = b∘a, the reachability closure R(F)
(least down-set containing ⊥, closed under a and b⁻¹; the Cut Lemma for F is R(F) = L), and the derived features.
Hist is a commutative monoid (counts and histograms add), so batches, checkpoints and runs merge in any order.

Arithmetic is integer gathers and comparisons; the one float matmul (down-closure) multiplies 0/1 matrices of size
n ≤ 63, exact in float32. Plan.selftest compares observe with reference.observe_one before any run.
Env: MORDOR_MEM (MiB per working set, default 1024), MORDOR_GROUP (census prefix jobs per checkpoint, default 256)."""
import os, time, json, pickle, hashlib, collections
os.environ.setdefault('PYTORCH_CUDA_ALLOC_CONF', 'expandable_segments:True')      # before torch: less fragmentation
import numpy as np
import torch
import reference

SCHEMA = 2
MEM = int(os.environ.get('MORDOR_MEM', '1024') or 1024) << 20
GROUP = int(os.environ.get('MORDOR_GROUP', '256') or 256)
WITNESS_MAX = 20
JOINT_BITS = ('comm', 'semi_ba_le_ab', 'semi_ab_le_ba', 'polar', 'meqn')          # joint key = Σ bit_i << i
TRIPS = ('trip_i1', 'trip_l1', 'trip_l2', 'trip_fusion', 'trip_i2', 'trip_lax', 'trip_pcut')   # theorems: must stay 0
VIOLS = ('cl', 'semi', 'cut')                                                     # conjectures: 0 so far


def pick_device(spec=None):
    if spec: return torch.device(spec)
    if torch.cuda.is_available(): return torch.device('cuda')                      # ROCm exposes HIP as 'cuda'
    return torch.device('cpu')


def describe(dev):
    if dev.type == 'cuda':
        be = f"HIP {torch.version.hip}" if getattr(torch.version, 'hip', None) else f"CUDA {torch.version.cuda}"
        return f"{dev} ({torch.cuda.get_device_name(dev)}, {be}, torch {torch.__version__})"
    return f"{dev} (torch {torch.__version__}, {torch.get_num_threads()} threads)"


def lattice_id(L):
    return hashlib.sha256(np.packbits(L.leq).tobytes() + bytes([L.n])).hexdigest()[:16]


class Plan:
    """The static (Mu) side on the device: everything that depends only on L."""

    def __init__(self, L, dev, census=True, mcmc=True):
        torch.backends.cuda.matmul.allow_tf32 = False
        torch.set_float32_matmul_precision('highest')
        n = L.n; self.L, self.n, self.dev = L, n, dev
        assert n <= 63, "R(F) closure uses n ≤ 63"
        T = lambda a, dt=torch.long: torch.as_tensor(np.asarray(a), dtype=dt, device=dev)
        self.leq = T(L.leq, torch.bool); self.leqTf = self.leq.T.to(torch.float32)   # (n, n)
        self.down = self.leq.T.contiguous()                                          # down[z, x] = x ≤ z
        self.join, self.meet = T(L.join), T(L.meet)
        self.idx = torch.arange(n, device=dev)
        self.bot, self.top, self.h = L.bot, L.top, L.height
        rel = np.full((n, n), reference.REL_INC, dtype=np.int64)
        rel[L.leq] = reference.REL_LT; rel[L.leq.T] = reference.REL_GT; np.fill_diagonal(rel, reference.REL_EQ)
        self.rel = T(rel)
        if census: self._census_tables()
        if mcmc: self._mcmc_tables()
        self.selftest()

    def _census_tables(self):
        L = self.L
        if L.n > 9: raise SystemExit(f"census of {L.name}: n = {L.n} is out of reach (Mon(L) too large); use mcmc")
        Mon = L.mon
        if len(Mon) > 30000: raise SystemExit(f"census of {L.name}: |Mon(L)| = {len(Mon)} is out of reach; use mcmc")
        self.Mon = torch.as_tensor(Mon, device=self.dev)                             # (M, n)
        self.rowle = torch.as_tensor(L.leq[Mon[:, None, :], Mon[None, :, :]].all(2), device=self.dev)  # (M, M)
        self.order = list(L.order); self.pos = {x: i for i, x in enumerate(self.order)}
        self.by_x = torch.as_tensor([self.pos[x] for x in range(self.n)], device=self.dev)

    def _mcmc_tables(self):
        L, n = self.L, self.n; N = n * n; BOT, TOP = N, N + 1                         # two constant cells
        up = {x: [y for (z, y) in L.covers if z == x] for x in range(n)}
        lo = [[(z * n + y) for z in L.lower[x]] + [(x * n + w) for w in L.lower[y]] for x in range(n) for y in range(n)]
        hi = [[(z * n + y) for z in up[x]] + [(x * n + w) for w in up[y]] for x in range(n) for y in range(n)]
        color = [-1] * N                                                             # greedy coloring of the cover graph
        for c in sorted(range(N), key=lambda c: -len(lo[c]) - len(hi[c])):
            used = {color[d] for d in lo[c] + hi[c]}
            color[c] = next(k for k in range(N) if k not in used)
        dl = max(1, max(map(len, lo))); du = max(1, max(map(len, hi)))
        self.colors = []
        for k in range(max(color) + 1):
            cs = [c for c in range(N) if color[c] == k]
            self.colors.append((torch.as_tensor(cs, device=self.dev),
                                torch.as_tensor([lo[c] + [BOT] * (dl - len(lo[c])) for c in cs], device=self.dev),
                                torch.as_tensor([hi[c] + [TOP] * (du - len(hi[c])) for c in cs], device=self.dev)))
        cnt = np.zeros((n, n), dtype=np.int64); il = np.zeros((n, n, n), dtype=np.int64)
        for u in range(n):
            for v in range(n):
                iv = [w for w in range(n) if L.leq[u, w] and L.leq[w, v]]
                cnt[u, v] = max(1, len(iv)); il[u, v, :len(iv)] = iv
        self.cnt = torch.as_tensor(cnt, device=self.dev); self.ilist = torch.as_tensor(il, device=self.dev)
        self.set_box(None)

    def set_box(self, box):
        """Confine every cell c = (x, y) to an interval [lo_c, hi_c] (box = (lo, hi), two (n, n) arrays, or None for
        the whole space). Monotone F inside a box form a sublattice of L^(L×L) with least element F_lo(c) = ⋁_{c' ≤ c} lo
        and greatest F_hi(c) = ⋀_{c' ≥ c} hi; the box is nonempty iff F_lo ≤ hi. The heat bath restricted to the box is
        reversible w.r.t. the uniform law on it and irreducible (descend cell by cell to F_lo), as without a box."""
        L, n = self.L, self.n; N = n * n
        lo = np.full((n, n), L.bot, dtype=np.int64) if box is None else np.asarray(box[0], dtype=np.int64)
        hi = np.full((n, n), L.top, dtype=np.int64) if box is None else np.asarray(box[1], dtype=np.int64)
        Flo, Fhi = np.empty_like(lo), np.empty_like(hi)
        for x in range(n):
            for y in range(n):
                v, w = L.bot, L.top
                for x2 in range(n):
                    for y2 in range(n):
                        if L.leq[x2, x] and L.leq[y2, y]: v = L.join[v, lo[x2, y2]]
                        if L.leq[x, x2] and L.leq[y, y2]: w = L.meet[w, hi[x2, y2]]
                Flo[x, y], Fhi[x, y] = v, w
        if not L.leq[Flo, hi].all(): raise SystemExit(f"box on {L.name} contains no monotone F")
        T = lambda a: torch.as_tensor(np.concatenate([a.reshape(-1), [L.bot, L.top]]), device=self.dev)
        self.blo, self.bhi, self.Flo, self.Fhi = T(lo), T(hi), T(Flo), T(Fhi)
        self.box = None if box is None else (lo.tolist(), hi.tolist())

    def selftest(self, k=64):
        """L2 contract: observe on device ≡ reference.observe_one, on random monotone F (heat bath from both ends)."""
        if not hasattr(self, 'colors'): self._mcmc_tables()                         # samples come from the heat bath
        g = torch.Generator(device=self.dev); g.manual_seed(12345)
        Fs = mcmc_init(self, k)
        for _ in range(3): Fs = sweep(self, Fs, g)
        F = Fs[:, :self.n * self.n].reshape(k, self.n, self.n)
        assert monotone(self, F).all(), "selftest: heat bath produced a non-monotone F"
        got = observe(self, F); Fc = F.cpu().numpy()
        for i in range(k):
            ref = reference.observe_one(self.L, Fc[i])
            for key in ('m', 'n', 'comm', 'semi_ba_le_ab', 'semi_ab_le_ba', 'polar', 'meqn', 'ncf', 'ndef',
                        'rstages', 'rfull', 'rfirst_nonideal', 'kstages', 'laxfirst') + TRIPS:
                assert int(got[key][i]) == int(ref[key]), f"selftest on {self.dev}: {key} differs at sample {i}"
            assert got['a'][i].tolist() == ref['a'] and got['b'][i].tolist() == ref['b'], "selftest: derived pair differs"
            sig = sorted(got['sig'][i][got['defect'][i]].tolist())
            assert sig == ref['sig'], "selftest: defect signatures differ"


def monotone(P, F):
    """F (B, n, n) → (B,) bool: monotone in both arguments (checked on all cover pairs)."""
    ok = torch.ones(F.shape[0], dtype=torch.bool, device=P.dev)
    for (x, y) in P.L.covers:
        ok &= P.leq[F[:, x, :], F[:, y, :]].all(1) & P.leq[F[:, :, x], F[:, :, y]].all(1)
    return ok


def observe(P, F):
    """F (B, n, n) long → dict of per-F tensors. Pure; the only place where the mathematics of a single F lives."""
    B, n, ar = F.shape[0], P.n, P.idx
    full = lambda v: torch.full((B, n), v, dtype=torch.long, device=P.dev)
    a = full(P.top)
    for _ in range(P.h + 1): a = F.gather(2, a[:, :, None])[:, :, 0]               # a[x] ← F[x, a[x]]   (from ⊤)
    b = full(P.bot)
    for _ in range(P.h + 1): b = F.gather(1, b[:, None, :])[:, 0, :]               # b[y] ← F[b[y], y]   (from ⊥)
    m = torch.full((B,), P.bot, dtype=torch.long, device=P.dev)
    nn = torch.full((B,), P.top, dtype=torch.long, device=P.dev)
    for _ in range(P.h + 1):
        m = a.gather(1, m[:, None])[:, 0]; nn = b.gather(1, nn[:, None])[:, 0]
    phi, psi = a.gather(1, b), b.gather(1, a)                                      # a∘b, b∘a
    fa, fb = a == ar, b == ar
    defect = phi != psi
    out = dict(a=a, b=b, m=m, n=nn, defect=defect,
               comm=~defect.any(1),
               semi_ba_le_ab=P.leq[psi, phi].all(1),
               semi_ab_le_ba=P.leq[phi, psi].all(1),
               polar=(a[:, P.bot] == P.bot) & (b[:, P.bot] == P.bot) & (a[:, P.top] == P.top) & (b[:, P.top] == P.top),
               meqn=m == nn, ncf=(fa & fb).sum(1), ndef=defect.sum(1),
               sig=16 * P.rel[phi, ar] + 4 * P.rel[psi, ar] + P.rel[phi, psi])
    # R(F): R_0 = ↓⊥, R_{k+1} = ↓(R_k ∪ a(R_k) ∪ b⁻¹(R_k)); stage k counted when the set grows.
    # Alongside, the ideal-closure orbit r_0 = ⊥, r_{k+1} = r_k ∨ κ(r_k), κ(d) = a(d) ∨ ⋁{y : b(y) ≤ d}: the
    # transposed (κ-algebra) side of the Cut Lemma (§32.6). ⋁R_k ≤ r_k always (lax square); `laxfirst` is the
    # first iteration where it is strict; r_final = ⊤ is the principal-cut proposition (§30.4).
    def sup(mask):                                                                 # (B, n) bool → ⋁ selected, (B,)
        v = torch.full((B,), P.bot, dtype=torch.long, device=P.dev)
        for x in range(n): v = torch.where(mask[:, x], P.join[v, x], v)
        return v
    S = torch.zeros(B, n, dtype=torch.bool, device=P.dev); S[:, P.bot] = True
    stages = torch.zeros(B, dtype=torch.long, device=P.dev); first = torch.full((B,), -1, dtype=torch.long, device=P.dev)
    r = torch.full((B,), P.bot, dtype=torch.long, device=P.dev); kst = torch.zeros(B, dtype=torch.long, device=P.dev)
    lax = torch.full((B,), -1, dtype=torch.long, device=P.dev); tlax = torch.zeros(B, dtype=torch.bool, device=P.dev)
    hit = a[:, :, None] == ar                                                      # (B, x, z): a(x) = z
    for it in range(2 * n + 2):
        ideal = ((S[:, None, :] == P.down[None]).all(2) & S).any(1)                # S = ↓z for some z ∈ S
        first = torch.where((first < 0) & ~ideal, stages, first)
        sS = sup(S)
        tlax |= ~P.leq[sS, r]
        lax = torch.where((lax < 0) & (sS != r), torch.full_like(lax, it), lax)
        kap = P.join[a.gather(1, r[:, None])[:, 0], sup(P.leq[b, r[:, None]])]
        r2 = P.join[r, kap]
        T = S | (hit & S[:, :, None]).any(1) | S.gather(1, b)
        T = (T.to(torch.float32) @ P.leqTf) > 0                                    # down-closure
        grew = (T != S).any(1); stages += grew; S = T
        rg = r2 != r; kst += rg; r = r2
        if not bool(grew.any() | rg.any()): break                                  # both orbits stable (checked above)
    out.update(rstages=stages, rfull=S.all(1), rfirst_nonideal=first, kstages=kst, laxfirst=lax, orbit_lax=lax >= 0,
               trip_lax=tlax, trip_pcut=r != P.top)
    out.update(trip_i1=~P.leq[m, nn], trip_l1=a.gather(1, nn[:, None])[:, 0] != nn,
               trip_l2=b.gather(1, m[:, None])[:, 0] != m, trip_fusion=((phi == ar) != (fa & fb)).any(1))
    out['trip_i2'] = out['meqn'] != (out['ncf'] == 1)                              # §14: m = n ⟺ one common fixed point
    out.update(cl=out['comm'] & ~out['meqn'], semi=out['semi_ba_le_ab'] & ~out['meqn'], cut=~out['rfull'])
    return out


class Hist:
    """Commutative monoid of counts. Fixed schema (closed vocabulary); merge = add."""

    def __init__(self, n):
        self.n = n
        z = lambda k: np.zeros(k, dtype=np.int64)
        self.d = dict(count=z(1), joint=z(1 << len(JOINT_BITS)), ncf=z(n + 1), ndef=z(n + 1), sig=z(64),
                      rstages=z(n + 2), rfirst=z(n + 3), rstages_polar=z(n + 2), rfirst_polar=z(n + 3),
                      kstages=z(n + 2), laxfirst=z(2 * n + 4), laxfirst_polar=z(2 * n + 4),
                      trips=z(len(TRIPS)), viols=z(len(VIOLS)))
        self.witness = collections.defaultdict(list)

    def add(self, feats, F):
        bc = lambda t, k: torch.bincount(t.reshape(-1), minlength=k)[:k].cpu().numpy()
        d, f = self.d, feats
        d['count'] += len(f['m'])
        key = sum(f[k].long() << i for i, k in enumerate(JOINT_BITS))
        d['joint'] += bc(key, len(d['joint']))
        d['ncf'] += bc(f['ncf'], self.n + 1); d['ndef'] += bc(f['ndef'], self.n + 1)
        d['sig'] += bc(f['sig'][f['defect']], 64)
        d['rstages'] += bc(f['rstages'], self.n + 2); d['rfirst'] += bc(f['rfirst_nonideal'] + 1, self.n + 3)
        pol = f['polar']
        d['rstages_polar'] += bc(f['rstages'][pol], self.n + 2)
        d['rfirst_polar'] += bc(f['rfirst_nonideal'][pol] + 1, self.n + 3)
        d['kstages'] += bc(f['kstages'], self.n + 2)
        d['laxfirst'] += bc(f['laxfirst'] + 1, 2 * self.n + 4)
        d['laxfirst_polar'] += bc(f['laxfirst'][pol] + 1, 2 * self.n + 4)
        d['trips'] += np.array([int(f[k].sum()) for k in TRIPS], dtype=np.int64)
        v = np.array([int(f[k].sum()) for k in VIOLS], dtype=np.int64); d['viols'] += v
        for k in TRIPS + VIOLS + ('orbit_lax',):                                   # orbit_lax: examples only (§32.6)
            if int(f[k].sum()) and len(self.witness[k]) < WITNESS_MAX:
                for i in f[k].nonzero()[:, 0][:WITNESS_MAX - len(self.witness[k])].tolist():
                    self.witness[k].append(F[i].tolist())

    def merge(self, other):
        for k in self.d: self.d[k] += other.d[k]
        for k, v in other.witness.items(): self.witness[k] = (self.witness[k] + v)[:WITNESS_MAX]
        return self

    def json(self):
        d = {k: v.tolist() for k, v in self.d.items()}
        d['count'] = d['count'][0]
        d['joint'] = {''.join('1' if j >> i & 1 else '0' for i in range(len(JOINT_BITS))): int(c)
                      for j, c in enumerate(self.d['joint']) if c}
        d['joint_bits'] = list(JOINT_BITS)
        d['trips'] = dict(zip(TRIPS, map(int, d['trips']))); d['viols'] = dict(zip(VIOLS, map(int, d['viols'])))
        d['sig'] = {f"{'=<>|'[c >> 4]}{'=<>|'[(c >> 2) & 3]}{'=<>|'[c & 3]}": int(v) for c, v in enumerate(self.d['sig']) if v}
        d['witnesses'] = {k: v for k, v in self.witness.items() if v}
        return d


class Fibres:
    """Optional exact fibre sizes of π : F ↦ (a, b) (census only, n ≤ 9: the pair is encoded in one int64)."""

    def __init__(self, n):
        assert n ** (2 * n) < 2 ** 63, "fibre keys need n ≤ 9"
        self.n, self.c = n, collections.Counter()
        self.w = None

    def add(self, feats, P):
        if self.w is None: self.w = (P.n ** torch.arange(P.n, device=P.dev)).long()
        key = (feats['a'] * self.w).sum(1) * (P.n ** P.n) + (feats['b'] * self.w).sum(1)
        u, c = torch.unique(key, return_counts=True)
        for k, v in zip(u.tolist(), c.tolist()): self.c[k] += v

    def json(self):
        sizes = collections.Counter(self.c.values())
        return dict(image=len(self.c), fibre_size_hist={str(k): v for k, v in sorted(sizes.items())},
                    largest=max(self.c.values(), default=0))


# ---------------------------------------------------------------- census (exact)
def census_mask(P, Rw, k):
    """Parents Rw (B, k) int32: Mon-row indices of order[0..k-1] → (B, M) bool: admissible rows for order[k]."""
    ok = torch.ones(Rw.shape[0], P.Mon.shape[0], dtype=torch.bool, device=P.dev)
    for z in P.L.lower[P.order[k]]: ok &= P.rowle[Rw[:, P.pos[z]]]
    return ok


def census_level(P, Rw, k, ok=None):
    """Parents Rw (B, k) → children (B', k+1) int32."""
    ok = census_mask(P, Rw, k) if ok is None else ok
    pi, ri = ok.nonzero(as_tuple=True)
    return torch.cat([Rw[pi], ri[:, None].to(Rw.dtype)], 1)


def estimate_count(P, paths=65536, seed=0):
    """Knuth's estimator of the census size: random root-to-leaf descents choosing a uniform admissible row at each
    level; the product of branching numbers is an unbiased estimate of the number of leaves. → (mean, std. error)."""
    g = torch.Generator(device=P.dev); g.manual_seed(seed)
    M = P.Mon.shape[0]; chunk = max(1, min(paths, MEM // (24 * M)))                # ≈ 24 bytes per (path, row)
    ws = []
    for c0 in range(0, paths, chunk):
        Rw = torch.zeros(min(chunk, paths - c0), 0, dtype=torch.int32, device=P.dev)
        w = torch.ones(Rw.shape[0], dtype=torch.float64, device=P.dev)
        for k in range(P.n):
            ok = census_mask(P, Rw, k)                                              # ≥ 1 admissible row: constant-⊤
            w *= ok.sum(1).to(torch.float64)
            r = torch.multinomial(ok.to(torch.float32), 1, generator=g)[:, 0]; del ok
            Rw = torch.cat([Rw, r[:, None].to(torch.int32)], 1)
        ws.append(w)
    w = torch.cat(ws)
    return float(w.mean()), float(w.std() / paths ** 0.5)


def census_size(L, dev, paths=65536):
    """(estimate, std. error) of the census size of L, or None if a census of L is refused outright."""
    try: P = Plan(L, dev, census=True, mcmc=True)
    except SystemExit: return None
    return estimate_count(P, paths)


def leaves_to_F(P, Rw):
    return P.Mon[Rw[:, P.by_x]]                                                     # (B, n, n): F[x] = Mon[row of x]


def census_prefixes(P, target=2000):
    """Deterministic prefix jobs: expand levels until there are ≥ target partial assignments (or n−1 levels)."""
    Rw = torch.zeros(1, 0, dtype=torch.int32, device=P.dev); k = 0
    while k < P.n - 1 and Rw.shape[0] < target:
        Rw = census_level(P, Rw, k); k += 1
    return k, Rw


def census(L, dev, ck=None, fibres=False, log=print):
    P = Plan(L, dev, census=True, mcmc=True)
    M, n = P.Mon.shape[0], P.n
    # Budgets (bytes per item, all ≤ MEM per working set): the level mask and its temporaries per parent: the mask
    # and one gathered row of `rowle` (2·M bools) plus the row count ok.sum(1), which promotes bool to int64 and on
    # HIP materializes the cast (8·M bytes; uncounted before, a 3.9 GiB allocation on L6_6 at MORDOR_MEM=1024),
    # the children of one expansion (nonzero: 2 int64, gather + cat: 2·(n+1) int32 ⇒ ≈ 8n + 24 per child), and
    # observe (≈ 24 words per cell of F). A parent batch whose children exceed `cap` is split by the cumulative
    # child count before expanding, so the stack holds views of parent tensors, never more than one child batch
    # per level.
    nb = max(1, MEM // (10 * M + 4 * n))                                            # parents per level batch
    cap = max(M, MEM // (8 * n + 24))                                               # children per expansion
    leaf = max(1, MEM // (n * n * 8 * 24))                                          # F per observe batch
    j, pre = census_prefixes(P)
    state = dict(lattice=L.name, lid=lattice_id(L), schema=SCHEMA, j=j, njobs=pre.shape[0], done=0,
                 hist=Hist(n), fibres=Fibres(n) if fibres else None)
    if ck and os.path.exists(ck):
        with open(ck, 'rb') as fh: old = pickle.load(fh)
        assert (old['lid'], old['schema'], old['j'], old['njobs']) == (state['lid'], SCHEMA, j, pre.shape[0]), \
            "checkpoint belongs to another lattice/schema"
        if fibres and old['fibres'] is None: raise SystemExit("checkpoint was written without --fibres")
        state = old
    est, se = estimate_count(P)
    log(f"  census {L.name}: n={n}, |Mon|={M}, height {P.h}, ≈{est:.3g} ± {se:.2g} bifunctions (Knuth estimate), "
        f"{pre.shape[0]} prefix jobs at depth {j}, resuming at {state['done']}; device {describe(dev)}; mem {MEM >> 20} MiB")
    t0 = last = time.time(); cnt0 = int(state['hist'].d['count'][0])
    def save():
        if ck:
            with open(ck + '.tmp', 'wb') as fh: pickle.dump(state, fh)
            os.replace(ck + '.tmp', ck)
    while state['done'] < pre.shape[0]:
        g0 = state['done']; g1 = min(pre.shape[0], g0 + GROUP)
        H = Hist(n); Fb = Fibres(n) if fibres else None
        stack = [(j, pre[g0:g1])]
        while stack:
            k, Rw = stack.pop()
            if k == n:
                for s in range(0, Rw.shape[0], leaf):
                    F = leaves_to_F(P, Rw[s:s + leaf]); f = observe(P, F); H.add(f, F)
                    if Fb is not None: Fb.add(f, P)
                continue
            if Rw.shape[0] > nb:
                stack += [(k, Rw[s:s + nb]) for s in range(0, Rw.shape[0], nb)][::-1]; continue
            ok = census_mask(P, Rw, k)
            cnt = ok.sum(1)
            if Rw.shape[0] > 1 and int(cnt.sum()) > cap:                           # split parents by child count
                cut = torch.searchsorted(torch.cumsum(cnt, 0), torch.arange(cap, int(cnt.sum()), cap, device=P.dev))
                edges = [0] + sorted(set(min(max(int(c), 1), Rw.shape[0] - 1) for c in cut.tolist())) + [Rw.shape[0]]
                stack += [(k, Rw[a:b]) for a, b in zip(edges, edges[1:]) if b > a][::-1]
                del ok; continue
            ch = census_level(P, Rw, k, ok); del ok
            if ch.shape[0]: stack.append((k + 1, ch))
        state['hist'].merge(H)
        if fibres: state['fibres'].c.update(Fb.c)
        state['done'] = g1; save()
        if time.time() - last > 30 or g1 == pre.shape[0]:
            el = time.time() - t0; cnt = int(state['hist'].d['count'][0])
            mem = (f", peak device memory {torch.cuda.max_memory_allocated(dev) >> 20} MiB" if dev.type == 'cuda' else "")
            rate = (cnt - cnt0) / max(el, 1e-9)
            eta = f", ≈{(est - cnt) / rate / 3600:.1f} h left at this rate" if rate > 0 and est > cnt else ""
            log(f"  {g1}/{pre.shape[0]} prefix jobs, {cnt:,} bifunctions, {el:.0f}s ({rate:,.0f}/s this run){mem}{eta}")
            last = time.time()
    res = dict(schema=SCHEMA, mode='census', lattice=L.name, lid=state['lid'], n=n, height=P.h, mon=M,
               t=round(time.time() - t0, 1), device=describe(dev), **state['hist'].json())
    if fibres: res['fibres'] = state['fibres'].json()
    return res


# ---------------------------------------------------------------- mcmc (heat bath)
def mcmc_init(P, C):
    """Half the chains start at the least F of the box (constant-⊥ without a box), half at the greatest (constant-⊤):
    overdispersed starts, used for the mixing check. Columns N, N+1 are the constant ⊥ / ⊤ padding cells."""
    Fs = P.Flo[None].repeat(C, 1)
    Fs[C // 2:] = P.Fhi
    return Fs


def class_step(P, Fs, i, g, rho=1.0):
    """Heat bath on color class i (an independent set of cells), in place: resample each cell uniformly from
    [⋁ lower neighbours ∨ lo_c, ⋀ upper neighbours ∧ hi_c]. With rho < 1 only a random subset of the class (each cell
    with probability rho, independently of the state) is resampled. Either way the kernel is symmetric, i.e.
    reversible w.r.t. the uniform law on the box: the interval of a cell depends only on cells outside the class."""
    cells, lo_i, hi_i = P.colors[i]
    lov, hiv = Fs[:, lo_i], Fs[:, hi_i]                                             # (C, K, deg)
    lo, hi = P.join[lov[..., 0], P.blo[cells]], P.meet[hiv[..., 0], P.bhi[cells]]
    for t in range(1, lov.shape[-1]): lo = P.join[lo, lov[..., t]]
    for t in range(1, hiv.shape[-1]): hi = P.meet[hi, hiv[..., t]]
    c = P.cnt[lo, hi]
    u = torch.rand(lo.shape, generator=g, device=P.dev)
    new = P.ilist[lo, hi, torch.minimum((u * c).long(), c - 1)]
    if rho < 1.0: new = torch.where(torch.rand(lo.shape, generator=g, device=P.dev) < rho, new, Fs[:, cells])
    Fs[:, cells] = new
    return Fs


def sweep(P, Fs, g):
    """One systematic heat-bath sweep (every color class once). Reversible w.r.t. the uniform law on monotone F in
    the box; irreducible (every F descends cell by cell to the least F of the box)."""
    for i in range(len(P.colors)): class_step(P, Fs, i, g)
    return Fs


def mcmc(L, dev, chains, sweeps, burn, thin, seed, ck=None, log=print, box=None):
    """Heat bath, uniform on monotone F (in the named box, `box_preset`; then every rate is conditional on the box)."""
    P = Plan(L, dev, census=False, mcmc=True); n = P.n; N = n * n
    P.set_box(box_preset(L, box))
    g = torch.Generator(device=dev); g.manual_seed(seed)
    state = dict(lattice=L.name, lid=lattice_id(L), schema=SCHEMA, chains=chains, seed=seed, box=box, done=0,
                 hist=[Hist(n), Hist(n)], Fs=None, rng=None)
    if ck and os.path.exists(ck):
        with open(ck, 'rb') as fh: old = pickle.load(fh)
        assert (old['lid'], old['schema'], old['chains'], old['seed'], old.get('box')) == \
            (state['lid'], SCHEMA, chains, seed, box), "checkpoint belongs to another lattice/schema/chains/seed/box"
        state = old; g.set_state(state['rng'])
    Fs = mcmc_init(P, chains) if state['Fs'] is None else torch.as_tensor(state['Fs'], device=dev)
    grp = torch.arange(chains, device=dev) >= chains // 2
    log(f"  mcmc {L.name}: n={n}, height {P.h}, {len(P.colors)} color classes, box {box or 'none'}, {chains} chains, sweeps {sweeps} "
        f"(burn {burn}, thin {thin}), resuming at {state['done']}; device {describe(dev)}")
    t0 = last = time.time()
    def save():
        if ck:
            state['Fs'] = Fs.cpu().numpy(); state['rng'] = g.get_state()
            with open(ck + '.tmp', 'wb') as fh: pickle.dump(state, fh)
            os.replace(ck + '.tmp', ck)
    while state['done'] < sweeps:
        Fs = sweep(P, Fs, g); state['done'] += 1; s = state['done']
        if s > burn and (s - burn) % thin == 0:
            F = Fs[:, :N].reshape(chains, n, n); f = observe(P, F)
            for gi in (0, 1):
                sel = grp == bool(gi)
                state['hist'][gi].add({k: v[sel] for k, v in f.items()}, F[sel])
        if time.time() - last > 60 or s == sweeps:
            save(); log(f"  sweep {s}/{sweeps}, {(time.time() - t0):.0f}s"); last = time.time()
    assert monotone(P, Fs[:, :N].reshape(chains, n, n)).all(), "heat bath left the monotone set"
    H0, H1 = state['hist']
    tot = Hist(n).merge(H0).merge(H1)
    res = dict(schema=SCHEMA, mode='mcmc', lattice=L.name, lid=state['lid'], n=n, height=P.h, chains=chains,
               sweeps=sweeps, burn=burn, thin=thin, seed=seed, t=round(time.time() - t0, 1), device=describe(dev),
               **tot.json(), mixing=mixing_check(H0, H1))
    if box: res.update(box=box, box_cells=P.box)
    return res


def mixing_check(H0, H1):
    """L3 diagnostic, not a guarantee: rates of each joint bit in the ⊥-started vs ⊤-started halves. Samples within a
    chain are autocorrelated, so |z| is optimistic; large |z| means: run longer (more burn-in / sweeps)."""
    out = {}
    n0, n1 = int(H0.d['count'][0]), int(H1.d['count'][0])
    if not (n0 and n1): return out
    for i, k in enumerate(JOINT_BITS):
        c0 = sum(int(v) for j, v in enumerate(H0.d['joint']) if j >> i & 1)
        c1 = sum(int(v) for j, v in enumerate(H1.d['joint']) if j >> i & 1)
        p0, p1, p = c0 / n0, c1 / n1, (c0 + c1) / (n0 + n1)
        se = (p * (1 - p) * (1 / n0 + 1 / n1)) ** 0.5
        out[k] = dict(rate_bot_start=round(p0, 6), rate_top_start=round(p1, 6), z=round((p0 - p1) / se, 2) if se else 0.0)
    return out


# ---------------------------------------------------------------- boxes and multicanonical sampling (round 26)
def box_preset(L, name):
    """Named boxes (lo, hi) of cell intervals.
      corners  F(⊥,⊥) = ⊥ and F(⊤,⊤) = ⊤, i.e. b(⊥) = ⊥ and a(⊤) = ⊤ (two of the four polar conditions)
      rowgap   corners, and F(⊥, y) ≥ p for every y ≥ q, for the first two atoms p ≠ q: then b(y) ≠ ⊥ on ↑q, so
               b⁻¹(⊥) avoids ↑q and the principal step κ(⊥) = a(⊥) ∨ ⋁b⁻¹(⊥) is kept off ⊤ whenever ⋁(L ∖ ↑q) < ⊤"""
    if name in (None, '', 'none'): return None
    n = L.n
    lo = np.full((n, n), L.bot, dtype=np.int64); hi = np.full((n, n), L.top, dtype=np.int64)
    hi[L.bot, L.bot] = L.bot; lo[L.top, L.top] = L.top
    if name == 'corners': return lo, hi
    if name == 'rowgap':
        atoms = [x for x in range(n) if x != L.bot and all(z in (L.bot, x) for z in range(n) if L.leq[z, x])]
        if len(atoms) < 2: raise SystemExit(f"box rowgap needs two atoms; {L.name} has {len(atoms)}")
        p, q = atoms[:2]
        for y in range(n):
            if L.leq[q, y]: lo[L.bot, y] = L.join[lo[L.bot, y], p]
        return lo, hi
    raise SystemExit(f"unknown box {name!r} (corners, rowgap)")


# Scores for multicanonical runs: name → (number of levels, S(observe output) ∈ {0, …, levels−1}). Low S = rare.
SCORES = {
    'kappa':   (lambda P: P.h + 1, lambda P, f: (P.h - f['kstages']).clamp(min=0)),       # long ideal (κ) orbits
    'rstages': (lambda P: P.n, lambda P, f: (P.n - 1 - f['rstages']).clamp(min=0)),       # long R(F) closures
    'lag':     (lambda P: 2, lambda P, f: (f['laxfirst'] < 0).long()),                    # orbit lag (§32.6.3)
    'defects': (lambda P: P.n + 2, lambda P, f: torch.where(f['polar'], f['ndef'], torch.full_like(f['ndef'], P.n + 1))),
}                                                                                          # polar F with few defects


def tmmc_logg(C):
    """Level masses from proposal counts C[s, s'] (rows: from). The proposal kernel is symmetric, so the uniform law is
    stationary for it and, lumped onto levels, g(s) T(s→s') = g(s') T(s'→s) with T = C / row sums. Weighted least
    squares for x = log g over level pairs seen in both directions (weight = inverse variance 1/(1/C[s,s'] + 1/C[s',s]))
    on the component of the most visited level; x normalized so Σ g = 1 there. Other levels: nan."""
    C = np.asarray(C, dtype=np.float64); m = len(C); rows = C.sum(1)
    ref = int(np.argmax(rows)); comp = {ref}; grew = True
    E = [(s, t) for s in range(m) for t in range(s + 1, m) if C[s, t] > 0 and C[t, s] > 0]
    while grew:
        grew = False
        for s, t in E:
            if (s in comp) != (t in comp): comp |= {s, t}; grew = True
    idx = sorted(comp); pos = {v: i for i, v in enumerate(idx)}
    A, b, wt = [], [], []
    for s, t in E:
        if s in comp:
            row = np.zeros(len(idx)); row[pos[t]], row[pos[s]] = 1.0, -1.0
            A.append(row); b.append(np.log(C[s, t] / rows[s]) - np.log(C[t, s] / rows[t]))
            wt.append(1.0 / (1.0 / C[s, t] + 1.0 / C[t, s]))
    A.append(np.eye(len(idx))[pos[ref]]); b.append(0.0); wt.append(1e12)                # gauge x_ref = 0
    sw = np.sqrt(np.array(wt))[:, None]
    x = np.linalg.lstsq(np.array(A) * sw, np.array(b) * sw[:, 0], rcond=None)[0]
    out = np.full(m, np.nan); out[idx] = x - np.log(np.exp(x - x.max()).sum()) - x.max()
    return out


def mucan(L, dev, score, chains, sweeps, adapt, burn, thin, seed, rho=0.25, box=None, ck=None, log=print):
    """Multicanonical Metropolis on monotone F (in a box): target π(F) ∝ exp(w(S(F))) for a score S with few levels.
    Proposal: heat bath on one color class, on a random fraction rho of its cells (symmetric, §class_step); accept
    with min(1, exp(w(S') − w(S))). Every proposal, accepted or not, is counted in C[s, s'] (transition-matrix Monte
    Carlo); `tmmc_logg` turns C into level masses g. Phase 1 (`adapt` sweeps): every adapt/8 sweeps, w ← −log ĝ
    (levels not yet connected get the largest weight + 1, which pulls chains toward them). Phase 2 (`sweeps` sweeps,
    w frozen): exact Metropolis; after `burn`, every `thin` sweeps every
    chain is recorded. Since π depends on F only through S, the samples at level s are uniform on {F : S(F) = s}:
    per-level Hists are exact conditional laws. P_uniform(S = s) is estimated twice: from production proposal counts
    (TMMC, `p_uniform`; needs only uniformity within levels) and from visits, H(s) e^(−w(s)) / Σ (`p_uniform_hist`;
    needs flux equilibrium between levels). Disagreement means: run longer."""
    P = Plan(L, dev, census=False, mcmc=True); n = P.n; N = n * n
    P.set_box(box_preset(L, box))
    nlev, Sfun = SCORES[score][0](P), SCORES[score][1]
    g = torch.Generator(device=dev); g.manual_seed(seed)
    key = dict(lid=lattice_id(L), schema=SCHEMA, score=score, box=box, chains=chains, seed=seed,
               adapt=adapt, rho=rho)
    state = dict(key, lattice=L.name, done=0, w=np.zeros(nlev), Cad=np.zeros((nlev, nlev), dtype=np.int64),
                 Cpr=np.zeros((2, nlev, nlev), dtype=np.int64), hist=[Hist(n) for _ in range(nlev)],
                 visits=np.zeros((2, nlev), dtype=np.int64), acc=[0, 0], examples=[[] for _ in range(nlev)],
                 Fs=None, rng=None)
    if ck and os.path.exists(ck):
        with open(ck, 'rb') as fh: old = pickle.load(fh)
        assert all(old[k] == v for k, v in key.items()), "checkpoint belongs to another lattice/schema/run"
        state = old; g.set_state(state['rng'])
    Fs = mcmc_init(P, chains) if state['Fs'] is None else torch.as_tensor(state['Fs'], device=dev)
    leaf = max(1, MEM // (n * n * 8 * 24))                                          # F per observe batch (as census)
    def score_of(X):
        F = X[:, :N].reshape(-1, n, n)
        return torch.cat([Sfun(P, observe(P, F[i:i + leaf])) for i in range(0, F.shape[0], leaf)])
    S = score_of(Fs)
    w = torch.as_tensor(state['w'], dtype=torch.float64, device=dev)
    grp = (torch.arange(chains, device=dev) >= chains // 2).long()
    log(f"  mucan {L.name}: n={n}, score {score} ({nlev} levels), box {box or 'none'}, {chains} chains, adapt {adapt}, "
        f"sweeps {sweeps} (burn {burn}, thin {thin}), rho {rho}, resuming at {state['done']}; device {describe(dev)}")
    t0 = last = time.time()
    def save():
        if ck:
            state['Fs'] = Fs.cpu().numpy(); state['rng'] = g.get_state(); state['w'] = w.cpu().numpy()
            with open(ck + '.tmp', 'wb') as fh: pickle.dump(state, fh)
            os.replace(ck + '.tmp', ck)
    total = adapt + sweeps
    while state['done'] < total:
        t = state['done']; prod = t >= adapt
        for i in range(len(P.colors)):
            prop = class_step(P, Fs.clone(), i, g, rho)
            Sp = score_of(prop)
            ok = torch.log(torch.rand(chains, generator=g, device=dev, dtype=torch.float64)) < (w[Sp] - w[S]).clamp(max=0)
            cc = torch.bincount((grp * nlev + S) * nlev + Sp, minlength=2 * nlev * nlev).reshape(2, nlev, nlev)
            if prod: state['Cpr'] += cc.cpu().numpy()
            else: state['Cad'] += cc.sum(0).cpu().numpy()
            Fs = torch.where(ok[:, None], prop, Fs); S = torch.where(ok, Sp, S)
            if prod: state['acc'][0] += int(ok.sum()); state['acc'][1] += chains
        state['done'] = t + 1
        if not prod and ((t + 1) % max(1, adapt // 8) == 0 or t == adapt - 1):     # w ← −log ĝ (TMMC)
            lg = tmmc_logg(state['Cad']); wn = -lg
            wn[np.isnan(lg)] = np.nanmax(wn) + 1.0
            w = torch.as_tensor(wn - wn.max(), device=dev)
        else:
            s_prod = state['done'] - adapt
            if s_prod > burn and (s_prod - burn) % thin == 0:
                Fa = Fs[:, :N].reshape(chains, n, n)
                for i0 in range(0, chains, leaf):
                    F = Fa[i0:i0 + leaf]; f = observe(P, F); Sc = Sfun(P, f)
                    assert bool((Sc == S[i0:i0 + leaf]).all()), "score cache diverged from the state"
                    for lev in torch.unique(Sc).tolist():
                        sel = Sc == lev
                        state['hist'][lev].add({k: v[sel] for k, v in f.items()}, F[sel])
                        if len(state['examples'][lev]) < WITNESS_MAX:
                            state['examples'][lev] += F[sel][:WITNESS_MAX - len(state['examples'][lev])].tolist()
                state['visits'] += torch.bincount(grp * nlev + S, minlength=2 * nlev).reshape(2, nlev).cpu().numpy()
        if time.time() - last > 60 or state['done'] == total:
            save(); last = time.time()
            log(f"  {'sweep' if prod else 'adapt'} {state['done'] - adapt * prod}/{sweeps if prod else adapt}, "
                f"{(time.time() - t0):.0f}s, levels visited now {torch.bincount(S, minlength=nlev).tolist()}")
    assert monotone(P, Fs[:, :N].reshape(chains, n, n)).all(), "sampler left the monotone set"
    assert bool(((Fs >= 0) & P.leq[P.blo[None], Fs] & P.leq[Fs, P.bhi[None]]).all()), "sampler left the box"
    wv = w.cpu().numpy(); H = state['visits']
    def p_unif(h):
        x = np.where(h > 0, np.exp(-(wv - wv.max())) * h, 0.0); return (x / x.sum()).tolist() if x.sum() else x.tolist()
    def p_tmmc(C):
        lg = tmmc_logg(C); return [None if np.isnan(v) else float(np.exp(v)) for v in lg]
    levels = []
    for lev in range(nlev):
        if not state['visits'][:, lev].sum(): continue
        levels.append(dict(level=lev, samples=int(H[:, lev].sum()), w=float(wv[lev]),
                           **state['hist'][lev].json(), examples=state['examples'][lev]))
    return dict(schema=SCHEMA, mode='mucan', lattice=L.name, lid=key['lid'], n=n, height=P.h, score=score,
                box=box, box_cells=P.box, chains=chains, sweeps=sweeps, adapt=adapt, burn=burn, thin=thin,
                seed=seed, rho=rho, t=round(time.time() - t0, 1), device=describe(dev),
                acceptance=round(state['acc'][0] / max(state['acc'][1], 1), 4), count=int(H.sum()),
                p_uniform=p_tmmc(state['Cpr'].sum(0)), p_uniform_bot_start=p_tmmc(state['Cpr'][0]),
                p_uniform_top_start=p_tmmc(state['Cpr'][1]), p_uniform_hist=p_unif(H.sum(0)),
                proposals=state['Cpr'].sum(0).tolist(),
                visits=H.sum(0).tolist(), levels=levels)
