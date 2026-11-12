"""Cube-and-conquer for the rigid orbit-height theory (log §34.3z¹⁶¹).

Leaves are ground searches of `oh_ground.run` (lazyall rigid firable) under case clauses over term expressions, with
a time budget. A leaf that exceeds its budget is split three ways on the shallowest boundary-derived term z
(F(p, ⊤), F(⊥, p), F(p, q) over pinned elements p, q) whose order relation to some pinned element c is undetermined
(decided by assumption queries on the leaf's solver): z ≤ c | c < z | z ∥ c; z becomes pinned. The case clauses are
search guidance only: every refuted leaf contributes its term expressions, and the union of all leaves' terms is then
refuted *without* case clauses (`oh_ground.py … preset=FILE nogrow`), giving one certificate.
Options: warm (children start from the parent's terms), cache=DIR (persist every refuted leaf and split decision; a
restarted run replays them).
  python3 oh_cube.py H BUDGET OUT.pkl [root=n,m] [sub=a,b] [warm] [cache=DIR]   (root: one boundary-orbit case; sub: oh_ground SUBCASE)
"""
import sys, time, pickle, os, hashlib
sys.argv += ['lazyall', 'rigid', 'firable']
import oh_ground as og

def u_d(H):
    us = [0]; ds = [1]
    for _ in range(H): us.append((us[-1], 1)); ds.append((0, ds[-1]))
    return us, ds

def case_clauses(H, n, m):
    us, ds = u_d(H); cl = []
    for i in range(1, H + 1):
        cl.append([(1, us[i], True)] if i >= n else [(1, us[i], False)])
        cl.append([(ds[i], 0, True)] if i >= m else [(ds[i], 0, False)])
    return cl

def split_terms(pinned):
    out = []
    for p in pinned:
        out += [(p, 1), (0, p)]
    for p in pinned:
        for q in pinned: out.append((p, q))
    def size(e): return 1 if e in (0, 1) else 1 + size(e[0]) + size(e[1])
    return sorted(set(out) - set(pinned) - {0, 1}, key=lambda e: (size(e), repr(e)))

WARM = 'warm' in sys.argv
def solve_leaf(H, clauses, budget, preset=None):
    ok, G = og.run(H, cap=100000, batch=4, verbose=False, rigid=True, extra=clauses, tmax=budget, preset=preset)
    return ok, G

def undetermined(G, a, b):
    la = G.le(G.add_expr(a), G.add_expr(b))
    return G.S.solve(assumptions=[la]) and G.S.solve(assumptions=[-la])

CACHE = next((a[6:] for a in sys.argv if a.startswith('cache=')), None)
def ckey(H, clauses): return hashlib.sha1(repr((H, clauses)).encode()).hexdigest()
def cget(k):
    if CACHE and os.path.exists(os.path.join(CACHE, k)): return pickle.load(open(os.path.join(CACHE, k), 'rb'))
def cput(k, v):
    if CACHE:
        os.makedirs(CACHE, exist_ok=True); tmp = os.path.join(CACHE, k + '.tmp')
        pickle.dump(v, open(tmp, 'wb')); os.replace(tmp, os.path.join(CACHE, k))

def cube(H, budget, clauses, pinned, depth, leaves, log, preset=None):
    tag = '  ' * depth; k = ckey(H, clauses); c = cget(k)
    if c is not None and c[0] == 'leaf':
        leaves.append(c[1]); log(f"{tag}UNSAT (cached, {len(c[1])} terms)"); return True
    if c is not None and c[0] == 'split':
        log(f"{tag}split (cached) {c[1]}")
        for extra in c[2]:
            if not cube(H, budget, clauses + extra, pinned + [c[1]], depth + 1, leaves, log, c[3]): return False
        return True
    t0 = time.time(); ok, G = solve_leaf(H, clauses, budget, preset)
    if ok:
        terms = [G.expr(t) for t in range(2, len(G.terms))]
        cput(k, ('leaf', terms)); leaves.append(terms); log(f"{tag}UNSAT ({len(G.terms)} terms, {time.time()-t0:.0f}s)"); return True
    if G.S.solve() is False:                     # refuted by saturation after the budget check
        terms = [G.expr(t) for t in range(2, len(G.terms))]
        cput(k, ('leaf', terms)); leaves.append(terms); log(f"{tag}UNSAT late"); return True
    kids = [G.expr(t) for t in range(2, len(G.terms))] if WARM else None
    forced = lambda a, b: not G.S.solve(assumptions=[-G.le(G.add_expr(a), G.add_expr(b))])
    for z in split_terms(pinned):                # interval split: forced lo ≤ z ≤ hi → z = lo | z = hi | strictly between
        below = [c for c in pinned if forced(c, z)]; above = [c for c in pinned if forced(z, c)]
        lo = [c for c in below if not any(c != d and forced(c, d) for d in below)]
        hi = [c for c in above if not any(c != d and forced(d, c) for d in above)]
        if not lo or not hi: continue
        lo, hi = lo[0], hi[0]
        if forced(z, lo) or forced(hi, z): continue
        log(f"{tag}split {z} in [{lo}, {hi}] ({len(G.terms)} terms)")
        G.S.delete()
        exts = ([[(z, lo, True)]], [[(hi, z, True)]], [[(z, lo, False)], [(hi, z, False)]]); cput(k, ('split', z, exts, kids))
        for extra in exts:
            if not cube(H, budget, clauses + extra, pinned + [z], depth + 1, leaves, log, kids): return False
        return True
    for z in split_terms(pinned):                # fallback: z ≤ c | c < z | z ∥ c against an undetermined pinned c
        for c in pinned:
            if c in (0, 1): continue
            if undetermined(G, z, c) and undetermined(G, c, z):
                log(f"{tag}split {z} vs {c} ({len(G.terms)} terms)")
                G.S.delete()
                exts = ([[(z, c, True)]], [[(c, z, True)], [(z, c, False)]], [[(z, c, False)], [(c, z, False)]])
                cput(k, ('split', z, exts, kids))
                for extra in exts:
                    if not cube(H, budget, clauses + extra, pinned + [z], depth + 1, leaves, log, kids): return False
                return True
    log(f"{tag}no split available ({len(G.terms)} terms)"); return False

if __name__ == '__main__':
    H = int(sys.argv[1]); budget = float(sys.argv[2]); out = sys.argv[3]
    sub = next((tuple(int(v) for v in a[4:].split(',')) for a in sys.argv if a.startswith('sub=')), None)
    root = next((tuple(int(v) for v in a[5:].split(',')) for a in sys.argv if a.startswith('root=')), None)
    leaves = []; t0 = time.time(); log = lambda s: print(f"[{time.time()-t0:7.0f}s] {s}", flush=True)
    us, ds = u_d(H)
    cases = [root] if root else [(n, m) for n in range(2, H + 1) for m in range(2, H + 1) if n + m <= H + 2]
    allok = True
    for (n, m) in cases:
        log(f"case u-steps {n}, d-steps {m}")
        pinned = sorted(set(us[1:n] + ds[1:m]), key=repr); cls = case_clauses(H, n, m)
        if sub:                                  # oh_ground.py SUBCASE: p = F(⊥, u₂) in [d₂, v], q = F(d₂, ⊤) in [v, u₂]
            v_, u2, d2 = us[1], us[2], ds[2]; p_, q_ = (0, u2), (d2, 1)
            for (z, lo, hi, w) in ((p_, d2, v_, sub[0]), (q_, v_, u2, sub[1])):
                cls += [[(z, lo, True)]] if w == 0 else [[(hi, z, True)]] if w == 1 else [[(z, lo, False)], [(hi, z, False)]]
            pinned += [p_, q_]
        allok &= cube(H, budget, cls, pinned, 1, leaves, log)
    terms = sorted({e for L in leaves for e in L}, key=repr)
    pickle.dump(terms, open(out, 'wb'))
    log(f"{'all cases refuted' if allok else 'INCOMPLETE'}: {len(leaves)} leaves, union {len(terms)} terms -> {out}")
