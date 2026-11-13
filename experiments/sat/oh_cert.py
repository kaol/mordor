"""Certificates for a cube-and-conquer refutation of the rigid orbit-height theory (log §34.3z¹⁶¹).

1. Build the case tree. Root: n = first i ≤ H with ⊤ ≤ u_i (else n = H+1), then m = first j with d_j ≤ ⊥ (else H+1);
   minimal literals [⊤ ≤ u_n] (n ≤ H), [¬ ⊤ ≤ u_{n−1}] (n ≥ 2), [d_m ≤ ⊥] (m ≤ H), [¬ d_{m−1} ≤ ⊥] (m ≥ 2).
   Search cases (2 ≤ n, m, n + m ≤ H + 2) continue with the cached oh_cube.py tree (keys over its full-unit case
   clauses; a ('sub',) entry marks the oh_ground SUBCASE 3×3 split); every other root combination is a fresh leaf.
   Splits are 3-way: [A] | [B, ¬A] | [¬A, ¬B] with A = z ≤ lo, B = hi ≤ z (interval) or A = z ≤ c, B = c ≤ z.
2. For each leaf: ground refutation (rigid, lazyall, firable; starting from the leaf's cached terms, growing if needed)
   of the theory plus the leaf's literals, drat-trim core, provenance tags.
3. Lean: one global term table, one `bv_decide` theorem per leaf (the literals are hypotheses), and the case tree.
  DRAT_TRIM=path/to/drat-trim python3 oh_cert.py H CACHE_DIR OUT_DIR [seed] [seeddir=DIR]
  (seed: add the H = 5 hand-run leaves from oh5_work/seed — or seeddir — to the cache first)
"""
import sys, os, pickle, subprocess, time, hashlib
sys.argv += ['lazyall', 'rigid', 'firable']
import oh_ground as og
import oh_cube as oc
S = next((a[8:] for a in sys.argv if a.startswith('seeddir=')), os.path.join(os.path.dirname(os.path.abspath(__file__)), 'oh5_work', 'seed'))
TRIM = os.environ.get('DRAT_TRIM', 'drat-trim')

def seed_h5(cache):
    oc.CACHE = cache; H = 5; us, ds = oc.u_d(H)
    for (n, m) in [(2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 4), (4, 2), (4, 3), (5, 2)]:
        k = oc.ckey(H, oc.case_clauses(H, n, m))
        if oc.cget(k) is None: oc.cput(k, ('leaf', pickle.load(open(f'{S}/c5_{n}_{m}.pkl', 'rb'))))
    oc.cput(oc.ckey(H, oc.case_clauses(H, 3, 3)), ('sub',))
    for (a, b, f) in [(0, 0, 'c5_33_0_0'), (0, 1, 'c5_33_0_1'), (1, 0, 'c5_33_1_0'), (1, 1, 'c5_33_1_1'), (2, 2, 'cube33_2_2')]:
        k = oc.ckey(H, sub_clauses(H, a, b))
        if oc.cget(k) is None: oc.cput(k, ('leaf', pickle.load(open(f'{S}/{f}.pkl', 'rb'))))

def sub_lits(H, w):
    us, ds = oc.u_d(H); v_, u2, d2 = us[1], us[2], ds[2]; p_, q_ = (0, u2), (d2, 1)
    out = []
    for (z, lo, hi, ww) in ((p_, d2, v_, w[0]), (q_, v_, u2, w[1])):
        out.append((z, lo, hi, ww))
    return out

def sub_clauses(H, a, b):
    cls = oc.case_clauses(H, 3, 3)
    for (z, lo, hi, w) in sub_lits(H, (a, b)):
        cls += [[(z, lo, True)]] if w == 0 else [[(hi, z, True)]] if w == 1 else [[(z, lo, False)], [(hi, z, False)]]
    return cls

def three(A, B):                      # branch literal lists of a 3-way split
    return [[A], [B, (A[0], A[1], False)], [(A[0], A[1], False), (B[0], B[1], False)]]

def build_tree(H):
    """Tree nodes: ('leaf', lits, terms) | ('split', A, B, [child0, child1, child2]) | ('bin', A, child_yes, child_no)."""
    us, ds = oc.u_d(H)
    def cube_node(full_cls, lits):
        c = oc.cget(oc.ckey(H, full_cls))
        if c is None: raise RuntimeError(f'missing cache entry under {lits}')
        if c[0] == 'leaf': return ('leaf', lits, c[1])
        if c[0] == 'sub':
            kids = []
            def subnode(ws, lits2):
                if len(ws) == 2:
                    return cube_node(sub_clauses(H, *ws), lits2)
                z, lo, hi, _ = sub_lits(H, (0, 0))[len(ws)]
                A = (z, lo, True); B = (hi, z, True)
                return ('split', A, B, [subnode(ws + [w], lits2 + br) for w, br in enumerate(three(A, B))])
            return subnode([], lits)
        _, z, exts, _ = c
        A = exts[0][0][0]; B = exts[1][0][0]
        return ('split', A, B, [cube_node(full_cls + ext, lits + [cl[0] for cl in ext]) for ext in exts])
    def m_level(n, lits):
        def rec(m):
            Lm = [(ds[m - 1], 0, False)] if m >= 2 else []
            if m == H + 1: return leafnode(n, m, lits + Lm)
            A = (ds[m], 0, True)
            return ('bin', A, leafnode(n, m, lits + [A] + Lm), rec(m + 1))
        return rec(1)
    def leafnode(n, m, lits):
        if 2 <= n <= H and 2 <= m <= H and n + m <= H + 2:
            return cube_node(oc.case_clauses(H, n, m), lits)
        return ('leaf', lits, [])
    def n_level(n):
        Ln = [(1, us[n - 1], False)] if n >= 2 else []
        if n == H + 1: return m_level(n, Ln)
        A = (1, us[n], True)
        return ('bin', A, m_level(n, [A] + Ln), n_level(n + 1))
    return n_level(1)

def leaves_of(t):
    if t[0] == 'leaf': return [t]
    if t[0] == 'bin': return leaves_of(t[2]) + leaves_of(t[3])
    return [x for c in t[3] for x in leaves_of(c)]

def certify_leaf(H, lits, terms, idx, work):
    og.KEEP = True
    G = og.OH(H, False, True); G.add_F(0, 1)
    for e in terms: G.add_expr(e)
    for j, (a, b, pos) in enumerate(lits):
        x, y = G.add_expr(a), G.add_expr(b)
        G.add([G.le(x, y) if pos else -G.le(x, y)], ('case', j))
    ok, G = og.run(H, cap=100000, batch=4, verbose=False, rigid=True, preset=[], tmax=1800, prebuilt=G)
    if not ok: raise RuntimeError(f'leaf {idx} not refuted')
    cnf = os.path.join(work, f'leaf{idx}.cnf'); core = os.path.join(work, f'leaf{idx}_core.cnf')
    with open(cnf, 'w') as fh:
        fh.write(f"p cnf {G.nv} {len(G.clauses)}\n")
        for c in G.clauses: fh.write(" ".join(map(str, c)) + " 0\n")
    r = subprocess.run([sys.executable, 'drat_certify.py', cnf, TRIM, core], capture_output=True, text=True)
    if 's VERIFIED' not in r.stdout: raise RuntimeError(f'leaf {idx}: drat-trim failed\n{r.stdout}')
    for it in range(3):                             # iterate core extraction (drat-trim cores are not minimal)
        nxt = core + f'.{it}'
        r2 = subprocess.run([sys.executable, 'drat_certify.py', core, TRIM, nxt], capture_output=True, text=True)
        if 's VERIFIED' not in r2.stdout: break
        os.replace(nxt, core); os.remove(core.rsplit('.', 1)[0] + '.drat') if os.path.exists(core.rsplit('.', 1)[0] + '.drat') else None
    tagof = {}
    for c, tg in zip(G.clauses, G.tags): tagof.setdefault(tuple(sorted(c)), tg)
    cl = [tuple(sorted(map(int, l.split()[:-1]))) for l in open(core) if l.strip() and not l.startswith(('p', 'c'))]
    tags = [tagof[c] for c in cl]
    exprs = {t: G.expr(t) for t in range(len(G.terms))}
    os.remove(cnf); os.remove(cnf.rsplit('.', 1)[0] + '.drat')
    return dict(tags=tags, exprs=exprs, terms=G.terms, nlits=len(lits), core=len(cl))

if __name__ == '__main__':
    H = int(sys.argv[1]); cache = sys.argv[2]; out = sys.argv[3]; os.makedirs(out, exist_ok=True)
    oc.CACHE = cache
    if 'seed' in sys.argv: seed_h5(cache)
    tree = build_tree(H); L = leaves_of(tree)
    print(f'H={H}: case tree with {len(L)} leaves', flush=True)
    res = []
    for i, (_, lits, terms) in enumerate(L):
        f = os.path.join(out, f'leaf{i}.pkl')
        if os.path.exists(f): res.append(pickle.load(open(f, 'rb'))); continue
        t0 = time.time(); r = certify_leaf(H, lits, terms, i, out); pickle.dump(r, open(f, 'wb')); res.append(r)
        print(f'  leaf {i}: {len(lits)} literals, core {r["core"]} clauses, {time.time()-t0:.0f}s', flush=True)
    pickle.dump(dict(H=H, tree=tree), open(os.path.join(out, 'tree.pkl'), 'wb'))
    print('certified all leaves', flush=True)
