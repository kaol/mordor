"""Free analysis (no search) of stored NoFix models of relaxed worlds (Row1/LastLast/LastMeet/LastEither/Desc1/...).
For each model: build the descent-maximal map F# (brief291 A3; same descents), list every W0 Tb violation of F#
at an atom row q (high w with F#(q,w) <= q), and report:
  - fibre: phi(w) = q at every violation (lemma TbFibre)
  - k = size of the smallest set of rows x' >= q in Z whose successor values succ_{x'}(sigma_{x'}(w)) already meet <= q
  - whether some violation column is a two-row meet u ^ v (u in desc(q), v in desc(x), x >= q) [then F# is not in W0^2]
Prints the quantifier: FOR EACH model, FOR EACH atom q, FOR EACH high w."""
import sys, json, itertools, glob, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W
def sharp(w):
    n, le, h, L = w.n, w.le, w.h, w.L; D = {x: w.desc(x) for x in w.Z}
    sig = lambda x, y: min((z for z in D[x] if le[y][z]), key=lambda z: h[z])
    G = [[w.top] * n for _ in range(n)]
    for y in range(n): G[w.bot][y] = w.F[w.bot][y]
    for x in w.Z:
        if x == w.bot: continue
        for y in range(n):
            v = w.top
            for x2 in w.Z:
                if le[x][x2]: v = L.meet[v][w.F[x2][sig(x2, y)]]
            G[x][y] = v
    return G, sig
def analyse(name, d, verbose=False):
    w = W(d['sets'], d['F']); G, sig = sharp(w); v = W(w.sets, G)
    assert v.mono and v.Z == w.Z and all(v.desc(x) == w.desc(x) for x in w.Z), 'F# breaks the normal form'
    n, le, h, L, bot = w.n, w.le, w.h, w.L, w.bot
    out = collections.Counter(); viols = []
    for q in w.atoms:
        rows = [x for x in w.Z if x != bot and le[q][x]]
        two = set()
        for x in rows:
            for u in w.desc(q):
                for vv in w.desc(x):
                    m_ = L.meet[u][vv]
                    if h[m_] >= 3: two.add(m_)
        for y in w.hi:
            if le[G[q][y]][q]:
                fib = w.F[bot][y] == q
                vals = {x: w.F[x][sig(x, y)] for x in rows}
                k = next(k for k in range(1, len(rows) + 1) for S in itertools.combinations(rows, k)
                         if le[L.meet[w.top][w.top] if False else __import__('functools').reduce(lambda a, b: L.meet[a][b], [vals[x] for x in S], w.top)][q])
                viols.append((q, y, fib, k, y in two))
    ks = collections.Counter(k for *_, k, _ in viols)
    return dict(name=name, n=w.n, H=w.h[w.top], nofix=v.nofix(), w0_sharp=v.w0(), nviol=len(viols),
                fibre_all=all(f for _, _, f, _, _ in viols), k=dict(ks), two_row_viol=any(t for *_, t in viols),
                exits=not v.noexit(), d_N=w.dN(), viols=viols if verbose else None)
if __name__ == '__main__':
    files = sys.argv[1:]
    print(__doc__)
    tot = collections.Counter()
    for f in files:
        D = json.load(open(f)); D = D if isinstance(D, list) else [D]
        for k, d in enumerate(D):
            r = analyse(f.split('/')[-1] + f'#{k}', d)
            print(r); tot[('two_row_viol', r['two_row_viol'], 'fibre_all', r['fibre_all'], 'w0#', r['w0_sharp'], 'mink', min(r['k']) if r['k'] else None)] += 1
    for k_, c in tot.items(): print(c, k_)
