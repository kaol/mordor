"""The i = 0 case and the first A-entry (log §34.3z¹⁹⁷).

For every non-ascending height-k row x and every terminal source q′ (all a_normal choices, positive stage) with x ≤ q′:
A1 (x = q′) or A2 (h(q′) = k + 1, x ⋖ q′); p = b(q′) vs q′ and vs x, h(p) − k, the meet and join of p and q′.
For genealogies ending at a first A-entry (q_d ≤ a(r)): r ascending, h(r) − k, q_d = a(r).
mode=icok: ¬IC(m) dropped, ¬UpCell imposed; mode=min: MinUpCell hypotheses.
   python3 i0_probe.py [mode=min|icok] [rmin=R] (closure … | sweep …)
"""
import sys, collections, json, signal
MODE = next((a[5:] for a in sys.argv if a.startswith('mode=')), 'icok')
sys.argv += ['multi', 'notop', 'nofeeder', 'notightK1'] + (['icok'] if MODE == 'icok' else [])
sys.path.insert(0, '../separation')
from rstages import stages, b_of, a_of
from tight_probe import lattices
import single_claims as sc

C = collections.Counter(); best = {}
def report(*_):
    for k_, v in sorted(C.items(), key=str): print(k_, v)
    for k_, v in sorted(best.items()): print('MIN', k_, v)
    sys.stdout.flush(); sys.exit(0)
signal.signal(signal.SIGTERM, report)
def keep(tag, n, d):
    if tag not in best or n < best[tag]:
        best[tag] = n; json.dump(d, open(f'i0_{MODE}_{tag}_min{n}.json', 'w'))

FLAGS = ('multi', 'notop', 'nofeeder', 'notightK1', 'icok')
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS and not a.startswith(('rmin=', 'mode='))]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'upcell' if MODE == 'icok' else 'minhyp', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F); jn = L.join; mt = L.meet
        inR = lambda x, j: st[x] is not None and st[x] <= j
        A = [a_of(L, F, x) for x in range(n)]; B = [b_of(L, F, x) for x in range(n)]
        rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
        def terminals(q, s, seen):
            if (q, s) in seen: return set()
            seen.add((q, s))
            if s == 0: return {(0, q)}
            rs = [r for r in range(n) if inR(r, s - 1) and le[q][A[r]]]
            if rs:
                out = set()
                for r in rs: out |= terminals(r, s - 1, seen)
                return out
            if inR(q, s - 1): return terminals(q, s - 1, seen)
            return {(s, q)}
        X = [x for x in range(n) if inR(x, k) and h[x] == k]
        uprow = lambda x: any(le[x][z] and z != x and not le[m][z] and (le[F[x][z]][x] or le[z][F[x][z]]) for z in range(n))
        C['models', MODE] += 1; D = dict(sets=L.S, F=F, m=m)
        for x in X:
            if le[x][A[x]]: continue
            for (t, q0) in terminals(x, k, set()):
                if t == 0 or not le[x][q0]: continue
                p = B[q0]; case = 'A1 (x = q′)' if x == q0 else 'A2 (x ⋖ q′)'
                mtq = mt[p][q0]; jq = jn[p][q0]
                tag = ('i = 0', MODE, case, 'p vs q′', rl(p, q0), 'p vs x', rl(p, x), 'h(p) − k', h[p] - k,
                       'p ∧ q′: h − k', h[mtq] - k, 'p ∨ q′ off m', not le[m][jq], 'x carries UpCell', uprow(x))
                C[tag] += 1
                keep(case[:2] + '_p' + {'<': 'lt', '∥': 'par', '>': 'gt', '=': 'eq'}[rl(p, q0)] + '_x' + {'<': 'lt', '∥': 'par', '>': 'gt', '=': 'eq'}[rl(p, x)], n, dict(D, x=x, q=q0))
            # first A-entry genealogies
            for (t, q0) in terminals(x, k, set()):
                if t == 0: continue
                q = q0; sig = st[q]
                while True:
                    rs = [r for r in range(n) if inR(r, sig - 1) and le[q][A[r]]]
                    if rs or sig == 1: break
                    q = B[q]; sig -= 1
                if rs:
                    for r in rs:
                        C[('first A-entry parent', MODE, 'r ascending', le[r][A[r]], 'h(r) − k', h[r] - k, 'q_d = a(r)', q == A[r], 'r vs q_d', rl(r, q))] += 1
report()
