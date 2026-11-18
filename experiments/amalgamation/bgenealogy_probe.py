"""B-source genealogy of the terminal sources of non-ascending rows (log §34.3z¹⁹⁶).

For every non-ascending height-k row x (x ≰ a x) and every terminal source q′ of an A-normal form x ≤ a^i(q′) (all
choices of the recursion of a_normal), follow terminalBAncestry: q_0 = q′ new at stage σ; at q_j (new at σ_j): stop if
A-entered (q_j ≤ a(r), r ∈ R_{σ_j − 1}), stop as pure-B if σ_j = 1 (b q_j = ⊥), else q_{j+1} = b(q_j). Records the end
type, depth, comparability b(q_j) vs q_j, covers, lateness h(q_j) − σ_j, and at an A-entry the parent r and q_d vs a(r).
mode=icok: ¬IC(m) dropped, ¬UpCell imposed; mode=min: MinUpCell hypotheses.
   python3 bgenealogy_probe.py [mode=min|icok] [rmin=R] (closure … | sweep …)
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
        best[tag] = n; json.dump(d, open(f'bg_{MODE}_{tag}_min{n}.json', 'w'))

FLAGS = ('multi', 'notop', 'nofeeder', 'notightK1', 'icok')
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS and not a.startswith(('rmin=', 'mode='))]):
    if L.height < 2: continue
    for m in range(L.n):
        if not (max(2, sc.RMIN) <= L.rank[m] < L.height): continue
        F = sc.query(L, m, 'upcell' if MODE == 'icok' else 'minhyp', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        A = [a_of(L, F, x) for x in range(n)]; B = [b_of(L, F, x) for x in range(n)]
        rl = lambda a_, b_: '=' if a_ == b_ else '<' if le[a_][b_] else '>' if le[b_][a_] else '∥'
        def terminals(q, s, seen):            # all (stage, source) terminals of the a_normal recursion from q ∈ R_s
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
        C['models', MODE] += 1
        D = dict(sets=L.S, F=F, m=m)
        for x in X:
            if le[x][A[x]]: continue
            for (t, q0) in terminals(x, k, set()):
                if t == 0: C[('terminal', MODE, 'stage 0')] += 1; continue
                ii = next(i_ for i_ in range(k - t + 1) if (lambda c_: le[x][c_])(__import__('functools').reduce(lambda u, _: A[u], range(i_), q0)))
                chain = [q0]
                for _ in range(ii): chain.append(A[chain[-1]])
                C[('terminal', MODE, 'least i with x ≤ a^i(q′)', ii, 'q′ ascending', le[q0][A[q0]], 'some chain element ascending', any(le[c_][A[c_]] for c_ in chain))] += 1
                q = q0; sig = st[q]; d = 0; comps = []; late = []; covers = []
                while True:
                    late.append(h[q] - sig)
                    rs = [r for r in range(n) if inR(r, sig - 1) and le[q][A[r]]]
                    if rs: end = 'first A-entry'; break
                    if sig == 1: end = 'pure B (b q_d = ⊥)'; break
                    bq = B[q]; comps.append(rl(bq, q)); covers.append(bq in L.covers_dn[q]); q = bq; sig -= 1; d += 1
                    assert st[q] == sig
                tag = ('genealogy', MODE, end, 'depth', d, 'b(q_j) vs q_j', tuple(sorted(set(comps))), 'all covers', all(covers) if covers else None,
                       'some late source', any(l > 0 for l in late))
                if end == 'first A-entry':
                    r = rs[0]
                    tag += ('q_d = a(r)', q == A[r], 'r vs q_d', rl(r, q), 'h(r) − (σ_d − 1)', h[r] - (sig - 1))
                    if d > 0: tag += ('q_{d−1} vs a(r)', rl(B and q0 if d == 0 else [q0][0], A[r]) if False else None,)
                C[tag] += 1
                if end.startswith('pure'): keep('pureB', n, dict(D, x=x, q=q0))
report()
