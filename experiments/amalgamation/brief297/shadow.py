"""Free check (no SAT) of the SHADOW lemma on NoFix two-unbounded-colour models (any relaxed world):
  hypothesis: ColourGain holds at the colour row b (lambda(b) >= a), both colour rows land.
  SHADOW(a):  a <= phi(r_a), r_a = last high element of row a's descent.
Quantifier: every model, every ordered colour pair (a, b) meeting the hypothesis.  FAIL = phi(r_a) not >= a.
Also reported: STEP1(b): a <= phi(r_b) (paper consequence of CG at b and NoFix; FAIL = paper step wrong)."""
import sys, json, collections
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W
import lib
print(__doc__)
C = collections.Counter(); bad = []
for fn in sys.argv[1:]:
    D = json.load(open(fn)); D = D if isinstance(D, list) else [D]
    for k, m in enumerate(D):
        w = W(m['sets'], m['F']); A = lib.colours(w); F = w.F; le = w.le
        if len(A) != 2 or lib.bounded(w, A) or not w.nofix(): continue
        if any(w.lidx(c) is None for c in A): continue
        cg = {c: any(le[c2][w.lam(c)] and not le[c2][c] for c2 in A) for c in A}
        r = {c: w.desc(c)[w.lidx(c) - 1] for c in A}
        for b in A:
            a = A[0] if b == A[1] else A[1]
            if not cg[b]: continue
            s1 = le[a][F[w.bot][r[b]]]; sh = le[a][F[w.bot][r[a]]]
            C[('STEP1(b)', s1)] += 1
            C[('SHADOW(a)', 'CG(a)=%s' % cg[a], sh)] += 1
            if not sh: bad.append((fn, k, w.n, a, b))
for k_, v in sorted(C.items(), key=str): print(v, k_)
print('SHADOW failures', len(bad), bad[:10])
