"""Free census (no SAT): TRall = some x in L (x in Z with its own row, or x not in Z with any legit row g >= G_x)
satisfies TopRow''s hypothesis: its row lands at p and every colour atom c <= p has c <= x  (=> CertAtom, Lean
certAtom_of_topRow' + w0_of_T).  Quantifier: per stored W0+n1 model, exists x.  FAIL = no such x: on that model the
fixed atom is not produced by TopRow' from any single (real or virtual) row.  Failing models are saved to cex_trall.json."""
import lib, collections, json
print(__doc__)
D = [(n, w) for n, w, i, l in lib.get() if i]
C = collections.Counter(); out = []
for name, w in D:
    A = lib.colours(w); unb = not lib.bounded(w, A); L = w.L; F = w.F; le = w.le; h = w.h; n = w.n
    d, N = w.dN(); hi = [y for y in range(n) if h[y] >= 3]; low = [y for y in range(n) if h[y] <= 2]
    okp = lambda p, x: all(le[c][x] for c in A if le[c][p])
    zrow = [x for x in w.Z if okp(w.lam(x), x)]
    def search(x):
        zs = [z for z in w.Z if le[z][x]]
        G = [0] * n
        for y in range(n):
            v = w.bot
            for z in zs: v = L.join[v][F[z][y]]
            G[y] = v
        seen = set(); st = [w.top]
        while st:
            y = st.pop()
            if y in seen: continue
            seen.add(y)
            if any(le[G[y]][p] and le[p][y] and okp(p, x) for p in low): return True
            st.extend(y2 for y2 in hi if y2 != y and le[y2][y] and le[G[y]][y2] and y2 not in seen)
        return False
    vrow = [x for x in range(n) if x not in w.Z and search(x)]
    fx = [q for q in w.atoms if w.fixed(q)]
    tag = ('unb' if unb else 'bdd', '|A|=%d' % len(A), 'N1' if N == 1 else 'N>=2')
    res = 'holds(Z-row)' if zrow else ('holds(virtual only)' if vrow else 'FAIL')
    C[tag + (res,)] += 1
    if not zrow and not vrow:
        out.append(dict(sets=w.sets, F=w.F, src=name, refutes='TRall: some real or virtual row satisfies TopRow-prime hypothesis',
                        n=n, H=h[w.top], N=N, A=A, fixed=fx))
for k, v in sorted(C.items(), key=str): print(v, k)
out.sort(key=lambda m: m['n'])
print('FAIL models', len(out), 'smallest', [(m['src'], m['n'], m['H'], m['N'], m['A']) for m in out[:5]])
json.dump(out, open('cex_trall.json', 'w'))
