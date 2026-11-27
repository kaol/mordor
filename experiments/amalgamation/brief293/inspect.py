"""Print a stored model: lattice (covers, heights), Z, rows of Z (descents, landings, mu), all Tb-at-meet violations."""
import sys, json
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation'); sys.path.insert(0, '/home/user/mordor/experiments/separation')
import bank
def show(d):
    m = bank.M(d['sets'], d['F']); L = m.L; le = m.le; h = m.h; F = m.F; n = m.n
    print(f'|L|={n} H={h[m.top]} bot={m.bot} top={m.top} Z={m.Z} atoms={m.atoms} M2={m.M2} d={m.d} N={m.N} branch={m.branch}')
    cov = {x: [y for y in L.covers_up[x]] for x in range(n)}
    print('heights:', {x: h[x] for x in range(n)})
    print('covers_up:', cov)
    print('bot-descent:', m.desc(m.bot))
    for x in m.Z:
        if x == m.bot: continue
        print(f' row {x} (h{h[x]}): desc {m.desc(x)} lam {m.lam(x)} idx {m.lidx(x)} exits {m.exits(x)} c {m.c(x)} mu {m.mu(x)}')
    for x in m.Z:
        print(f'  F({x},.)=', [F[x][y] for y in range(n)])
    print('phi =', [F[m.bot][y] for y in range(n)])
    return m
if __name__ == '__main__':
    D = json.load(open(sys.argv[1])); D = D if isinstance(D, list) else [D]
    for k in ([int(sys.argv[2])] if len(sys.argv) > 2 else range(len(D))):
        print('== model', k); show(D[k])
