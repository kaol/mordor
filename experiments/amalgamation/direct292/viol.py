import sys, json, collections; sys.path.insert(0, '.'); import bank
C = collections.Counter()
for f in sys.argv[1:]:
    for k, d in enumerate(json.load(open(f))):
        m = bank.M(d['sets'], d['F']); L = m.L; le = m.le; h = m.h; F = m.F
        V = []
        for q in m.atoms:
            dq = m.desc(q)
            for x in m.Z:
                if not le[q][x]: continue
                dx = m.desc(x)
                for i, u in enumerate(dq):
                    for j, v in enumerate(dx):
                        w = L.meet[u][v]
                        if h[w] > 2 and le[F[q][w]][q]:
                            V.append((q, x, i, j, u, v, w, F[q][w]))
        kinds = set()
        for (q, x, i, j, u, v, w, val) in V:
            kinds.add(('x=q' if x == q else ('xM2' if h[x] == 2 else 'xatom'), 'u=lastHigh' if i == m.lidx(q) - 1 else f'u@{i}/{m.lidx(q)}', 'v=lastHigh' if j == m.lidx(x) - 1 else f'v@{j}/{m.lidx(x)}', 'val=bot' if val == m.bot else 'val=q'))
        if k < 3 or len(sys.argv) > 2: print(f.split('/')[-1], k, 'n', m.n, 'branch', m.branch, 'N', m.N, 'viol', len(V), sorted(kinds)[:6])
        for kd in kinds: C[kd] += 1
for k_, v_ in C.most_common(): print(v_, k_)
