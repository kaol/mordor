import sys, json, glob, collections; sys.path.insert(0, '.'); import bank
C = collections.Counter()
for f in glob.glob(sys.argv[1] + '/r3_cgone_*.json'):
    for d in json.load(open(f)):
        m = bank.M(d['sets'], d['F']); L = m.L; F = m.F; h = m.h; le = m.le; A, B = d['colours']
        v = m.desc(A); w = m.desc(B)
        i = next(j for j, z in enumerate(v) if h[z] <= 2); i2 = next(k for k, z in enumerate(w) if h[z] <= 2)
        J = L.join[A][B]
        D = lambda j, k: L.meet[v[min(j, len(v) - 1)]][w[min(k, len(w) - 1)]]
        brk = 0; ok_a = []
        for l in range(i):
            kap = next(k for k in range(len(w) + 5) if h[D(l, k)] <= 2)
            Bl = D(l, kap - 1); e = F[m.bot][Bl]; Al = D(l, kap)
            ok_a.append(le[A][e])
            if Al == J and J not in m.Z and F[m.bot][J] == B: brk += 1
        C[('break occurs', brk > 0)] += 1
        C[('all e >= a', all(ok_a))] += 1
        C[('shadow a <= phi(r_a)', le[A][F[m.bot][v[i - 1]]])] += 1
for k in sorted(C, key=str): print(k, C[k])
