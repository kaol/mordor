import sys, json, collections; sys.path.insert(0, '.'); import bank
C = collections.Counter(); rows = []
for f in sys.argv[1:]:
    for d in json.load(open(f)):
        m = bank.M(d['sets'], d['F']); le = m.le; h = m.h; F = m.F
        Wt = [x for x in m.M2 if m.lam(x) == x]
        ex = [x for x in m.Z if m.exits(x)]
        lb = m.lam(m.bot)
        feats = dict(
            any_witness=bool(Wt),
            d_w=m.d in Wt, lamb_w=lb in Wt, lamb_inZ=lb in m.Z,
            noexit=not ex,
            w_above_d=any(le[m.d][x] for x in Wt),
            w_is_landing_of_atom=any(m.lam(q) == x for q in m.atoms for x in Wt),
            w_landing_of_below_atom=any(m.lam(q) == x and le[q][x] for q in m.atoms for x in Wt),
            w_stalls=any(F[x][x] == x for x in Wt),
            w_max_landing=any(all(not (le[x][y] and x != y) for y in m.M2) for x in Wt),
            every_M2_lands_inZ_or_w=all(x in Wt or m.lam(x) in m.Z for x in m.M2),
            some_w_above_every_atom_landing=any(all(not (m.lam(q) in m.Z) or le[m.lam(q)][x] or m.lam(q)==x for q in m.atoms) for x in Wt),
        )
        for k, v in feats.items(): C[(k, v)] += 1
        C['models'] += 1
for k in sorted(C, key=str): print(k, C[k])
