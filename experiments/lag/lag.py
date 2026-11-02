"""Lagged comparison calibration (log §34.3z⁸⁷), z3, two generators p1, p2, r = p1 ⊓ p2, h = F(r, ·).

Columns: s, s' = F(p1, s), the h-orbits of s and s' up to their entries (s enters at step n+1, s' at step n'+1),
and z = w_s ⊓ w_{s'} (glb of the last points, also used as a column). F on rows {p1, p2, r} × all named columns,
monotone, witness-free. Lemmas (L), lagged_time, (M) are consequences of the encoding.
Cases: s contracting for p1 (F(p1, s) ≤ s) or not (F(p1, s) ∥ s, the sink situation); A1 (n' = n − 1) or
A2 (n' ≥ n); labels of the two entries equal or opposite."""
import itertools
from z3 import *
def run(contract, n, n2, lab_s, lab_t):
    P = ['p1', 'p2']; rows = P + ['r']
    so = ['s'] + [f"s_{k}" for k in range(1, n + 1)]          # orbit points 0..n outside, entry at n+1
    to = ['t'] + [f"t_{k}" for k in range(1, n2 + 1)]
    cols = ['top'] + so + to + ['z']
    val = {(a, c): f"F[{a},{c}]" for a in rows for c in cols}
    E = ['bot'] + rows + cols + list(val.values())
    S = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}
    for a in E:
        S.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            for c in E: S.add(Implies(And(le[a, b], le[b, c]), le[a, c]))
    inD = {a: Or([le[a, q] for q in P]) for a in E}
    S.add(Not(le['p1', 'p2']), Not(le['p2', 'p1']))
    S.add(le['r', 'p1'], le['r', 'p2'], *[Implies(And(le[w, 'p1'], le[w, 'p2']), le[w, 'r']) for w in E])
    S.add([inD[a] for a in rows]); S.add([Not(inD[c]) for c in cols if c != 'z'])
    for (a, c), v in val.items():
        for (a2, c2), v2 in val.items():
            if (a, c) != (a2, c2): S.add(Implies(And(le[a, a2], le[c, c2]), le[v, v2]))
        S.add(Implies(Not(inD[c]), And(Not(le[v, a]), Not(le[c, v]))))
    eq = lambda a, b: And(le[a, b], le[b, a])
    S.add(eq('t', val['p1', 's']))
    S.add(le[val['p1', 's'], 's'] if contract else And(Not(le[val['p1', 's'], 's']), Not(le['s', val['p1', 's']])))
    for orb in (so, to):
        for k in range(len(orb) - 1): S.add(eq(orb[k + 1], val['r', orb[k]]))
    es, et = val['r', so[-1]], val['r', to[-1]]
    S.add(inD[es], inD[et], le[es, lab_s], le[et, lab_t])
    S.add(le['z', so[-1]], le['z', to[-1]], *[Implies(And(le[w, so[-1]], le[w, to[-1]]), le[w, 'z']) for w in E])
    return S.check()
for contract in [False, True]:
    for n in [1, 2]:
        for n2 in range(max(0, n - 1), n + 2):
            for ls, lt in [('p1', 'p1'), ('p1', 'p2')]:
                case = 'A1' if n2 == n - 1 else 'A2'
                print(f"{'contracting' if contract else 'non-contracting'} start, n={n}, n'={n2} ({case}), labels {ls[-1]}/{lt[-1]}: "
                      f"{run(contract, n, n2, ls, lt)}", flush=True)
