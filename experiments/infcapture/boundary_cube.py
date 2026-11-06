"""(Preorder model: named elements may coincide; the quotient is a poset with the same exact meets.)
First-entry boundary captors without a common outside lower point (log §34.3z¹¹⁰, brief work package A).

Finite partial order with exact meets (Dedekind–MacNeille completes it): start column ⊤, rows g₁..g_k ∈ D (maximal
among named D-elements), m = ⋀ g, orbits γᵢ(n) with γᵢ(n+1) = F(gᵢ, γᵢ(n)), first entry at Nᵢ + 1, grid columns
W(t) = ⋀ γᵢ(tᵢ) (exact glb), a prescribed D-shape of the grid, cells F(row, W(t)) for rows gᵢ and m, monotone, no
witness on every cross cell. For chosen boundary points t we add NEW maximal capturers P_t ≥ W(t) (W(t) below no
gᵢ: the uncaptured case) and ask whether the meet of a chosen set of capturers can lie below m.
`cube_escape` (Lean) forbids it whenever the chosen points lie below π s + 1 for an outside s."""
import itertools, sys
from z3 import *

def run(N, Dmin, chosen, label, meet=True, uncaptured=True):
    k = len(N); box = list(itertools.product(*[range(n + 2) for n in N]))
    ge = lambda a, b: all(x >= y for x, y in zip(a, b))
    inDgrid = {t: any(ge(t, d) for d in Dmin) for t in box} if Dmin is not None else None
    def wname(t):
        nz = [i for i in range(k) if t[i] > 0]
        if not nz: return 'top'
        if len(nz) == 1: return f"y{nz[0]}_{t[nz[0]]}"
        return 'W' + ''.join(map(str, t))
    rows = [f"g{i}" for i in range(k)] + ['m']
    cols = list(dict.fromkeys(wname(t) for t in box))
    caps = {t: 'P' + ''.join(map(str, t)) for t in chosen}
    cell = {(r, c): f"F[{r},{c}]" for r in rows for c in cols}
    E = list(dict.fromkeys(['bot', 'top'] + rows + cols + list(caps.values()) + ['Mcap'] + list(cell.values())))
    s = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}; inD = {a: Bool(f"D|{a}") for a in E}
    for a in E:
        s.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            for c in E: s.add(Implies(And(le[a, b], le[b, c]), le[a, c]))
            s.add(Implies(And(le[a, b], inD[b]), inD[a]))
    def glb(z, q): s.add([le[z, x] for x in q]); s.add([Implies(And([le[w, x] for x in q]), le[w, z]) for w in E])
    glb('m', [f"g{i}" for i in range(k)])
    for t in box:
        nz = [i for i in range(k) if t[i] > 0]
        if len(nz) >= 2: glb(wname(t), [f"y{i}_{t[i]}" for i in nz])
    s.add(inD['bot'], Not(inD['top']))
    if inDgrid is not None:
        for t in box: s.add(inD[wname(t)] if inDgrid[t] else Not(inD[wname(t)]))
    else:   # free shape: only the orbit facts (axes outside up to N, faces inside)
        for t in box:
            if any(t[i] == N[i] + 1 for i in range(k)): s.add(inD[wname(t)])
            if sum(1 for i in range(k) if t[i] > 0) <= 1 and all(t[i] <= N[i] for i in range(k)): s.add(Not(inD[wname(t)]))
    named_D_max = [f"g{i}" for i in range(k)] + list(caps.values())
    for p in named_D_max:
        s.add(inD[p]); s.add([Not(And(le[p, w], inD[w])) for w in E if w != p])
    for a, b in itertools.permutations(named_D_max, 2): s.add(Not(le[a, b]))
    for (r, c), v in cell.items():
        for (r2, c2), v2 in cell.items():
            if (r, c) != (r2, c2): s.add(Implies(And(le[r, r2], le[c, c2]), le[v, v2]))
        s.add(Implies(And(inD[r], Not(inD[c])), And(Not(le[v, r]), Not(le[c, v]))))
    for i in range(k):
        for n in range(N[i] + 1):
            src = 'top' if n == 0 else f"y{i}_{n}"; dst = f"y{i}_{n + 1}"
            s.add(le[cell[(f"g{i}", src)], dst], le[dst, cell[(f"g{i}", src)]])
    for t, P in caps.items():
        s.add(le[wname(t), P])
        if uncaptured: s.add([Not(le[wname(t), f"g{i}"]) for i in range(k)])
    if caps: glb('Mcap', list(caps.values()))
    if meet: s.add(le['Mcap', 'm'])
    r = s.check()
    if r == sat and Dmin is None:
        mo = s.model(); Dset = [t for t in box if is_true(mo.eval(inD[wname(t)], model_completion=True))]
        mins = [t for t in Dset if not any(d != t and ge(t, d) for d in Dset)]
        print(f"   free-shape model: minimal D-valued grid points {sorted(mins)}", flush=True)
    print(f"[{label}] N={N}, boundary {sorted(Dmin) if Dmin is not None else "free"}, capturers of {sorted(chosen)} (meet ≤ m imposed: {meet}, uncaptured: {uncaptured}): {r}", flush=True)
    return r

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'base':
    N = (2, 2); Dmin = [(3, 0), (2, 1), (1, 2), (0, 3)]
    run(N, Dmin, [], 'base, no capturers', meet=False)
    for NN in [(2, 2), (1, 2), (2, 3), (1, 3)]:
        run(NN, None, [], 'free shape, no capturers', meet=False)
    run(N, Dmin, [(3, 0), (1, 2)], 'base with capturers', meet=False)
    run(N, Dmin, [(3, 0), (1, 2)], 'base with capturers, captured allowed', meet=False, uncaptured=False)
    sys.exit()
if __name__ == '__main__':
    N = (2, 2); Dmin = [(3, 0), (2, 1), (1, 2), (0, 3)]
    run(N, Dmin, [(2, 1), (1, 2)], 'control: common outside lower point (1,1)')
    run(N, Dmin, [(3, 0), (2, 1)], 'control: common outside lower point (2,0)')
    run(N, Dmin, [(3, 0), (1, 2)], 'no common outside lower point')
    run(N, Dmin, [(3, 0), (0, 3)], 'face points, no common outside lower point')
    run(N, Dmin, [(3, 0), (2, 1), (1, 2)], 'triple, pairwise adjacent only')
