"""Rigid maps (log §34.3z¹⁵⁷): a(⊥) = ⊥, b(⊤) = ⊤, and x ↦ F(x, x) fixes only ⊥, ⊤ — the only case of the
orbit-height property not reduced to lower heights (HeightInduction.lean). Random census: frequency, orbit length
versus height, and further good diagonal post-fixed points m ∉ {⊥} (m ≤ F(m, m), τ(m) ≤ h(m)) besides ⊤.
  python3 rigid.py SEED SECONDS
"""
import sys, random, time, collections, json
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter(); ex = None
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.n > 40 or L.height < 2: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); n = L.n; le = L.le; rk = L.rank
        T['instances'] += 1
        if a_of(L, F, L.bot) != L.bot or b_of(L, F, L.top) != L.top: continue
        if any(F[c][c] == c for c in range(n) if c not in (L.bot, L.top)): continue
        T['rigid'] += 1; st = stages(L, F)
        T[('⊤ ∈ R_H', st[L.top] is not None and st[L.top] <= L.height)] += 1
        gp = [m for m in range(n) if m not in (L.bot, L.top) and le[m][F[m][m]] and st[m] is not None and st[m] <= rk[m]]
        T[('good diagonal post-fixed m ∉ {⊥, ⊤}', bool(gp))] += 1
        A = [a_of(L, F, x) for x in range(n)]
        gr = [x for x in range(n) if st[x] is not None and st[x] <= rk[x] and le[x][A[x]] and A[x] != x]
        T[('good x with x < a(x)', bool(gr))] += 1
        x = L.bot; chain = [x]                       # column-⊤ Kleene chain (b(⊤) = ⊤ ⇒ it reaches ⊤)
        while F[x][L.top] != L.top: x = F[x][L.top]; chain.append(x)
        xn = chain[-1]
        T[('column-⊤ chain: last x_n good', st[xn] is not None and st[xn] <= rk[xn])] += 1
        T[('column-⊤ chain: every x_i ∈ R_i', all(st[c] is not None and st[c] <= i for i, c in enumerate(chain)))] += 1
        T[('column-⊤ chain: every x_i good', all(st[c] is not None and st[c] <= rk[c] for c in chain))] += 1
        T[('column-⊤ chain: v = x_1 good', len(chain) > 1 and st[chain[1]] is not None and st[chain[1]] <= rk[chain[1]])] += 1
        gp = gp or gr
        T[('either', bool(gp))] += 1
        if not gp and (ex is None or n < ex[0]): ex = (n, L.S, F)
    for k, v in sorted(T.items(), key=str): print(k, v)
    if ex: print('smallest rigid without good post-fixed |L| =', ex[0]); json.dump(dict(sets=ex[1], F=ex[2]), open(f'rigid_s{sys.argv[1]}.json', 'w'))
