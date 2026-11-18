"""Bare SAT check (log §34.3z¹⁹⁵): with only R_K tight and some rank-K element new at stage K, can the pure A-chain
a^i(⊥), i ≤ K − 1, reach rank K?  Every Moore family on 4 points, every K.   python3 pajump_bare.py"""
import sys
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import lattices
from rstages import stages, a_of
res = {}
for L in lattices(['sweep', '4', '16']):
    n = L.n; rk = L.rank
    for K in range(2, L.height + 1):
        for tightK1 in (False,):
            E = Enc(L, K + 1); r = lambda j, z: E.v('r', j, z); A = lambda x, g: E.v('A', x, g)
            for z in range(n):
                if rk[z] > K: E.S.add_clause([-r(K, z)])
                if tightK1 and rk[z] > K - 1: E.S.add_clause([-r(K - 1, z)])
            Sc = lambda i, g: E.v('chain', i, g)
            for g in range(n): E.S.add_clause([Sc(0, g)] if g == L.bot else [-Sc(0, g)])
            for i in range(K - 1):
                for g in range(n):
                    lits = []
                    for g2 in range(n):
                        o = E.v('cs', i, g2, g); E.iff_and(o, [Sc(i, g2), A(g2, g)]); lits.append(o)
                    E.iff_or(Sc(i + 1, g), lits)
            E.S.add_clause([Sc(i, g) for i in range(K) for g in range(n) if rk[g] == K])
            news = [E.v('mnew', z) for z in range(n) if rk[z] == K]
            for z in range(n):
                if rk[z] == K:
                    o = E.v('mnew', z); E.iff_and(o, [r(K, z), -r(K - 1, z)])
            if not news: E.S.delete(); continue
            E.S.add_clause(news)
            sat = E.S.solve()
            key = 'R_K tight + a new rank-K element of R_K'
            res.setdefault(key, [0, 0, None]); res[key][0 if sat else 1] += 1
            if sat:
                F = E.decode(); c = L.bot; ch = [c]
                for i in range(K): c = a_of(L, F, c); ch.append(c)
                st = stages(L, F)
                if res[key][2] is None or n < res[key][2][0]: res[key][2] = (n, K, [rk[x] for x in ch], [st[x] for x in ch], L.S, F)
            E.S.delete()
for k, v in res.items(): print(k, 'sat', v[0], 'unsat', v[1], 'smallest', v[2])
