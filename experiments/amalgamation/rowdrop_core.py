"""§34.3z²⁶⁸: RowDrop at N = 2, independent encoding (one-hot roles, no descent variables), with role-level tightness facts
as solver assumptions; reports which facts are needed (minimal UNSAT cores).

World (hard): a(bot) = bot, top not in R_2; roles u1 = F(bot, top), d = F(bot, u1) with h(d) = 2, F(bot, d) = bot, u1 != d
(so N = 2); v1 = F(d, top); s = F(bot, v1).
Negated claim (hard): s not <= d.            => SAT = RowDrop fails under the assumed facts.
Facts (assumptions):
  S   s not in R_2              AD  a(d) has height <= 2        ZT  Z = R_1 has heights <= 2
  Ubd F(d, u1) not <= d (b(u1) not <= d)   Uad  u1 not <= a(d)   Ule  u1 not <= F(d, u1)
  U   u1 not in R_2             V   v1 not in R_2               T   full tightness (R_2 heights <= 2)
Flag noTop drops the hard fact 'top not in R_2'; anyd allows d of any height > 0; noA drops a(bot) = bot. Each SAT model is replayed in Python (stages, a_of).
  python3 rowdrop_core.py (sweep N MAX | closure K M SEED CNT) FACTS...      e.g. FACTS = S AD ZT U V  or  T"""
import sys, collections, itertools
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import lattices
from rstages import stages, a_of
ALL = ['S', 'AD', 'ZT', 'U', 'V', 'T', 'Ubd', 'Uad', 'Ule', 'noTop', 'anyd', 'noA']
FACTS = [a for a in sys.argv[1:] if a in ALL]; args = [a for a in sys.argv[1:] if a not in ALL]
print('rowdrop_core | SAT = RowDrop (N = 2) fails under facts', FACTS, '| UNSAT = RowDrop follows from them; core = a minimal sufficient subset')
C = collections.Counter(); CORES = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; top = L.top; bot = L.bot
    if L.height < 3: continue
    E = Enc(L, 2); f = lambda a, b, u: E.v('f', a, b, u); r = lambda i, z: E.v('r', i, z); add = E.S.add_clause; A = lambda x, g: E.v('A', x, g)
    if 'noA' not in FACTS: add([A(bot, bot)])
    if 'noTop' not in FACTS: add([-r(2, top)])
    def onehot(name, dom):
        ls = [E.v(name, x) for x in dom]; add(ls)
        for p, q in itertools.combinations(ls, 2): add([-p, -q])
        for x in range(n):
            if x not in dom: add([-E.v(name, x)])
        return lambda x: E.v(name, x)
    U = onehot('U', list(range(n))); DOM = [x for x in range(n) if (x != bot if 'anyd' in FACTS else h[x] == 2)]; D = onehot('D', DOM); V = onehot('V', list(range(n))); S = onehot('S', list(range(n)))
    for u in range(n):
        add([-U(u), f(bot, top, u)])
        for d in DOM: add([-U(u), -D(d), f(bot, u, d)])
    for d in range(n):
        if d not in DOM: continue
        add([-D(d), f(bot, d, bot)]); add([-D(d), -U(d)])
        for v in range(n): add([-D(d), -V(v), f(d, top, v)])
        for s in range(n):
            if le[s][d]: add([-D(d), -S(s)])
    for v in range(n):
        for s in range(n): add([-V(v), -S(s), f(bot, v, s)])
    lit = {k: E.v('fact', k) for k in ALL}
    high = [z for z in range(n) if h[z] > 2]
    for x in range(n):
        add([-lit['S'], -S(x), -r(2, x)]); add([-lit['U'], -U(x), -r(2, x)]); add([-lit['V'], -V(x), -r(2, x)])
        if x in DOM:
            for g in high: add([-lit['AD'], -D(x), -A(x, g)])
    for z in high: add([-lit['ZT'], -r(1, z)]); add([-lit['T'], -r(2, z)])
    for u in range(n):
        for d in DOM:
            add([-lit['Ubd'], -U(u), -D(d)] + [f(d, u, w) for w in range(n) if not le[w][d]])
            add([-lit['Ule'], -U(u), -D(d)] + [f(d, u, w) for w in range(n) if not le[u][w]])
            for g in range(n):
                if le[u][g]: add([-lit['Uad'], -U(u), -D(d), -A(d, g)])
    assum = [lit[k] for k in FACTS if k not in ('noTop', 'anyd', 'noA')]
    if E.S.solve(assumptions=assum):
        F = E.decode(); st = stages(L, F); inR = lambda x, i: st[x] is not None and st[x] <= i
        u1 = F[bot][top]; d = F[bot][u1]; v1 = F[d][top]; s = F[bot][v1]; ad = a_of(L, F, d)
        ok = ('noA' in FACTS or a_of(L, F, bot) == bot) and ('noTop' in FACTS or not inR(top, 2)) and (h[d] == 2 or ('anyd' in FACTS and d != bot)) and F[bot][d] == bot and u1 != d and not le[s][d]
        if 'S' in FACTS: ok = ok and not inR(s, 2)
        if 'U' in FACTS: ok = ok and not inR(u1, 2)
        if 'V' in FACTS: ok = ok and not inR(v1, 2)
        if 'AD' in FACTS: ok = ok and h[ad] <= 2
        if 'Ubd' in FACTS: ok = ok and not le[F[d][u1]][d]
        if 'Uad' in FACTS: ok = ok and not le[u1][ad]
        if 'Ule' in FACTS: ok = ok and not le[u1][F[d][u1]]
        if 'ZT' in FACTS: ok = ok and all(h[z] <= 2 for z in range(n) if inR(z, 1))
        if 'T' in FACTS: ok = ok and all(h[z] <= 2 for z in range(n) if inR(z, 2))
        assert ok, 'SAT/Python mismatch'
        C['SAT'] += 1
        if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F))
    else:
        C['UNSAT'] += 1
        core = [k for k in FACTS if k not in ('noTop', 'anyd', 'noA') and lit[k] in set(E.S.get_core() or [])]
        for k in list(core):                       # deletion-minimise
            trial = [lit[j] for j in core if j != k]
            if not E.S.solve(assumptions=trial): core = [j for j in core if j != k]
        CORES['+'.join(core) or '(none: RowDrop holds with no fact)'] += 1
    E.S.delete()
print(FACTS, args, dict(C), 'smallest SAT', best[0] if best else None)
for k, v in sorted(CORES.items()): print('  minimal core', k, v)
if best:
    import json; json.dump(best[1], open(f'rowdrop_core_{"_".join(FACTS)}_min{best[0]}.json', 'w'))
