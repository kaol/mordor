"""Local progress: does every state have a response-or-maximal successor that lowers the potential? (§34.3z¹³⁸)

For an instance and a stage potential Ψ (exist_cegar POT: gap, diff, lex), a state T (finite, meet-closed, ⊥, ⊤ ∈ T)
is *progressive* if it is goal, or some choice of one RM separator per bad pair gives T' that is goal or has
Ψ(T') < Ψ(T). Universal progress would make the greedy run descend from anywhere.
States tested: (a) all states reachable by RM runs with any choices; (b) random meet-closed families.
  python3 local_lex.py random SEED SECONDS | hard FILE...
"""
import sys, json, random, itertools, time, collections
import separator_stages as ss
import exist_cegar as ec
ec.RESPMAX = True
POTS = ('lex', 'gap', 'diff')

def goal(L, F, bad): return not bad or any(L.le[y][F[x][y]] for x, y in bad)

def progressive(L, F, D, T, pot, cap=20000):
    bad = ss.bad_pairs(L, F, D, T)
    if goal(L, F, bad): return True
    ec.POT = pot; M = ec.stage_potential(L, bad); n = 0
    for ch in itertools.product(*[ec.seps(L, F, x, y) for x, y in bad]):
        n += 1
        if n > cap: return None
        b2 = ss.bad_pairs(L, F, D, ss.mclose(L, set(T) | set(ch)))
        if goal(L, F, b2) or ec.stage_potential(L, b2) < M: return True
    return False

def reachable(L, F, D, cap=3000):
    seen = set(); st = [ss.mclose(L, {L.bot, L.top})]
    while st and len(seen) < cap:
        T = st.pop()
        if T in seen: continue
        seen.add(T); bad = ss.bad_pairs(L, F, D, T)
        if goal(L, F, bad): continue
        for ch in itertools.product(*[ec.seps(L, F, x, y) for x, y in bad]): st.append(ss.mclose(L, set(T) | set(ch)))
    return seen

def audit(L, F, D, tally, ex, rng, nrand=20):
    for T in reachable(L, F, D):
        for p in POTS:
            r = progressive(L, F, D, T, p); tally[('reachable', p, r)] += 1
            if r is False and (('reachable', p) not in ex or L.n < ex[('reachable', p)]['n']):
                ex[('reachable', p)] = dict(n=L.n, sets=L.S, F=F, D=D, T=sorted(T))
    for _ in range(nrand):
        T = ss.mclose(L, {L.bot, L.top} | {rng.randrange(L.n) for _ in range(rng.randint(1, 4))})
        for p in POTS:
            r = progressive(L, F, D, T, p); tally[('random T', p, r)] += 1
            if r is False and (('random', p) not in ex or L.n < ex[('random', p)]['n']):
                ex[('random', p)] = dict(n=L.n, sets=L.S, F=F, D=D, T=sorted(T))

if __name__ == '__main__':
    tally = collections.Counter(); ex = {}
    if sys.argv[1] == 'random':
        rng = random.Random(int(sys.argv[2])); t0 = time.time()
        while time.time() - t0 < float(sys.argv[3]):
            L = ss.Lat(ss.closure_system(rng.choice([4, 5]), rng.choice([6, 8, 10]), rng))
            if L.height < 3 or L.n > 18: continue
            _, g, gens = ss.random_instance(0, 0, rng, L)
            audit(L, ss.make_F(L, g), ss.Dof(L, gens), tally, ex, rng)
        tag = sys.argv[2]
    else:
        rng = random.Random(0)
        for f in sys.argv[2:]:
            for w in json.load(open(f)):
                L = ss.Lat(w['sets']); audit(L, w['F'], w['D'], tally, ex, rng)
        tag = 'hard'
    print(dict(sorted(tally.items(), key=str)), flush=True)
    for k, e in ex.items():
        print(f"smallest non-progressive {k}: |L| = {e['n']}", flush=True)
        json.dump(e, open(f"local_fail_{k[0].replace(' ', '')}_{k[1]}_{tag}.json", 'w'))
