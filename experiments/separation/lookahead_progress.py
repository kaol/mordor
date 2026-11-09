"""k-step progress: does every reachable state have an RM continuation of ≤ k steps reaching goal or a strictly
lower stage potential? (log §34.3z¹³⁹)

k = 1 is `local_lex.progressive`. Universal k-progress for a bounded potential would make greedy k-lookahead
terminate. Tested on all RM-reachable states of random instances (same generator as local_lex.py) and of the hard
witnesses; reports counts of states that are not k-progressive for k = 1, 2, 3.
  python3 lookahead_progress.py random SEED SECONDS | hard FILE...
"""
import sys, json, random, itertools, time, collections
import separator_stages as ss
import exist_cegar as ec
from local_lex import reachable, goal
ec.RESPMAX = True

def kprog(L, F, D, T, pot, k, M=None, memo=None):
    bad = ss.bad_pairs(L, F, D, T)
    if goal(L, F, bad): return True
    ec.POT = pot; P = ec.stage_potential(L, bad)
    if M is not None and P < M: return True
    if M is None: M = P
    if k == 0: return False
    memo = {} if memo is None else memo
    key = (T, k)
    if key in memo: return memo[key]
    res = False
    for ch in itertools.product(*[ec.seps(L, F, x, y) for x, y in bad]):
        if kprog(L, F, D, ss.mclose(L, set(T) | set(ch)), pot, k - 1, M, memo): res = True; break
    memo[key] = res; return res

def audit(L, F, D, tally, ex):
    for T in reachable(L, F, D):
        for pot in ('lex', 'gap'):
            for k in (1, 2, 3):
                r = kprog(L, F, D, T, pot, k)
                tally[(pot, k, r)] += 1
                if r: break
                if k == 3 and ((pot,) not in ex or L.n < ex[(pot,)]['n']):
                    ex[(pot,)] = dict(n=L.n, sets=L.S, F=F, D=D, T=sorted(T))

if __name__ == '__main__':
    tally = collections.Counter(); ex = {}
    if sys.argv[1] == 'random':
        rng = random.Random(int(sys.argv[2])); t0 = time.time()
        while time.time() - t0 < float(sys.argv[3]):
            L = ss.Lat(ss.closure_system(rng.choice([4, 5]), rng.choice([6, 8, 10]), rng))
            if L.height < 3 or L.n > 18: continue
            _, g, gens = ss.random_instance(0, 0, rng, L)
            audit(L, ss.make_F(L, g), ss.Dof(L, gens), tally, ex)
    else:
        for f in sys.argv[2:]:
            for w in json.load(open(f)): audit(ss.Lat(w['sets']), w['F'], w['D'], tally, ex)
    print("(potential, k, k-progressive) -> states (a state is counted at k = 1, 2, 3 until it becomes progressive):",
          dict(sorted(tally.items(), key=str)), flush=True)
    for k, e in ex.items():
        print(f"smallest state not 3-progressive for {k[0]}: |L| = {e['n']}", flush=True)
        json.dump(e, open(f"lookahead_fail_{k[0]}.json", "w"))
