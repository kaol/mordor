"""Cut Lemma counterexample hunt on larger lattices.  Usage: python3 hunt.py pi4|b5|c3cubed SECONDS"""
import sys, time, itertools, random
from lat import *
from cutlemma import cut_counterexample_exists
def partitions(s):
    if not s: yield []; return
    f, rest = s[0], s[1:]
    for p in partitions(rest):
        yield [[f]] + p
        for i in range(len(p)): yield p[:i] + [[f] + p[i]] + p[i+1:]
def Pi(k):
    P = [frozenset(frozenset(b) for b in p) for p in partitions(list(range(k)))]
    ref = lambda p, q: all(any(b <= c for c in q) for b in p)
    return Lattice(len(P), [[ref(p, q) for q in P] for p in P], f"Pi{k}")
def run(L, Ds, label, budget):
    t = time.time(); c = 0
    for D in Ds:
        if time.time() - t > budget: break
        c += 1
        if cut_counterexample_exists(L, D): print("COUNTEREXAMPLE", L.name, sorted(D), flush=True); return
    print(f"{label}: {c} down-sets checked, 0 counterexamples ({time.time()-t:.0f}s)", flush=True)
which, budget = sys.argv[1], float(sys.argv[2])
if which == "pi4":
    L = Pi(4); run(L, list(downsets(L)), "Pi4 (all down-sets)", budget)
elif which == "b5":
    seen, reps, rng = set(), [], random.Random(5)
    canon = lambda D: min(tuple(sorted(sum(1 << p[i] for i in range(5) if s >> i & 1) for s in D)) for p in itertools.permutations(range(5)))
    for _ in range(20000):
        gens = rng.sample(range(32), rng.randint(1, 6)); D = {x for x in range(32) if any(x & g == x for g in gens)}
        if 31 not in D and canon(D) not in seen: seen.add(canon(D)); reps.append(D)
    run(powerset(5), reps, f"B5 ({len(reps)} down-set orbit representatives)", budget)
else:
    C = product(product(chain(3), chain(3)), chain(3)); rng = random.Random(7); Dl = []
    for _ in range(400):
        gens = rng.sample(range(27), rng.randint(1, 5)); D = {x for x in range(27) if any(C.leq[x][g] for g in gens)}
        if C.top not in D: Dl.append(D)
    run(C, Dl, "C3^3 (random down-sets)", budget)
