import sys, locate as W, lattices as LT
names=None; fails={}; tot=0
for spec in sys.argv[1:]:
    Ls = LT.parse(spec); Ls = Ls if isinstance(Ls, list) else [Ls]
    for L in Ls:
        S = W.Solver(L)
        for D in W.downsets(L):
            cs = W.cellsets(L, D); names = list(cs); tot += 1
            for k in ('maxD ∪ minU lines', 'bot/top lines ∪ maxD×minU', 'bot row ∪ maxD rows', 'top col ∪ minU cols'):
                if S.no_witness_possible(D, cs[k]): fails.setdefault(k, []).append((L.name, sorted(D)))
    print(spec, 'pairs so far', tot, {k: len(v) for k, v in fails.items()}, flush=True)
for k, v in fails.items(): print(k, v[:3])
