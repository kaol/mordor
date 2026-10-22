"""Threshold windows for the configuration E | B m ... m (L1 element alone; L2 chain of any length N, B at the bottom).
D ∩ {(⊥, c)} and D ∩ {(⊤, c)} (coordinate 1 on the L2 chain) are chain prefixes with last indices t_bot ≥ t_top.
Window = chain ends, B, and the two elements straddling each threshold; gaps elsewhere; D fixed on those points.
Each window is a sound abstraction; the set of compressed shapes is the same for all large N."""
import sys
from omega_window import *
N2 = ('nb', 2)

def shapes(N, lines=('b1', 't1')):
    out = {}
    rng = range(-1, N)
    for tb in rng:
        for tt in rng:
            if tt > tb: continue
            W = {0, N - 1}
            for t in (tb, tt):
                for i in (t, t + 1):
                    if 0 <= i < N: W.add(i)
            idx = sorted(W)
            toks, pos = [], {}
            for k, i in enumerate(idx):
                if k and i > idx[k - 1] + 1: toks.append(Z2)
                pos[i] = len(toks)
                toks.append(G2 if i == 0 else N2)
            key = (tuple(toks), tuple(sorted((pos[i], i <= tb, i <= tt) for i in idx)))
            out[key] = (tb, tt)
    return out

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    sh = shapes(N)
    print(f"{len(sh)} threshold shapes", flush=True)
    bad = 0
    for (toks, dinfo), (tb, tt) in sorted(sh.items(), key=lambda kv: str(kv[0])):
        dfix = {}
        for p, inb, intt in dinfo:
            c = (1, p)
            dfix[(B, c, 0)] = inb
            dfix[(T, c, 0)] = intt
        r = run(((G1,), toks), dfix=dfix, label=f"t_bot={tb} t_top={tt}")
        bad += bool(r)
    print("SAT shapes:", bad)
