"""Forcedness of term-closure runs (log §34.3z¹³⁴).

Along the term-d-all run (closure under F, ∨, ∧), check whether every bad pair at every stage has exactly one
C-maximal separator. If so, every selection policy that adds a nonempty set of C-maximal separators per bad pair
(all, one, lookahead, any potential) produces the same run, so the run length bounds all of them from below.
  python3 forced_check.py DEPTH FILE...
"""
import sys, json
import separator_stages as ss
from look_rule import closure

def forced(L, F, D, depth):
    T = ss.mclose(L, {L.bot, L.top}); n = 0; widths = []
    while True:
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad): return n, widths
        n += 1; C = closure(L, F, set(T) | {F[x][y] for x, y in bad}, depth); new = set(); w = []
        for x, y in bad:
            cand = [s for s in C if L.le[F[x][y]][s] and not L.le[y][s]]
            mx = [s for s in cand if not any(t != s and L.le[s][t] for t in cand)]
            w.append(len(mx)); new |= set(mx)
        widths.append(max(w)); T = ss.mclose(L, set(T) | new)

if __name__ == '__main__':
    dep = None if sys.argv[1] == 'omega' else int(sys.argv[1])
    for f in sys.argv[2:]:
        d = json.load(open(f)); L = ss.Lat(d['sets']); n, w = forced(L, d['F'], d['D'], dep)
        print(f"{f}: depth {sys.argv[1]}, run length {n}, max number of C-maximal separators per bad pair by stage {w}, "
              f"forced {all(x == 1 for x in w)}, existential minimum {ss.exist_min(L, d['F'], d['D'])}", flush=True)
