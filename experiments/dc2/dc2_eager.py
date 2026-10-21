"""Eager version of dc2_lazy: master plus one block copy per pool atom b, every block clause guarded by used(b).

Same soundness argument as dc2_lazy (block = restriction to cells over S1 ∪ {b} composed with π_b); the projection
is encoded by equivalences between block-side values at master pairs and master variables:
  pv(c, i, b) ↔ V(c, i, b),   pv(c, i, o) ↔ isL2(c, i) ∧ ¬V(c, i, b),   pv(c, i, a) ↔ V(c, i, a) otherwise.
Unused pool atoms impose nothing, so instance (k, m) covers every counterexample with |L1| = k and |L2| ≤ m."""
import sys, time, itertools
from pysat.solvers import Cadical153
import dc2_lazy as d
from dc2_lazy import B, T, O, cle

def run(k, m, n, verbose=True):
    d.LAYERS = list(range(n))
    I = d.Inst(k, m, n)
    S, V, pairs, dom = d.build_master(I)
    lev0 = lambda p: p[0] in (B, T) and p[1] in (B, T)
    t0 = time.time()
    for b in ([] if d.SKIP_BLOCKS else I.L2):
        u = V('used', b)
        cb = I.c1 + [b]
        Pb = [(x0, x1, l) for x0 in cb for x1 in cb for l in range(n)]
        hasb = lambda p: b in p[:2]
        # D on b-points: shared variable namespace ('D', p) is fine, b-points are distinct per b
        dm = lambda p: V('D', p)
        # downset edges from b-points down to S1-points and up from S1-points to b-points
        for p in Pb:
            for q in I.covers(p, cb):
                if hasb(p) or hasb(q): S.add_clause([-u, -dm(q), dm(p)])
        pdom = [B, T] + I.L1 + [b, O]
        W = lambda c, i, a: V('pv', b, c, i, a)      # block-side value at a pair (projected)
        bpairs = [(x, y) for x in Pb for y in Pb if not I.ple(y, x) and (hasb(x) or hasb(y))]
        # block pairs: one-hot (guarded), witness-free
        for x, y in bpairs:
            for i in range(2):
                lits = [W((x, y), i, a) for a in pdom]
                S.add_clause([-u] + lits)
                for p_, q_ in itertools.combinations(lits, 2): S.add_clause([-u, -p_, -q_])
            lits = [W((x, y), 2, l) for l in d.LAYERS]
            S.add_clause([-u] + lits)
            for p_, q_ in itertools.combinations(lits, 2): S.add_clause([-u, -p_, -q_])
            g = [-u, -dm(x), dm(y)]
            if d.WIT != 'hi': S.add_clause(g + [W((x, y), i, a) for i in range(2) for a in pdom if not cle(a, x[i])] + [W((x, y), 2, l) for l in d.LAYERS if l > x[2]])
            if d.WIT != 'lo': S.add_clause(g + [W((x, y), i, a) for i in range(2) for a in pdom if not cle(y[i], a)] + [W((x, y), 2, l) for l in d.LAYERS if l < y[2]])
        # projection of master pairs adjacent to block pairs
        mp = set()
        for x, y in bpairs:
            for x2 in I.covers(x, cb):
                if not I.ple(y, x2) and not (hasb(x2) or hasb(y)): mp.add((x2, y))
            for y2 in I.covers(y, cb):
                if not I.ple(y2, x) and not (hasb(x) or hasb(y2)): mp.add((x, y2))
            # predecessors: master pairs below block pairs
        for x, y in [(x, y) for x in I.P1 for y in I.P1 if not I.ple(y, x)]:
            for x2 in I.covers(x, cb):
                if hasb(x2) and not I.ple(y, x2): mp.add((x, y))
            for y2 in I.covers(y, cb):
                if hasb(y2) and not I.ple(y2, x): mp.add((x, y))
        for c in mp:
            ldom = dom(*c)
            for i in range(2):
                for a in pdom:
                    w = W(c, i, a)
                    if a == b: e = V('v', *c, i, b) if b in ldom else None
                    elif a == O:
                        # projected o: the master value is o, or an L2 atom other than b
                        parts = []
                        if b in ldom:
                            q = V('pvq', b, c, i)
                            S.add_clause([-q, V('isL2', *c, i)]); S.add_clause([-q, -V('v', *c, i, b)])
                            S.add_clause([q, -V('isL2', *c, i), V('v', *c, i, b)])
                            parts.append(q)
                        if O in ldom: parts.append(V('v', *c, i, O))
                        if not parts: e = None
                        else:
                            e = V('pvo', b, c, i)
                            S.add_clause([-e] + parts)
                            for q in parts: S.add_clause([e, -q])
                    else: e = V('v', *c, i, a)
                    if e is None: S.add_clause([-w])
                    else: S.add_clause([-w, e]); S.add_clause([w, -e])
            for l in d.LAYERS:
                S.add_clause([-W(c, 2, l), V('v', *c, 2, l)]); S.add_clause([W(c, 2, l), -V('v', *c, 2, l)])
        # monotonicity along covers touching block pairs
        allp = set(bpairs) | mp
        for x, y in allp:
            for x2 in I.covers(x, cb):
                c2 = (x2, y)
                if c2 in allp and ((x, y) in set(bpairs) or c2 in set(bpairs)):
                    d_mono(S, W, (x, y), c2, pdom, [-u, -dm(x2), dm(y)])
            for y2 in I.covers(y, cb):
                c2 = (x, y2)
                if c2 in allp and ((x, y) in set(bpairs) or c2 in set(bpairs)):
                    d_mono(S, W, (x, y), c2, pdom, [-u, -dm(x), dm(y)])
    if d.SEL0:
        sels = {V('sel0', x, y): (x, y) for x, y in pairs if ('sel0', x, y) in V.d}
        cur = list(sels)
        if S.solve(assumptions=cur): return 'SAT-all-closed'
        cur = list(S.get_core()); i = 0
        while i < len(cur):
            trial = cur[:i] + cur[i + 1:]
            if not S.solve(assumptions=trial):
                c = set(S.get_core()); cur = [l for l in trial if l in c]
            else: i += 1
        return [sels[l] for l in cur]
    r = S.solve()
    if verbose: print(f"k={k} m={m} n={n}: {'SAT' if r else 'UNSAT'} [{time.time()-t0:.0f}s]", flush=True)
    return r

def d_mono(S, W, c1, c2, dom, guard):
    for i in range(2):
        for a in dom:
            if a == B: continue
            S.add_clause(guard + [-W(c1, i, a), W(c2, i, T)] + ([W(c2, i, a)] if a != T else []))
    for l in d.LAYERS:
        for l2 in d.LAYERS:
            if l2 < l: S.add_clause(guard + [-W(c1, 2, l), -W(c2, 2, l2)])

if __name__ == "__main__":
    n = int(sys.argv[1])
    for k, m in [tuple(map(int, a.split(','))) for a in sys.argv[2:]]:
        run(k, m, n)
