"""Can helper letters rescue a captor extension? (log §34.3z¹⁰⁸)

The infinite argument of work package A must extend the CURRENT chain by a designated captor letter r, possibly after
inserting other ("helper") letters first. Universe P* = {p0, p1, p2}, U* = {u0, u1}. Fixed chain prefix
({p0},{u0}) → ({p0,p1},{u0}) (the start of the minimal counterexample); target: a compatible chain from that prefix
to any stage containing the captor u1, with the helper p2 allowed before u1.
2QBF by CEGAR (outer: monotone system; inner: selectors, words, and the choice of continuation)."""
import itertools, time
from z3 import *
from monotone_good_words import Universe, inner, system_constraints

def continuations(prefix, P, U, captor):
    """Stage sequences extending `prefix` by single letters, ending at the first stage containing `captor`."""
    out = []
    A0, B0 = prefix[-1]; rest = [x for x in P + U if x not in A0 + B0 and x != captor]
    for k in range(len(rest) + 1):
        for helpers in itertools.permutations(rest, k):
            st = list(prefix); A, B = list(A0), list(B0)
            for x in list(helpers) + [captor]:
                (A if x in P else B).append(x); st.append((tuple(sorted(A)), tuple(sorted(B))))
            out.append(st)
    return out

def run(P, U, prefix, captor, max_iter=5000, captures=()):
    conts = continuations(prefix, P, U, captor); uns = [Universe(st) for st in conts]
    full = Universe([((P[0],), (U[0],)), (tuple(P), tuple(U))]); outer = Solver()
    sp = {(c, p): Bool(f"sp_{sorted(c[0])}_{sorted(c[1])}_{p}") for c in full.cells for p in full.P}
    su = {(c, u): Bool(f"su_{sorted(c[0])}_{sorted(c[1])}_{u}") for c in full.cells for u in full.U}
    system_constraints(full, outer, sp, su)
    for (A, B) in captures:  # the captor u lies below z at these cells (the possible pivots of the prefix's last word)
        outer.add(su[(frozenset(A), frozenset(B)), captor])
    for it in range(max_iter):
        if outer.check() != sat: return f"helpers always rescue ({len(conts)} continuations, {it} iterations)", None
        mo = outer.model()
        SPv = {c: {p for p in full.P if is_true(mo.eval(sp[c, p], model_completion=True))} for c in full.cells}
        SUv = {c: {u for u in full.U if is_true(mo.eval(su[c, u], model_completion=True))} for c in full.cells}
        done = False
        for un in uns:
            res = inner(un, {c: SPv[c] for c in un.cells}, {c: SUv[c] for c in un.cells})
            if res not in (None, 'unknown'):
                used, _ = res; outer.add(Or([sp[c, x] if k == 'P' else su[c, x] for k, c, x in used])); done = True; break
        if not done: return f"COUNTEREXAMPLE: no continuation reaches the captor ({it} iterations)", (SPv, SUv)
    return "iteration limit", None

if __name__ == '__main__':
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == 'captor':
        # u1 must capture every possible pivot of the stage-2 word: ({p0},{u0}) for u0p1p0, ({p1},{u0}) for u0p0p1
        caps = [(('p0',), ('u0',)), (('p1',), ('u0',))]
        for P, U in [(['p0', 'p1'], ['u0', 'u1']), (['p0', 'p1', 'p2'], ['u0', 'u1']), (['p0', 'p1'], ['u0', 'u1', 'u2']),
                     (['p0', 'p1', 'p2'], ['u0', 'u1', 'u2'])]:
            t0 = time.time(); msg, cx = run(P, U, [(('p0',), ('u0',)), (('p0', 'p1'), ('u0',))], 'u1', captures=caps)
            print(f"[captor of the pivot] universe {P}+{U}: {msg} ({time.time()-t0:.0f}s)", flush=True)
            if cx and len(P) + len(U) == 4:
                for c in sorted(cx[0], key=lambda c: (len(c[0]), len(c[1]), sorted(c[0]), sorted(c[1]))):
                    if cx[0][c] or cx[1][c]: print('    ', sorted(c[0]), sorted(c[1]), 'SP', sorted(cx[0][c]), 'SU', sorted(cx[1][c]))
        sys.exit()
    for P, U, prefix, captor in [(['p0', 'p1'], ['u0', 'u1'], [(('p0',), ('u0',)), (('p0', 'p1'), ('u0',))], 'u1'),
                                 (['p0', 'p1', 'p2'], ['u0', 'u1'], [(('p0',), ('u0',)), (('p0', 'p1'), ('u0',))], 'u1'),
                                 (['p0', 'p1'], ['u0', 'u1', 'u2'], [(('p0',), ('u0',)), (('p0', 'p1'), ('u0',))], 'u1')]:
        t0 = time.time(); msg, cx = run(P, U, prefix, captor)
        print(f"universe {P}+{U}, prefix {[(''.join(a), ''.join(b)) for a, b in prefix]}, captor {captor}: {msg} ({time.time()-t0:.0f}s)", flush=True)
        if cx:
            for c in sorted(cx[0], key=lambda c: (len(c[0]), len(c[1]), sorted(c[0]), sorted(c[1]))):
                if cx[0][c] or cx[1][c]: print('    ', sorted(c[0]), sorted(c[1]), 'SP', sorted(cx[0][c]), 'SU', sorted(cx[1][c]))
