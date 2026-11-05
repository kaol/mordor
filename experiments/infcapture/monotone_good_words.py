"""F-monotone admissibility systems and compatible good words (log §34.3z¹⁰⁷, brief Stage 2, Work Package A).

Universe P* = {p0..}, U* = {u0..}. For every cell c = (A, B) (nonempty A ⊆ P*, B ⊆ U*) an abstract system records
  SP(c) = {p ∈ P* : z(c) ≤ p},   SU(c) = {u ∈ U* : u ≤ z(c)},       z(c) = F(⋀A, ⋁B),
subject to the facts every counterexample satisfies:
  order:  A' ⊆ A, B ⊆ B'  ⇒  z(A,B) ≤ z(A',B'), so SP(A',B') ⊆ SP(A,B) and SU(A,B) ⊆ SU(A',B')
          (these are the brief's two persistence laws for ΛP = A \\ SP, ΛU = B \\ SU);
  cross:  p ∈ SP(c), u ∈ SU(c) is impossible (u ≤ z ≤ p would put u in D);
  NW:     A ⊄ SP(c), B ⊄ SU(c) (no witness).
Selectors fP(c) ∈ ΛP(c), fU(c) ∈ ΛU(c) are GLOBAL. Good words as in `Sperner.lean`. A chain is a sequence of
good words for an exhaustion (A₁, B₁) ⊂ (A₂, B₂) ⊂ … adding one letter per stage, each the restriction of the next.
2QBF by CEGAR: outer = system, inner = (selectors, words); a found chain is blocked by requiring one of the
admissibility facts it used to fail."""
import itertools, sys, time
from z3 import *

def subsets(xs):
    return [frozenset(c) for r in range(1, len(xs) + 1) for c in itertools.combinations(xs, r)]

class Universe:
    def __init__(self, stages):
        self.stages = stages  # list of (A_n, B_n) tuples
        self.P = sorted(set().union(*[set(a) for a, _ in stages])); self.U = sorted(set().union(*[set(b) for _, b in stages]))
        self.cells = [(A, B) for A in subsets(self.P) for B in subsets(self.U)]

def system_constraints(un, s, sp, su):
    for (A, B) in un.cells:
        c = (A, B)
        s.add(Or([Not(sp[c, p]) for p in A])); s.add(Or([Not(su[c, u]) for u in B]))
        for p in un.P:
            for u in un.U: s.add(Not(And(sp[c, p], su[c, u])))
        for (A2, B2) in un.cells:
            c2 = (A2, B2)
            if c2 != c and A2 <= A and B <= B2:  # z(c) <= z(c2)
                for p in un.P: s.add(Implies(sp[c2, p], sp[c, p]))
                for u in un.U: s.add(Implies(su[c, u], su[c2, u]))

def inner(un, SPv, SUv, timeout=None):
    """Find global selectors and a compatible chain of good words; return (used facts) or None."""
    s = Solver()
    if timeout: s.set('timeout', timeout)
    fP, fU = {}, {}
    def selP(c):
        if c not in fP:
            v = Int(f"fP_{sorted(c[0])}_{sorted(c[1])}"); fP[c] = v
            adm = [p for p in c[0] if p not in SPv[c]]
            s.add(Or([v == un.P.index(p) for p in adm]))
        return fP[c]
    def selU(c):
        if c not in fU:
            v = Int(f"fU_{sorted(c[0])}_{sorted(c[1])}"); fU[c] = v
            adm = [u for u in c[1] if u not in SUv[c]]
            s.add(Or([v == un.U.index(u) for u in adm]))
        return fU[c]
    pos = []
    for n, (A, B) in enumerate(un.stages):
        letters = list(A) + list(B); m = len(letters)
        ps = {x: Int(f"pos{n}_{x}") for x in letters}; pos.append(ps)
        s.add([And(ps[x] >= 0, ps[x] < m) for x in letters]); s.add(Distinct(list(ps.values())))
        s.add(Or([ps[u] == 0 for u in B])); s.add(Or([ps[p] == m - 1 for p in A]))
        cand = [(A2, B2) for (A2, B2) in un.cells if A2 <= frozenset(A) and B2 <= frozenset(B)]
        labsP, labsU = [], []
        for t in range(1, m):
            matches = []
            for c in cand:
                cond = And([(ps[x] >= t) == (x in c[0]) for x in A] + [(ps[u] < t) == (u in c[1]) for u in B])
                matches.append((c, cond))
            if t <= len(A):
                lv = Int(f"lP{n}_{t}"); labsP.append(lv)
                s.add([Implies(cond, lv == selP(c)) for c, cond in matches])
            if t >= m - len(B):
                lv = Int(f"lU{n}_{t}"); labsU.append(lv)
                s.add([Implies(cond, lv == selU(c)) for c, cond in matches])
        s.add(Distinct(labsP)); s.add(Distinct(labsU))
        if n > 0:
            prev = pos[n - 1]
            for x, y in itertools.permutations(prev.keys(), 2):
                s.add((prev[x] < prev[y]) == (ps[x] < ps[y]))
    r = s.check()
    if r != sat: return None if r == unsat else 'unknown'
    mo = s.model()
    used = []
    for c, v in fP.items():
        val = mo.eval(v, model_completion=True).as_long(); used.append(('P', c, un.P[val]))
    for c, v in fU.items():
        val = mo.eval(v, model_completion=True).as_long(); used.append(('U', c, un.U[val]))
    words = []
    for n, ps in enumerate(pos):
        words.append(''.join(x for x, _ in sorted(ps.items(), key=lambda kv: mo.eval(kv[1]).as_long())))
    return used, words

def cegar(un, max_iter=2000, verbose=False):
    outer = Solver()
    sp = {(c, p): Bool(f"sp_{sorted(c[0])}_{sorted(c[1])}_{p}") for c in un.cells for p in un.P}
    su = {(c, u): Bool(f"su_{sorted(c[0])}_{sorted(c[1])}_{u}") for c in un.cells for u in un.U}
    system_constraints(un, outer, sp, su)
    for it in range(max_iter):
        if outer.check() != sat: return ('every system admits a compatible chain', it)
        mo = outer.model()
        SPv = {c: {p for p in un.P if is_true(mo.eval(sp[c, p], model_completion=True))} for c in un.cells}
        SUv = {c: {u for u in un.U if is_true(mo.eval(su[c, u], model_completion=True))} for c in un.cells}
        res = inner(un, SPv, SUv)
        if res is None: return ('COUNTEREXAMPLE system with no compatible chain', it, SPv, SUv)
        if res == 'unknown': return ('inner unknown', it)
        used, words = res
        outer.add(Or([sp[c, x] if k == 'P' else su[c, x] for k, c, x in used]))
        if verbose and it % 50 == 0: print('  iter', it, words, flush=True)
    return ('iteration limit', max_iter)

def chain(nP, nU, order='P-first'):
    P = [f"p{i}" for i in range(nP)]; U = [f"u{j}" for j in range(nU)]
    st = [((P[0],), (U[0],))]; a, b = 1, 1
    while a < nP or b < nU:
        if (order == 'P-first' and a < nP) or b >= nU: a += 1
        elif order == 'alternate' and a <= b and a < nP: a += 1
        else: b += 1
        st.append((tuple(P[:a]), tuple(U[:b])))
    return st

if __name__ == '__main__':
    for nP, nU, order in [(3, 1, 'P-first'), (4, 1, 'P-first'), (2, 2, 'alternate'), (3, 2, 'alternate'), (3, 2, 'P-first'),
                          (4, 2, 'alternate')]:
        un = Universe(chain(nP, nU, order)); t0 = time.time()
        out = cegar(un)
        head = out[0] if len(out) < 3 else out[0]
        print(f"|P*|={nP} |U*|={nU} exhaustion {order} {[(len(a), len(b)) for a, b in un.stages]}: {head} "
              f"(CEGAR iterations {out[1]}, {time.time()-t0:.0f}s)", flush=True)
        if len(out) > 2:
            SPv, SUv = out[2], out[3]
            for c in un.cells:
                if SPv[c] or SUv[c]: print('   ', sorted(c[0]), sorted(c[1]), 'SP', sorted(SPv[c]), 'SU', sorted(SUv[c]))

def all_exhaustions(nP, nU):
    P = [f"p{i}" for i in range(nP)]; U = [f"u{j}" for j in range(nU)]
    out = []
    for p in P:
        for u in U:
            rest = [x for x in P + U if x not in (p, u)]
            for order in itertools.permutations(rest):
                st = [((p,), (u,))]; A, B = [p], [u]
                for x in order:
                    (A if x in P else B).append(x); st.append((tuple(sorted(A)), tuple(sorted(B))))
                out.append(st)
    return out

def cegar_all(nP, nU, max_iter=5000):
    """A system for which NO exhaustion admits a compatible chain of good words."""
    exs = all_exhaustions(nP, nU); uns = [Universe(st) for st in exs]; un0 = uns[0]
    outer = Solver()
    sp = {(c, p): Bool(f"sp_{sorted(c[0])}_{sorted(c[1])}_{p}") for c in un0.cells for p in un0.P}
    su = {(c, u): Bool(f"su_{sorted(c[0])}_{sorted(c[1])}_{u}") for c in un0.cells for u in un0.U}
    system_constraints(un0, outer, sp, su)
    for it in range(max_iter):
        if outer.check() != sat: return ('for every system some exhaustion admits a compatible chain', it)
        mo = outer.model()
        SPv = {c: {p for p in un0.P if is_true(mo.eval(sp[c, p], model_completion=True))} for c in un0.cells}
        SUv = {c: {u for u in un0.U if is_true(mo.eval(su[c, u], model_completion=True))} for c in un0.cells}
        blocked = False
        for un in uns:
            res = inner(un, SPv, SUv)
            if res is not None and res != 'unknown':
                used, _ = res
                outer.add(Or([sp[c, x] if k == 'P' else su[c, x] for k, c, x in used])); blocked = True; break
        if not blocked: return ('COUNTEREXAMPLE: no exhaustion admits a compatible chain', it, SPv, SUv)
    return ('iteration limit', max_iter)
