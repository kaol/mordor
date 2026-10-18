"""Derivation amalgamation for R(F) (external suggestion, log §34.3k).

R_0 = ↓⊥, R_{k+1} = Φ(R_k) = ↓(R_k ∪ a(R_k) ∪ b⁻¹(R_k)); s(x) = least k with x ∈ R_k (∞ if x ∉ R(F)).
Join delay of F: max over x, y ∈ R(F) of s(x ∨ y) − max(s(x), s(y)). A uniform bound N would be the "binary
amalgamation lemma" R_i ∨ R_j ⊆ R_{max(i,j)+N}.  Also: per-stage join-closure of the R_k, and the same quantity
for arbitrary monotone pairs (a, b) not derived from any F, as a control.

  python3 amalgam.py"""
import sys, itertools, collections
import laws as Lw


def stages(L, a, b):
    R, le = range(L.n), L.le
    cur = {x for x in R if le[x][L.bot]}; s = {x: 0 for x in cur}; k = 0
    while True:
        gen = set(cur) | {a[x] for x in cur} | {y for y in R if b[y] in cur}
        nxt = {x for x in R if any(le[x][g] for g in gen)}
        k += 1
        if nxt == cur: return s
        for x in nxt - cur: s[x] = k
        cur = nxt


def delay(L, s):
    J = L.join; d = 0; per_stage_closed = True
    for x, y in itertools.combinations(s, 2):
        z = J[x][y]
        if z not in s: return None, False          # R not join-closed (a Cut counterexample)
        dd = s[z] - max(s[x], s[y]); d = max(d, dd)
        if dd > 0: per_stage_closed = False
    return d, per_stage_closed


def run(L, maps=False, limit=None):
    hist = collections.Counter(); closed = 0; tot = 0; full = 0
    if not maps:
        src = (( [L.gfp(lambda Y: F[(x, Y)]) for x in range(L.n)], [L.lfp(lambda X: F[(X, y)]) for y in range(L.n)])
               for F in Lw.monotone_F(L))
    else:
        mons = [t for t in itertools.product(range(L.n), repeat=L.n)
                if all(L.le[t[i]][t[j]] for i in range(L.n) for j in range(L.n) if L.le[i][j])]
        src = ((list(p), list(q)) for p in mons for q in mons)
    for a, b in src:
        tot += 1
        s = stages(L, a, b); d, pc = delay(L, s)
        full += (len(s) == L.n); hist[d] += 1; closed += pc
        if limit and tot >= limit: break
    print(f"{L.name} {'(arbitrary monotone a, b)' if maps else '(derived from F)'}: {tot} cases, R = L in {full}; "
          f"join delay histogram {dict(sorted(hist.items(), key=lambda kv: (kv[0] is None, kv[0] or 0)))}; "
          f"every R_k join-closed in {closed}", flush=True)


if __name__ == '__main__':
    for L in [Lw.chain(4), Lw.B2, Lw.chain(5), Lw.M3, Lw.N5]:
        run(L, limit=2_000_000 if L.name in ('M3', 'N5') else None)
        run(L, maps=True)
