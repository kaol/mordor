"""Round 22 cross-check: calibration against the log's ground truth, then a direct SAT decision of CL.
Run:  python3 crosscheck.py            (DRAT certification if $DRAT_TRIM points to a drat-trim binary)"""
import os, subprocess, time
from fractions import Fraction
from lat import *

def macmahon(a, b, c):
    r = Fraction(1)
    for i in range(1, a+1):
        for j in range(1, b+1):
            for k in range(1, c+1): r *= Fraction(i+j+k-1, i+j+k-2)
    return int(r)

def all_monotone_chain(n):
    F = [[0]*n for _ in range(n)]
    def rec(k):
        if k == n*n: yield [r[:] for r in F]; return
        x, y = divmod(k, n); lo = max(F[x-1][y] if x else 0, F[x][y-1] if y else 0)
        for v in range(lo, n): F[x][y] = v; yield from rec(k+1)
    yield from rec(0)

print("1. Calibration")
print("   MacMahon n x n x (n-1), n=3..6:", [macmahon(n, n, n-1) for n in (3, 4, 5, 6)])
for n in (3, 4):
    L = chain(n); pairs = set(); cnt = comm = mne = pol = viol = 0
    for F in all_monotone_chain(n):
        a, b, m, nn, c = semantic(L, F); cnt += 1; pairs.add((tuple(a), tuple(b)))
        comm += c; mne += m != nn; viol += c and m != nn; pol += (a[0] == b[0] == 0 and a[-1] == b[-1] == n-1)
    print(f"   chain-{n}: bifunctions {cnt}, derived pairs {len(pairs)}, commuting {comm}, m!=n {mne}, polar {pol}, CL violators {viol}")
    if n == 4:
        e = Enc(L, polar=False, commute=False); s = e.solver(); got = set()
        while s.solve():
            F, a, b = e.decode(s.get_model()); got.add((tuple(a), tuple(b)))
            assert derived(L, F) == (a, b) and monotone(L, F)
            s.add_clause([-e.A[x][a[x]] for x in range(n)] + [-e.B[x][b[x]] for x in range(n)])
        print(f"   chain-4: SAT-enumerated realizable pairs {len(got)}; set-equal to ground truth: {got == pairs}")
L = E(2); n = L.n; sigma = [0, 1, 5, 6, 7, 2, 3, 4]
def fix(a, b):
    def f(e):
        for x in range(n): e.cl += [[e.A[x][a[x]]], [e.B[x][b[x]]]]
    return f
print("   control twisted meet (sigma, const-0) realizable:", Enc(L, False, False, fix(sigma, [0]*n)).solver().solve())
print("   control sigma-diagonal (sigma, sigma) realizable:", Enc(L, False, False, fix(sigma, sigma)).solver().solve())

print("2. CL by direct SAT (every interval checked)")
Ls = [chain(k) for k in range(3, 11)] + [M(3), M(4), M(5), N5(), powerset(2), powerset(3), powerset(4),
      E(2), E(3), E(4), E(5), D_cols(4), product(chain(2), chain(3)), product(chain(3), chain(3)),
      product(chain(3), chain(4)), product(chain(4), chain(4)), product(powerset(2), chain(3)),
      product(N5(), chain(2)), product(M(3), chain(2)), product(M(3), M(3))]
for L in Ls:
    t = time.time(); ok, w = CL_holds(L)
    print(f"   {L.name:9s} n={L.n:3d}  CL {'holds' if ok else 'FAILS at ' + str(w)}  ({time.time()-t:.1f}s)", flush=True)
cnt = 0
for L in moore_family(4):
    if L.n >= 3: assert polar_violator(L) is None; cnt += 1
print(f"   all lattices with <=4 join-irreducibles: {cnt} (n>=3), polar violators 0  => CL on all (family closed under intervals)")

DT = os.environ.get("DRAT_TRIM")
if DT:
    print("3. DRAT certificates (polar instance on the whole lattice)")
    for L in [chain(10), M(5), N5(), powerset(3), E(2), E(3), E(4), E(5), powerset(4), product(chain(4), chain(4))]:
        e = Enc(L, polar=True, commute=True); s = Cadical153(bootstrap_with=e.cl, with_proof=True)
        assert s.solve() is False
        with open("/tmp/inst.cnf", "w") as f:
            f.write(f"p cnf {e.nv} {len(e.cl)}\n"); f.writelines(" ".join(map(str, c)) + " 0\n" for c in e.cl)
        with open("/tmp/inst.drat", "w") as f: f.writelines(l + "\n" for l in s.get_proof())
        out = subprocess.run([DT, "/tmp/inst.cnf", "/tmp/inst.drat", "-t", "2000"], capture_output=True, text=True).stdout
        print(f"   {L.name:8s} vars {e.nv:6d} clauses {len(e.cl):7d}  drat-trim: {[l for l in out.splitlines() if l.startswith('s ')]}", flush=True)
