"""Round 22: is commutation tight?  One-sided hypotheses b.a <= a.b and a.b <= b.a (pointwise)."""
from lat import *
for L in [chain(3), chain(4), chain(5), M(3), N5(), powerset(3), E(2), E(3)]:
    print(f"{L.name:4s}", {r: CL_holds(L, r)[0] for r in ("ba<=ab", "ab<=ba")})
cnt = 0
for L in moore_family(4):
    if L.n >= 3: assert polar_violator(L, "ba<=ab") is None; cnt += 1
print(f"b.a <= a.b  =>  m = n : all {cnt} lattices with <=4 join-irreducibles; chains C6..C9:",
      [CL_holds(chain(k), "ba<=ab")[0] for k in range(6, 10)])
