# Work in progress: `OHAt 5` by cube-and-conquer (log §34.3z¹⁶¹)

The rigid orbit-height theory at H = 5 is split by the boundary orbits (first n with ⊤ ≤ u_n, first m with d_m ≤ ⊥).
Cases with n + m ≤ 7 and n, m ≥ 2 are search cases; all are refuted except inside (n, m) = (3, 3), which is split
3×3 on p = F(⊥, u₂) ∈ [d₂, v] and q = F(d₂, ⊤) ∈ [v, u₂]. Sub-cases (0,0), (0,1), (1,0), (1,1), (2,2) are refuted;
(0,2), (1,2), (2,0), (2,1) are being refuted by `oh_cube.py` (3-way splits, warm start).

* `seed/`: term sets (pickled expressions) of the hand-run refuted leaves (`oh_ground.py 5 … case=n,m [subcase=a,b]
  terms=…`, `oh_cube.py … sub=2,2`).
* `cache5/`: snapshot of the `oh_cube.py` cache (refuted leaves and split decisions; restart-safe).

Resume (each in parallel; memory ≲ 4 GB each):

    cd experiments/sat
    for sc in 0,2 1,2 2,0 2,1; do python3 oh_cube.py 5 150 /tmp/c33_$sc.pkl root=3,3 sub=$sc warm cache=oh5_work/cache5 & done; wait

When all four report `all cases refuted`:

    DRAT_TRIM=/path/to/drat-trim python3 oh_cert.py 5 oh5_work/cache5 /tmp/cert5 seed
    python3 oh_cert_lean.py /tmp/cert5 ../../lean/Mordor chunk=12
    # add the generated imports (OHCube5Terms, OHCube5L*, OHCube5) to lean/Mordor.lean, then `lake build`

Lean cost: H = 5 leaf cores are large (e.g. the root case (3, 2): 3012 clauses, 1931 after iterated core
extraction, which `oh_cert.py` now does). Elaborating such a leaf overflows the default stack; use
`ulimit -s unlimited` and `lake env lean --tstack=1000000 …` (for `lake build`, add `moreLeanArgs := #["--tstack=1000000"]`
to the Mordor lean_lib). With 3012 clauses, `bv_decide` did not finish within 28 min on a shared core here; expect
tens of minutes per large leaf on a dedicated core.

The result is `OrbitHeight.ohAt_5c : OHAt 5` (a `bv_decide` certificate: `Lean.ofReduceBool`, `Lean.trustCompiler`).
