# R-orbit stages: amalgamation and the orbit length (round 26, §34.3z¹⁴⁰)

Programme C of the brief "Breaking the Commutation Lemma frontier". For a monotone F on a finite lattice,
a(x) = gfp_y F(x, y), b(y) = lfp_x F(x, y), R_0 = ↓⊥, R_{k+1} = ↓(R_k ∪ a(R_k) ∪ b⁻¹(R_k)) (Lean `Orbit.Rk`).

- `rstages.py`: reference simulator (stages, the ideal orbit `ideal_orbit`, hill-climbing of join excess).
- `amalg_sat.py`: exact SAT encoding of F, a (gfp), b (lfp) and the stages; slow joins x, y ∈ R_m, x ∨ y ∉ R_{m+e}.
- `orbit_sat.py`: exact maximum stage of ⊤ over all F (ORB: R_H = L at edge-height H).
- `reach_height_sat.py`: exact check of the orbit-height invariant (OH): ⊤ ∉ R_k ⇒ R_k has an element of height ≥ k.
- `orbit_mech.py`, `ideal_compare.py`, `height_step.py`, `rising_routes.py`, `upc.py`: candidate mechanisms on random
  instances (minimal elements, chain length, coheight, rising height, tightness against the ideal orbit, rising
  escape, entry routes, upper principal cuts). Smallest violations `*_viol_s*.json`.
- `rising_sat.py [--upc]`: exact check of rising escape (P1′) and of the tight-stage upper principal cut.

- §34.3z¹⁴¹: `diag_upc.py` (diagonal top elements at tight stages), `nondiag.py` (cell types at non-diagonal tight
  stages), `rising_sat.py --upc --xeqm` (exact tight-stage interval cell), `rising_sat.py --nodiag` (exact residue
  search), `residue.py`, `residue_select.py` (anatomy of the residue and selection rules). Output `out_orbit2.txt`.

Output `out_orbit.txt` (§34.3z¹⁴⁰), `out_orbit2.txt` (§34.3z¹⁴¹). Lean: `lean/Mordor/OrbitHeight.lean`.

- §34.3z¹⁵²: `tight_probe.py (aentry [noic] | fibre [bonly] [minfibre]) …`: exact tight-stage entry routes and the maximal/minimal b-fibre conjectures (both refuted). Output `out_tight_entry.txt`.
- §34.3z¹⁵³: `tight_probe.py gfp [single] [noic] [some] …`: exact Tight-GFP (some top has y* = m or F(m, y*) = y*; no counterexample found); `single_top.py SEED SECONDS`, `gfp_top.py SEED SECONDS`: random single-top and column-orbit statistics. Output `out_gfp.txt`.
- §34.3z¹⁵⁴: `tight_probe.py old [single] [some] …` (New-top: some tight-stage top is new; no counterexample) and `tight_probe.py transfer [noic] [some] …` (consecutive tight stages: some cell target has a cell; no counterexample); `ic_entry.py`, `gfp_fail.py`, `layer_transfer.py SEED SECONDS`: random entry-stage, GFP-failure and transfer statistics. Output `out_transfer.txt`.
- §34.3z¹⁵⁵: `single_local.py [orbit] [lower] [depth=d] [tighthist] [multi] [nonoic] …` (singleton TightIC with the orbit stage replaced by an abstract history of depth d: SAT for d ≤ 2, UNSAT for the true orbit); `tight_probe.py offset [single]` (offset-1 TightIC: false, |L| = 5) and `aentry single [aonly]` (a singleton non-diagonal a-entered top is always also b-entered on the lattices checked). Output `out_lower_transfer.txt`.
- §34.3z¹⁵⁶: `single_claims.py CLAIM [ahead] …` (exact tests of intermediate lemmas for singleton lower transfer, singleton a-entry and multi-target transfer; `ahead` shifts the top one stage early), `single_local.py … rank=R`, `single_lower_mine.py`, `entry_height.py`. Output `out_single_claims.txt`.
