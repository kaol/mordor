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
- §34.3z¹⁵⁷: `feeder.py` (hypothesis analysis of feeder identity: index-free, any base), `lemma_d.py`, `good_b.py`, `rise_sat.py [ctl] [local|both] …` (exact Rise conjecture: no counterexample); random `fixed_entry.py`, `feeder_mine.py`, `lemma_t_mine.py`, `lag_mine.py`, `g1_mine.py`, `g1star.py`, `rigid.py`. Output `out_rise.txt`.
- §34.3z¹⁵⁸: `rise_sat.py kc|kclast|shallow=J [hmax=h] (… | h3 K M SEED COUNT)` (column-⊤ Kleene chain goodness: false at height 4, true at height ≤ 3; shallow Rise witnesses need depth H − 1), `kleene_top.py`, `rise_witness.py`, `h3_case.py`. Output `out_rise_base.txt`.
- §34.3z¹⁵⁹: `grid_rise.py (grid0|grid|grid+|beta|ideal|betaonly|idealonly) …` (BoundaryGridRise: refuted for every family, smallest |L| = 6). Output `out_grid_rise.txt`.
- §34.3z¹⁶²: `single_claims.py noic_fi [ahead] …` (feeder identity without an interval cell: none index-tight, |L| = 7 one stage ahead). Output `out_singleton_history.txt`.
- §34.3z¹⁶³: `single_claims.py feeder_post …` (lower feeders are not always diagonal post-fixed, |L| = 5); flags `notop` / `multi` drop ⊤ ∉ R_{K+1} / uniqueness of m (`noic_fi multi`: |L| = 5); `crossing_probe.py sweep P NMAX` (c_n, q_n = b(c_n), d*, the entry route of w on the ahead models); `check_min7.py` (regression check of the 7-element model against the new lemmas' hypotheses). Output `out_crossing.txt`.
- §34.3z¹⁶⁴: `single_claims.py (side_w | side | below_w) multi …` (uniqueness-free side entry: false at |L| = 5, 7, 8); `witness_probe.py (ahead | multi) …` (A-route witness and second-element provenance); `check_side.py` (re-verifies the counterexamples' hypotheses); `show_model.py FILE` (prints a model). Output `out_side_entry.txt`.
- §34.3z¹⁶⁵: `single_claims.py (soleB | soleA | sibling | topparent) multi [post | strictpre | nopostlayer] …`; `witness_probe.py layer …` (route and parent provenance in the case left by `SecondEntry.lean`); `top_parent.py` (configuration-free TopParent: false at |L| = 15); `check_second.py` (replays the post-fixed descent on the stored models). Output `out_second_entry.txt`.
- §34.3z¹⁶⁶: `single_claims.py … rmin=3` and `witness_probe.py layer rmin=3 …` (only m of rank ≥ 3, where TopParent differs from SecondEntry); `top_parent.py` now classifies the low parents (route, rank, stage, own entry, comparability, A-lifting). Output `out_parent_ancestry.txt`.
- §34.3z¹⁶⁷: `single_claims.py alltops multi nopostlayer rmin=3 …` (StrongTopParent: false at |L| = 13); `late_probe.py (config [rmin=R] … | file FILE …)` (per-parent provenance of second tops: edge, own entry, B-source, A-lift, A-normal form, domination by T_k, B-up-closure); `find_late.py`. Output `out_late_parent.txt`.
- §34.3z¹⁶⁸: `single_claims.py (bdom | mech) multi nopostlayer rmin=3 …` (late B-parent domination: false at |L| = 14; CanonicalTopParent: no counterexample); `late_probe.py` adds the mechanism split, the compensation cases and the terminal roots. Output `out_bparent.txt`.
- §34.3z¹⁶⁹: `corner_probe.py [rmin=R] …` (cross-corner terms s, a(m′), b(w), d*; the feeder-row descent and its drop case; mechanism witnesses); `single_claims.py dwit multi nopostlayer …` (DescentWitness: no counterexample). Output `out_canonical.txt`.
- §34.3z¹⁷⁰: `drop_probe.py [rmin=R] [show] …` (feeder-row drops: first drop q, output r, all alternative descent witnesses and their relations); `single_claims.py dropbelow multi nopostlayer …` (a top below every drop output: false at |L| = 14). Output `out_drop.txt`.
- §34.3z¹⁷¹: `single_claims.py (fxq | ontime | latejoin | abovea) multi nopostlayer rmin=3 …` (immediate-drop transfer candidates: all false at |L| = 13–14); `drop_probe.py` adds the raw feeder orbit and r classes; `check_drop171.py FILE …` (counterexample inspection). Output `out_drop171.txt`.
- §34.3z¹⁷²: `single_claims.py upcell multi [nopostlayer] rmin=R …` (UpCell: no counterexample at rank 3 and rank 4). Output `out_upcell.txt`.
- §34.3z¹⁷³: `ancestry_probe.py [rmin=R] …` (entry routes and sources of the top rows, UpCell witnesses, drop models); `single_claims.py (bcup | sibup) multi nopostlayer rmin=R …` (BComparableUpCell: no counterexample; common-source version false at |L| = 11). Output `out_ancestry.txt`.
- §34.3z¹⁷⁴: `shadow_probe.py [rmin=R] [save] …` (cross-evaluation shadows c = F(b(x), u) and source meets; claims (1)–(5) refuted, models `shadow_claim*_min*.json`); `single_claims.py bcupnew …` (CoverUpCell: no counterexample). Output `out_shadow.txt`.
- §34.3z¹⁷⁵: `shadow_probe.py` adds the top-shadow trichotomy, sibling families, the sibling join and the A2 branch data. Output `out_shadow175.txt`.
- §34.3z¹⁷⁶: `shadow_probe.py` adds the sibling-pair analysis (F(c, u) vs u, clamped descent, total incomparability; model `sibling_totinc_min25.json`). Output `out_sibling.txt`.
- §34.3z¹⁷⁷: `shadow_probe.py` adds the totally incomparable case (upward closure v* = u ⊔ F(c, u), the column t = F(c, u)). Output `out_sibling177.txt`.
- §34.3z¹⁷⁸: `single_claims.py famup multi nopostlayer rmin=3 …` (FamilyUpCell: false at |L| = 13; the witness is the feeder, with a different source). Output `out_famup.txt`.
- §34.3z¹⁷⁹: `chain_probe.py [rmin=R] …` (replays `dropChain_exit` from every feeder drop: exit depth and type, and witness relations; the column-localization failure is `chain_rescue_fail_min19.json`). Output `out_chain.txt`.
- §34.3z¹⁸⁰: `descent2d_probe.py [rmin=R] …` (replays `cellState_cell` from the feeder state (m′, w): path, final depth and orientation, column status, lift data). Output `out_descent2d.txt`.
- §34.3z¹⁸¹: `descent2d_probe.py` adds the depth-one origin (shadow vs feeder path) and the depth-two climb (witness y with b(y) = z as a z-shadow). Output `out_descent2d_lift.txt`.
- §34.3z¹⁸²: `descent2d_probe.py` adds the climb simulation (`climb_step` / `climb_next_config`, greedy and exhaustive). Output `out_climb.txt`.
- §34.3z¹⁸³: `descent2d_probe.py` adds the full-fibre climb (`climbF`), the liberal graph search and the fibre join; `fibre_probe.py [rmin=R] [save] …` (FibreTop / FibreStep over all sibling-shadow configurations; models `fibre_{top,step}_fail_min*.json`); `single_claims.py topfibre multi nopostlayer …` (TopFibre: no counterexample). Output `out_fibre.txt`.
