# Lean 4 formalization

Machine-checked proofs of results from the research log, against Mathlib (`lakefile.toml` pins Lean 4.28.0 and
Mathlib `v4.28.0`). Mathlib is a lake dependency fetched into `.lake/` (gitignored); nothing large is committed.

```bash
cd lean
lake exe cache get     # prebuilt Mathlib (needs lakecache.blob.core.windows.net); otherwise
lake build             # builds the needed part of Mathlib from source, then Mordor
```

Every theorem compiles without `sorry`. `#print axioms` on the 35 headline theorems lists only `propext`,
`Quot.sound` and `Classical.choice` (docs/rounds/26-v3.7.md, §34).

| file | log | content |
|---|---|---|
| `Mordor/Derived.lean` | §13–§14, §24.1 | derived maps a, b, m, n; L1, L2, I1, fusion, L3, L4, the I2 characterization; the Realizability Criterion (no finiteness). Erratum: the log's L2 proof misuses Tarski (step 5) and its L1 proof skips a step; both are repaired here |
| `Mordor/Cut.lean` | §20.5, §30.3–§30.4 | Cut Lemma in cell form ⟺ map form, per F; Cut (on L itself, for that F) ⟹ semi-CL, without the polar-interval reduction; the Cut Lemma on finite chains; the Semi-Commutation Lemma and the Finite Commutation Lemma on finite chains |
| `Mordor/PrincipalCut.lean` | §30.4 | the Cut Lemma for principal cuts: ↑u under ACC, ↓d under DCC (finite lattices have both) |
| `Mordor/Reach.lean` | §31.1 | R(F) = L ⟺ Cut (per F); under ACC + DCC, Cut ⟺ R(F) join-closed ("the gap is joins") |
| `Mordor/Duality.lean` | §22.1 | the Duality Theorem: Fᵈ on αᵒᵈ, aᵈ = h∘b∘h⁻¹, mᵈ = h n; transfer of m = n and of commutation |
| `Mordor/Orbit.lean` | §32.6 | the lax square ⋁Θ⁺D ≤ κ⁺(⋁D), ⋁R_k ≤ r_k, and ⋁R_k = r_k on top-closed lattices |
| `Mordor/NoRoom.lean` | §16.2 | the Corner Lemma at (m, n); CL, and the Cut Lemma, on complete lattices whose middle elements are atom-and-coatom (M_κ for every κ) |
| `Mordor/Height3.lean` | §34.3f (new) | **the Cut Lemma, semi-CL and CL on every complete lattice of edge-height ≤ 3** (D_ω, M_ω × C₂ included) |
| `Mordor/GroundCut.lean` | §34.3g–h | clause lemmas of the ground cut theory (one per axiom family), `chainTo`, `NoChain`; order duality of cut counterexamples and `cut_of_wlog` (certificates may assume F(⊥,⊤) ∉ D) |
| `Mordor/CutHeight4.lean` | §34.3g | *generated* by `experiments/sat/cut_lean.py`: the Cut Lemma in bounded posets with no 6-chain, by `bv_decide` on a drat-trim-verified core (100 clauses, 17 terms, under WLOG) |
| `Mordor/Height4.lean` | §34.3g | **semi-CL and CL on every complete lattice of edge-height ≤ 4** (E_ω included); `cutCells_of_poset`. Trust: `bv_decide` (`Lean.ofReduceBool`) |
| `Mordor/CutHeight5.lean` | §34.3h | *generated*: the Cut Lemma in bounded posets with no 7-chain (832 clauses, 86 terms, under WLOG) |
| `Mordor/Height5.lean` | §34.3h | **semi-CL and CL on every complete lattice of edge-height ≤ 5**; locality: the same per F on any complete lattice when ⟨⊥, ⊤⟩_F has no 7-chain (`semi_local5`). Trust: `bv_decide` |
| `Mordor/Restrict.lean` | §15.1, §24.1, §30.5 | embedding lemma; polar reduction; interval violators transport to L; the Escape Lemma |
| `Mordor/Sharpness.lean` | §22.2–§22.5 | Ladder Lemma (records of a well-order), ladder and co-ladder constructions, Infinitude Lemma, **Sharpness**: a complete chain satisfies CL iff it is finite |
| `Mordor/Retract.lean` | §23.1 | the Retract Theorem for any retraction pair ι, σ (σ∘ι = id) between complete lattices |
| `Mordor/TheoremA.lean` | §23.2 | **Theorem A**: a complete lattice containing an infinite chain fails CL; CL lattices are chain-finite |
| `Mordor/Continuous.lean` | §34.3i | an M0-continuous CL violator on ω + 1: F(x, y) = min(x + 1, y ∸ 1) preserves ω-sups and ω-infs, commutes, m = 0 ≠ ω = n |
| `Mordor/Axioms/Thin.lean` | foundations §11 | every axiom, bound and rule with a thin reading, derived in an arbitrary complete lattice (μ1–μ5, ν1–ν5, B1, D1–D6, Bd1–Bd9, I1, I2, I10), with Bd8 and I2-as-a-rule refuted |
| `Mordor/Axioms/Cat.lean` | foundations §11 | the categorical layer over Mathlib's `Endofunctor.Algebra`/`Coalgebra`: Lambek and its inverse as the fold of F(in) (`unmade_where_made`), fold/ana, induction, coinduction; B1 refuted in `Type`; the category of dialgebras with D1 (transposition along L ⊣ G as an equivalence), D3, D5, D6, Bd9 |
| `Mordor/Axioms/Source.lean` | `docs/02-the-source.md` | sharpened rows: the one-functor distributive law closure ∘ interior ⇒ interior ∘ closure (bialgebras = fixed points); the derived law b∘a ⇒ a∘b, I11 guarded by the Cut Lemma and false unguarded; the One Ring (initial = final bi-fixed point ⟺ m = n); I3 |
| `Mordor/Axioms/Law.lean` | foundations B2, B3, I6, I7 | Turi–Plotkin for a plain distributive law S∘B ⇒ B∘S in any category: λ-bialgebras, the initial algebra and final coalgebra lifted to bialgebras, the comparison as fold = ana (I6) and as an algebra map (congruence, I7) |
| `Mordor/Local.lean` | §34.3j | locality of semi-CL: if semi-CL holds on [m, n], then m = n iff semi-commutation holds on [m, n]; discharged at edge-height ≤ 5 (`semi_interval5`) |
| `Mordor/Frontier.lean` | §34.4a | `frontier`: CL ⟹ chain-finite; chain-finite ∧ (∀ F, R(F) join-closed) ⟹ CL. The conjecture reduced to one statement |
| `Mordor/Dialgebra.lean` | §32.2–§32.4 | transposition (D1/D2 via adjoints), the failure-zone theorem and its dual, D5 by order reversal; `bd8_fails`: the cross bound Bd8 is false in the thin model (foundations v3.7) |
| `Mordor/CutDuality.lean` | §33.3 | Φ ⊣ c∘Ψ∘c and the k + j law, for any preorder and arbitrary maps a, b |
| `Mordor/Sperner.lean`, `Mordor/FinGenAll.lean` | §34.3n | the product Sperner lemma (`odd_goods`); `captured`, `cut_fingen` (finitely generated cut and complement), `cut_finite`, `cl_finite`: **Cut and CL on every finite lattice** |
| `Mordor/FGTwo.lean` | §34.3z¹⁴, ¹⁶ | `orbit_end`, the sandwich, `cut_two` (two-generated cuts under DCC), `cut_bouquet` |
| `Mordor/AsyncMeetGrid.lean` | §34.3z¹⁰⁵ | the asynchronous meet grid; **`cut_fingen_dcc`: the Cut Lemma for every finitely generated cut of a DCC lattice** (via `cut_finite` on the grid lattice); `cut_three`, `cut_two_of_grid` |
| `Mordor/InfiniteCapture.lean` | §34.3z¹⁰⁶, ¹¹⁶ | extremal boundary facts; `cut_of_grid_capture` (one-sided capture suffices) and `cut_of_grid_capture_upto` (no chain condition, given entry times); `uncaptured_column_exists`, `uncaptured_column_upto`; `cut_cofingen_acc` (dual); `cut_chainfinite_of_finite_side` |
| `Mordor/BoundedSupportPivot.lean`, `Mordor/AxisCapture.lean` | §34.3z¹¹⁷ | minimal supports give strict partial-meet chains (\|S\| + 1 ≤ H, tᵢ + \|S\| ≤ H); the axis-capture graph, `axis_or_mixed`, `mixed_minimal_support`, `new_maximum` |
| `Mordor/CrossCell.lean` | §34.3z¹¹⁸ | the cross-envelope lemma, its row-side dual, boundary extension of cross outputs, the two-point form at the blind coordinate |
| `Mordor/FiniteQuotient.lean` | §34.3z¹¹⁹ | `faithful_image_impossible`, `finite_cut_faithful_quotient_impossible`; half-filtration `separating_family_witness` (and dual); the ω + 1 obstruction |
| `Mordor/ExtremalSeparators.lean`, `Mordor/SeparatorStages.lean` | §34.3z¹²⁰–¹²¹ | maximal/minimal separators (⊓-/⊔-irreducible), the aggregation criterion; the separator process (`Step`, `Run`), persistence, strict growth, the causal chain, `cut_of_terminal_run`, `exists_run` |
| `Mordor/SeparatorRank.lean`, `Mordor/SeparatorAncestry.lean` | §34.3z¹²²–¹²³ | closure-rank drop, `rank_parent_stage_bound`, the causal fork, `contained_branch_height6` (via `cut_height5`; `bv_decide` trust); separator tokens, fresh tokens, minimal meet/join supports ≤ H, fan collapse, `potential_parent_stage_bound` |
| `Mordor/IntervalRefinement.lean` | §34.3z¹²⁴ | the crossing-interval order and its well-foundedness (`intervalLT_wellFounded`, Dershowitz–Manna refinement), anchor envelopes |
| `Mordor/InterfaceTrace.lean` | §34.3z¹²⁵–¹²⁶ | low/high traces, `patch_mono`, `patch_no_witness`, external/internal/general pins, `atom_family_block` |
| `Mordor/GapPotential.lean`, `Mordor/GapMax.lean` | §34.3z¹²⁵–¹²⁷ | `height` (edge-height rank), `cut_of_gap_parent`; `parent_iff_max_drop`, `cut_of_max_gap_drop`, `nested_child_gap` |
| `Mordor/ShortestRun.lean` | §34.3z¹³⁰ | `Goal`, the reachable state graph, `dist`, `optimal_successor`, `maxSep_restrict` |
| `Mordor/ResponseRun.lean` | §34.3z¹³¹ | the response run, sub-lattice transfer (`resp_transfer`), `cut_of_resp_bound` |
| `Mordor/GeneralRun.lean` | §34.3z¹³⁶ | `Closed` stage sequences; `cut_of_gap_parent_closed`, `cut_of_max_gap_drop_closed`; general-separator runs `GStep`/`GRun`, `run_grun`, `cut_of_terminal_grun`, `cut_of_max_gap_drop_general` |
| `Mordor/OrbitHeight.lean` | §34.3z¹⁴⁰ | `escape`, `orbitHeight_one`, `risingEscape_zero`; `TightUPC ⇒ RisingEscape ⇒ TightStep ⇒ OrbitHeightInv ⇒ ⊤ ∈ R_H`, `cutMaps_of_tightUPC`; `join_mem_of_top_mem`; §34.3z¹⁴¹: `upc_of_le_diag` (diagonal upper principal cut), `le_diag_of_a`, `TightIC`, `DiagTop ⇒ TightIC ⇒ Cut`, `tightIC_one_of_a_bot` |
| `Mordor/InterfaceExtraction.lean` | §34.3z¹⁴⁰ | `cycle_lower_witness`, `cycle_impossible`: separator cycles force a lower witness (via `atom_family_block`) |
| `Mordor/BottomMaxCell.lean` | §34.3z¹⁴² | `R_no_cross_cell` (no cell across R), `common_column`, `cut_of_atomic` (atomic cuts are bouquets), `cutMaps_of_R_atomic`, `cutMaps_of_R_height_le_one`, `near_cell_of_atomic_over`, `dual_near_cell` |

The table lists the headline files; the other files under `Mordor/` (about 120 in all) are documented in their module
docstrings and in the log section each one cites.
