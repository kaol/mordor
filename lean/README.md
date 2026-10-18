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
| `Mordor/Frontier.lean` | §34.4a | `frontier`: CL ⟹ chain-finite; chain-finite ∧ (∀ F, R(F) join-closed) ⟹ CL. The conjecture reduced to one statement |
| `Mordor/Dialgebra.lean` | §32.2–§32.4 | transposition (D1/D2 via adjoints), the failure-zone theorem and its dual, D5 by order reversal; `bd8_fails`: the cross bound Bd8 is false in the thin model (foundations v3.7) |
| `Mordor/CutDuality.lean` | §33.3 | Φ ⊣ c∘Ψ∘c and the k + j law, for any preorder and arbitrary maps a, b |
