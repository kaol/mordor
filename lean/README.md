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
| `Mordor/Derived.lean` | §13–§14 | derived maps a, b, m, n; L1, L2, I1, fusion, L3, L4, the I2 characterization. Erratum: the log's L2 proof misuses Tarski (step 5) and its L1 proof skips a step; both are repaired here |
| `Mordor/Cut.lean` | §20.5, §30.3–§30.4 | Cut Lemma in cell form ⟺ map form, per F; Cut (on L itself, for that F) ⟹ semi-CL, without the polar-interval reduction; the Cut Lemma on finite chains; the Semi-Commutation Lemma and the Finite Commutation Lemma on finite chains |
| `Mordor/PrincipalCut.lean` | §30.4 | the Cut Lemma for principal cuts: ↑u under ACC, ↓d under DCC (finite lattices have both) |
| `Mordor/Reach.lean` | §31.1 | R(F) = L ⟺ Cut (per F); under ACC + DCC, Cut ⟺ R(F) join-closed ("the gap is joins") |
| `Mordor/Duality.lean` | §22.1 | the Duality Theorem: Fᵈ on αᵒᵈ, aᵈ = h∘b∘h⁻¹, mᵈ = h n; transfer of m = n and of commutation |
| `Mordor/Orbit.lean` | §32.6 | the lax square ⋁Θ⁺D ≤ κ⁺(⋁D), ⋁R_k ≤ r_k, and ⋁R_k = r_k on top-closed lattices |
| `Mordor/NoRoom.lean` | §16.2 | the Corner Lemma at (m, n); CL on complete lattices whose middle elements are atom-and-coatom (M_κ for every κ) |
| `Mordor/Sharpness.lean` | §22.2–§22.5 | Ladder Lemma (records of a well-order), ladder and co-ladder constructions, Infinitude Lemma, **Sharpness**: a complete chain satisfies CL iff it is finite |
| `Mordor/Retract.lean` | §23.1 | the Retract Theorem for any retraction pair ι, σ (σ∘ι = id) between complete lattices |
| `Mordor/TheoremA.lean` | §23.2 | **Theorem A**: a complete lattice containing an infinite chain fails CL; CL lattices are chain-finite |
| `Mordor/Frontier.lean` | §34.4a | `frontier`: CL ⟹ chain-finite; chain-finite ∧ (∀ F, R(F) join-closed) ⟹ CL. The conjecture reduced to one statement |
| `Mordor/Dialgebra.lean` | §32.2–§32.4 | transposition (D1/D2 via adjoints), the failure-zone theorem and its dual, D5 by order reversal |
| `Mordor/CutDuality.lean` | §33.3 | Φ ⊣ c∘Ψ∘c and the k + j law, for any preorder and arbitrary maps a, b |
