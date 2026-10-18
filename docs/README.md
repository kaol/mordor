# Mordor — Research Log Index

One file per exploration round. Version tags are the framework versions in which each round landed.

## Foundations

- [`00-foundations.md`](00-foundations.md) — the formal system: ambient setting, bialgebraic axioms, dialgebraic axioms, bounds, interaction rules, consistency metatheorems, status tags; mixed fixed points (§6) and the Cut Lemma interface (§7). Version 3.7.
- [`01-early-notes.md`](01-early-notes.md) — revision notes (v1.1) and the first exploration findings (v1.2).

## Exploration rounds

| Round | Version | File | One-line summary |
|---|---|---|---|
| 2 | v1.3 | [`rounds/02-v1.3.md`](rounds/02-v1.3.md) | First exploration round: open questions sharpened |
| 3 | v1.4 | [`rounds/03-v1.4.md`](rounds/03-v1.4.md) | Computational & literature results |
| 4 | v1.5 | [`rounds/04-v1.5.md`](rounds/04-v1.5.md) | The census results |
| 5 | v1.6 | [`rounds/05-v1.6.md`](rounds/05-v1.6.md) | Proofs and validation |
| 6 | v1.7 | [`rounds/06-v1.7.md`](rounds/06-v1.7.md) | L3/L4 proven — the characterization theorem |
| 7 | v1.8 | [`rounds/07-v1.8.md`](rounds/07-v1.8.md) | Polar reduction and the subidentity theorem |
| 8 | v1.9 | [`rounds/08-v1.9.md`](rounds/08-v1.9.md) | The general lemma refuted — finiteness is essential |
| 9 | v2.0 | [`rounds/09-v2.0.md`](rounds/09-v2.0.md) | The staircase squeeze |
| 10 | v2.1 | [`rounds/10-v2.1.md`](rounds/10-v2.1.md) | The bands are not enough |
| 11 | v2.2 | [`rounds/11-v2.2.md`](rounds/11-v2.2.md) | The commutation ladder and the single defect |
| 12 | v2.3 | [`rounds/12-v2.3.md`](rounds/12-v2.3.md) | The boundary cell — the finite Commutation Lemma proved |
| 13 | v2.4 | [`rounds/13-v2.4.md`](rounds/13-v2.4.md) | The sharp boundary — ω+1 |
| 14 | v2.5 | [`rounds/14-v2.5.md`](rounds/14-v2.5.md) | The sharpness theorem — the chain problem closed |
| 15 | v2.6 | [`rounds/15-v2.6.md`](rounds/15-v2.6.md) | The lattice frontier — retracts, the infinite-chain criterion, a two-dimensional failure |
| 16 | v2.7 | [`rounds/16-v2.7.md`](rounds/16-v2.7.md) | The pair-level method — realizability and the machine proof at height 4 |
| 17 | v2.8 | [`rounds/17-v2.8.md`](rounds/17-v2.8.md) | The one-way road — the E₂ audit, the pentagon erratum, the clean block-diagonal family on E₃ |
| 18 | v2.9 | [`rounds/18-v2.9.md`](rounds/18-v2.9.md) | The one crossing — the E₃ one-crossing census, the pentagon restored, the unary conflict |
| 19 | v3.0 | [`rounds/19-v3.0.md`](rounds/19-v3.0.md) | The two crossing — class enumeration, interface certificates, the first two full censuses |
| 20 | v3.1 | [`rounds/20-v3.1.md`](rounds/20-v3.1.md) | **The two-crossing census completed — the Two-Crossing Theorem** |
| 21 | v3.2 | [`rounds/21-v3.2.md`](rounds/21-v3.2.md) | **The three-crossing census — E₃ closed: Theorem C, CL holds on E₃** |
| 22 | v3.3 | [`rounds/22-v3.3.md`](rounds/22-v3.3.md) | **The Cut — direct SAT decision (E₄, E₅, B₄), semi-commutation on chains, the Cut Lemma, errata** |
| 23 | v3.4 | [`rounds/23-v3.4.md`](rounds/23-v3.4.md) | The Cut under the microscope — reachability (the gap is joins), contradiction shape, evidence to all lattices ≤ 8 elements, no uniform sideways escape on D_ω/E_ω |
| 24 | v3.5 | [`rounds/24-v3.5.md`](rounds/24-v3.5.md) | The dialgebraic layer, read thin: transposition (D1/D2 via adjoints), the failure zone is the unit of G* ⊣ G, D5 is the Duality Theorem, the Cut Lemma as a dialgebra L → 𝒪(L) whose orbit is tight exactly on trees |
| 25 | v3.6 | [`rounds/25-v3.6.md`](rounds/25-v3.6.md) | **The first GPU census**: 3.7·10¹¹ F exact, zero violators; orbit lag on exactly the non-top-closed 6-element lattices; the Cut Lemma is self-dual per F (Φ ⊣ cΨc); the uniform law concentrates on two generic classes |
| 26 | v3.7 | [`rounds/26-v3.7.md`](rounds/26-v3.7.md) | **The proved layer, machine-checked (Lean 4 + Mathlib); new: the Cut Lemma and CL at edge-height ≤ 5 (D_ω, M_ω × C₂, E_ω; heights 4 and 5 by verified ground refutation)**: stability, fusion, I2; Cut ⟺ R(F) = L, the gap is joins; Cut (per F, on L) ⟹ semi-CL; FCL and semi-CL on chains; principal cuts; No-Room (M_κ); Sharpness and Theorem A; duality; dialgebra and orbit theorems. Errata: the L2 proof misused Tarski, the L1 proof had a gap |

## Machine experiment material

- [`../experiments/README.md`](../experiments/README.md) — the census/solver stack, validation anchors, reproduction instructions.
- [`../data/e3-two-crossing-census.json`](../data/e3-two-crossing-census.json) — the complete 21-class census results.
- [`../experiments/sat/`](../experiments/sat/) — round 22: SAT encoding, DRAT certification, semi-commutation and Cut Lemma sweeps, z3 theories.
- [`../data/gpu-2026-10/`](../data/gpu-2026-10/) — round 25: the first GPU run (results.jsonl, batch.log); tables via `gpu/analyze.py`.
- [`../experiments/dialgebra/`](../experiments/dialgebra/) — round 24: dialgebra censuses in the thin model, the Cut Lemma transposition, orbit laxity.
- [`../data/e3-three-crossing-census.json`](../data/e3-three-crossing-census.json) — the complete 49-class three-crossing census results.