# Mordor — Bialgebraic & Dialgebraic Axioms Framework

An autonomous mathematics research program studying the **Commutation Lemma (CL)** for monotone bifunctions on complete lattices: when do the least and greatest fixed-point operators of a monotone bifunction F(x, y) commute — i.e., when does `lfp_x gfp_y F = gfp_y lfp_x F`?

Mordor is a formal system organized as three layers — **bialgebraic axioms** (algebra + coalgebra on one carrier), **dialgebraic axioms** (algebra and coalgebra fused), and a calculus of **bounds and interaction rules** governing how μ- and ν-axioms mix without collapse. The program combines this formal apparatus with exhaustive machine experiments: every claim in the research log is either proved, or enumerated and refuted to the last instance.

## Current status (v3.8 · The Proved Layer, Read Back to the Source)

**Proven:**
- **Finite Commutation Lemma** — CL holds on every finite chain (§20.5, round 12). Round 22 gives a short proof of a stronger statement: on a finite chain, one-sided **semi-commutation** b∘a ⊑ a∘b already forces μν = νμ (§30.3).
- **Sharpness** — a complete chain satisfies CL iff it is finite (§22.5); the Ladder Construction is also verified symbolically in z3 (§30.5).
- **Theorem A** — every complete lattice containing an infinite chain fails CL; failures can be genuinely two-dimensional (2^ω, §23).
- **Edge-height ≤ 5** (round 26, §34.3f–h, Lean): the Cut Lemma holds in every bounded poset with no chain of seven elements, so semi-CL and CL hold on every such complete lattice, infinite ones included (D_ω, M_ω × C₂, **E_ω**). The height-3 case is a hand proof. Heights 4 and 5 are drat-trim-verified ground refutations, replayed in Lean by `bv_decide`. Per F, the same holds on any complete lattice whose subalgebra ⟨⊥, ⊤⟩_F has edge-height ≤ 5 (`semi_local5`).
- **CL fails under M0 too** (§34.3i, Lean): F(x, y) = min(x + 1, y ∸ 1) on ω + 1 preserves ω-sups and ω-infs, commutes, and has m ≠ n.
- **Semi-CL is local** (§34.3j, Lean): if semi-CL holds on [m, n], then m = n iff semi-commutation holds on [m, n]; unconditional at edge-height ≤ 5.
- **No-Room** — CL holds on lattices whose middle elements are all atom-and-coatom (edge-height ≤ 2, including infinite M_κ; §16.2, re-proved for all such lattices in §30.5). *Erratum:* earlier status lines said "height ≤ 3"; the argument does not reach edge-height 3 (§30.2(ii)).
- **Dialgebraic layer, thin model** (round 24): D1 holds when G is a right adjoint (μ^{F,G} = μ(G*∘F)), and dually D2. For meet-preserving G, δ₀ is iso ⟺ F(A₀) ∈ Im G. So the Lambek failure zone is the unit of G* ⊣ G, which overturns the §13.3 negative. D5 through an anti-automorphism is the Duality Theorem §22.1 (§32.2–§32.4).
- **The Cut Lemma is self-dual per F** (round 25): the down-set step Φ and the up-set step Ψ satisfy Φ ⊣ c∘Ψ∘c, so R_k ∩ U_j = ∅ ⟺ R_{k+j} ≠ L for any monotone a, b. The down-set and up-set forms of the lemma coincide for each F (§33.3).
- **Finite lattices, decided by SAT** (§30.1; DRAT-certified where marked): E₂ (Theorem B), E₃ (Theorem C), **E₄, E₅, B₄**, C₄×C₄, M₃×M₃, and **every lattice with ≤ 4 join-irreducibles** satisfy CL.

- **Machine-checked in Lean 4 + Mathlib** (round 26, `lean/`): stability, I1, fusion, I2; the Finite Commutation and Semi-Commutation Lemmas on finite chains; principal cuts; No-Room (CL at edge-height ≤ 2, M_κ for every κ); **Sharpness** (complete chains: CL ⟺ finite) and **Theorem A** (an infinite chain ⟹ CL fails), the infinite side included; Cut ⟺ R(F) = L, and on finite lattices "the gap is joins"; the Duality Theorem; the dialgebra theorems of round 24; orbit tightness; the self-duality of round 25; the axioms of the foundations themselves, derived in the thin model and, where Mathlib allows, in any category (`lean/Mordor/Axioms/`, foundations §11). Doing so found a wrong step in the log's L2 proof and a gap in its L1 proof (§34.1). Cut ⟹ semi-CL now holds per F on L itself, with no interval reduction (§34.2).

**Reductions (round 22):**
- **Cut Lemma ⟹ CL.** If every monotone F and every proper down-set D admit x ∈ D, y ∉ D with F(x, y) ≤ x or F(x, y) ≥ y, then semi-commutation (hence CL) holds; proved for principal cuts, machine-checked on 55,320 instances, open in general (§30.4).
- **Escape Lemma** and **Herbrand reduction** for lattices of bounded height (§30.5).
- **The gap is joins** (round 23): the Cut Lemma is equivalent to join-closure of the least down-set containing ⊥ closed under a and b⁻¹ (§31.1). No counterexample on any lattice with ≤ 8 elements, Π₄, B₅, C₃³; no translation-invariant sideways escape on D_ω or E_ω (§31.4–§31.6).
- **The Cut Lemma as a dialgebra L → 𝒪(L)** (round 24): transposed along sup ⊣ ↓, it is the principal-cut proposition μκ = ⊤. The comparison square is lax. Along the orbit it is tight for every F exactly on lattices where L ∖ {⊤} is a tree. That direction is proved; the converse holds on all 73 lattices of size 5–7, and the delay grows off trees (§32.6).
- **GPU census** (round 25, Radeon W6600): 373,086,957,077 bifunctions enumerated exactly on 13 lattices of ≤ 6 elements, plus 2.4·10⁸ heat-bath samples up to B5. Zero tripwires and zero CL / semi-CL / Cut violators. Orbit lag is positive on exactly the 6 non-top-closed 6-element lattices. The uniform law concentrates on commuting and generic polar F, so it calibrates rather than searches (§33).

**Standing conjecture:** every chain-finite complete lattice satisfies CL. Formally (`lean/Mordor/Frontier.lean`), it follows from one statement: for every monotone F on a chain-finite complete lattice, R(F) is join-closed (§34.4a). The open frontier is the Cut Lemma at edge-height ≥ 6 and on chain-finite lattices of unbounded height; edge-height ≤ 5 is settled, in Lean (§34.3f–h).

## Repository layout

| Path | Contents |
|---|---|
| `docs/00-foundations.md` | The formal system: ambient setting, bialgebraic & dialgebraic axioms, bounds, interaction rules, metatheorems, with status tags; the CL program and the Cut Lemma interface (§0–§10, v3.7) |
| `docs/01-early-notes.md` | Early revision notes and first exploration findings (v1.1–v1.2) |
| `docs/rounds/` | The research log, one file per exploration round (rounds 2–26, versions v1.3 → v3.8) |
| `docs/02-the-source.md` | The framework's Tolkien vocabulary read back to its source; the sharpened axioms (I11 = CL guarded by the Cut Lemma) |
| `docs/README.md` | Index to the research log with one-line summaries |
| `experiments/` | The machine-experiment stack: exact realizability CSP solver, E₃ census pipeline, validation harness |
| `gpu/` | GPU census of the projection F ↦ (a, b): exact enumeration and heat-bath MCMC with tripwires (PyTorch, ROCm/CUDA/CPU); see `gpu/README.md` |
| `experiments/sat/` | Round 22: direct SAT encoding (CaDiCaL via PySAT), DRAT certification, semi-commutation and Cut Lemma sweeps, z3 theories |
| `lean/` | Round 26: Lean 4 / Mathlib proofs of the log's proved core (Mathlib is a lake dependency, not committed) |
| `data/gpu-2026-10/` | Round 25: results.jsonl and batch.log of the first GPU run |
| `experiments/dialgebra/` | Round 24: thin-model dialgebra censuses (transposition, failure zone, D5), the Cut Lemma transposition, orbit-laxity z3 searches |
| `data/` | Machine-experiment results (JSON) |

## The machine method, in one paragraph

CL fails on a lattice L exactly when some interval of L carries a **commuting polar pair** (a, b) — monotone, bound-fixing, a∘b = b∘a — is **realizable** as the derived pair of a monotone bifunction (a(x) = gfp_y F(x, y), b(y) = lfp_x F(x, y)). Realizability is an exact finite constraint problem on F: pin cells F(x, a(x)) = a(x), F(b(y), y) = b(y), the strong exclusions (E2⁺: y ≰ a(x) ⟹ F(x, y) ∉ ↑y; E3⁺: b(y) ≰ x ⟹ F(x, y) ∉ ↓x), and monotonicity in both coordinates. The solver (unary domains → AC-3 on cover arcs → MRV DFS) is exact — validated against the exhaustive chain-4 ground truth, 223 = 223. Censuses kill commuting pairs in bulk with sound relaxations only (T1 block unary tables, 40-cell interface sub-CSPs); every survivor is refuted by the exact solver. See `experiments/README.md`. Since round 22 the same criterion is also solved directly as one SAT instance per interval, with the pair (a, b) as variables (`experiments/sat/`).

## Reproducing the censuses

The census pipeline is a single self-contained TypeScript program (`experiments/e3-two-crossing-census.ts`); each two-crossing class is one parameter line. Each class census runs in about a minute in a sandboxed TypeScript runner. Anchors and tripwires for revalidation are listed in `experiments/README.md`.

## Reading the log

Start with `docs/README.md`. Each round file is self-contained prose: what was asked, what the machine found, what was proved, what remains open, and an honest-scope section stating exactly what the round does *not* cover. Errata are recorded in place and withdrawn explicitly — audits are themselves censuses.