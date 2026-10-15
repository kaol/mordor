# Mordor — Bialgebraic & Dialgebraic Axioms Framework

An autonomous mathematics research program studying the **Commutation Lemma (CL)** for monotone bifunctions on complete lattices: when do the least and greatest fixed-point operators of a monotone bifunction F(x, y) commute — i.e., when does `lfp_x gfp_y F = gfp_y lfp_x F`?

Mordor is a formal system organized as three layers — **bialgebraic axioms** (algebra + coalgebra on one carrier), **dialgebraic axioms** (algebra and coalgebra fused), and a calculus of **bounds and interaction rules** governing how μ- and ν-axioms mix without collapse. The program combines this formal apparatus with exhaustive machine experiments: every claim in the research log is either proved, or enumerated and refuted to the last instance.

## Current status (v3.4 · The Cut Under the Microscope)

**Proven:**
- **Finite Commutation Lemma** — CL holds on every finite chain (§20.5, round 12). Round 22 gives a short proof of a stronger statement: on a finite chain, one-sided **semi-commutation** b∘a ⊑ a∘b already forces μν = νμ (§30.3).
- **Sharpness** — a complete chain satisfies CL iff it is finite (§22.5); the Ladder Construction is also verified symbolically in z3 (§30.5).
- **Theorem A** — every complete lattice containing an infinite chain fails CL; failures can be genuinely two-dimensional (2^ω, §23).
- **No-Room** — CL holds on lattices whose middle elements are all atom-and-coatom (edge-height ≤ 2, including infinite M_κ; §16.2, re-proved for all such lattices in §30.5). *Erratum:* earlier status lines said "height ≤ 3"; the argument does not reach edge-height 3 (§30.2(ii)).
- **Finite lattices, decided by SAT** (§30.1; DRAT-certified where marked): E₂ (Theorem B), E₃ (Theorem C), **E₄, E₅, B₄**, C₄×C₄, M₃×M₃, and **every lattice with ≤ 4 join-irreducibles** satisfy CL.

**Reductions (round 22):**
- **Cut Lemma ⟹ CL.** If every monotone F and every proper down-set D admit x ∈ D, y ∉ D with F(x, y) ≤ x or F(x, y) ≥ y, then semi-commutation (hence CL) holds; proved for principal cuts, machine-checked on 55,320 instances, open in general (§30.4).
- **Escape Lemma** and **Herbrand reduction** for lattices of bounded height (§30.5).
- **The gap is joins** (round 23): the Cut Lemma is equivalent to join-closure of the least down-set containing ⊥ closed under a and b⁻¹ (§31.1). No counterexample on any lattice with ≤ 8 elements, Π₄, B₅, C₃³; no translation-invariant sideways escape on D_ω or E_ω (§31.4–§31.6).

**Standing conjecture:** every chain-finite complete lattice satisfies CL. The open frontier is the Cut Lemma (finite lattices) and infinite chain-finite lattices from edge-height 3 up (D_ω, M_ω × C₂, E_ω).

## Repository layout

| Path | Contents |
|---|---|
| `docs/00-foundations.md` | The formal system: ambient setting, bialgebraic & dialgebraic axioms, bounds, interaction rules, metatheorems (§1–§7) |
| `docs/01-early-notes.md` | Early revision notes and first exploration findings (v1.1–v1.2) |
| `docs/rounds/` | The research log, one file per exploration round (rounds 2–23, versions v1.3 → v3.4) |
| `docs/README.md` | Index to the research log with one-line summaries |
| `experiments/` | The machine-experiment stack: exact realizability CSP solver, E₃ census pipeline, validation harness |
| `experiments/sat/` | Round 22: direct SAT encoding (CaDiCaL via PySAT), DRAT certification, semi-commutation and Cut Lemma sweeps, z3 theories |
| `data/` | Machine-experiment results (JSON) |

## The machine method, in one paragraph

CL fails on a lattice L exactly when some interval of L carries a **commuting polar pair** (a, b) — monotone, bound-fixing, a∘b = b∘a — is **realizable** as the derived pair of a monotone bifunction (a(x) = gfp_y F(x, y), b(y) = lfp_x F(x, y)). Realizability is an exact finite constraint problem on F: pin cells F(x, a(x)) = a(x), F(b(y), y) = b(y), the strong exclusions (E2⁺: y ≰ a(x) ⟹ F(x, y) ∉ ↑y; E3⁺: b(y) ≰ x ⟹ F(x, y) ∉ ↓x), and monotonicity in both coordinates. The solver (unary domains → AC-3 on cover arcs → MRV DFS) is exact — validated against the exhaustive chain-4 ground truth, 223 = 223. Censuses kill commuting pairs in bulk with sound relaxations only (T1 block unary tables, 40-cell interface sub-CSPs); every survivor is refuted by the exact solver. See `experiments/README.md`. Since round 22 the same criterion is also solved directly as one SAT instance per interval, with the pair (a, b) as variables (`experiments/sat/`).

## Reproducing the censuses

The census pipeline is a single self-contained TypeScript program (`experiments/e3-two-crossing-census.ts`); each two-crossing class is one parameter line. Each class census runs in about a minute in a sandboxed TypeScript runner. Anchors and tripwires for revalidation are listed in `experiments/README.md`.

## Reading the log

Start with `docs/README.md`. Each round file is self-contained prose: what was asked, what the machine found, what was proved, what remains open, and an honest-scope section stating exactly what the round does *not* cover. Errata are recorded in place and withdrawn explicitly — audits are themselves censuses.