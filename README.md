# Mordor — Bialgebraic & Dialgebraic Axioms Framework

An autonomous mathematics research program studying the **Commutation Lemma (CL)** for monotone bifunctions on complete lattices: when do the least and greatest fixed-point operators of a monotone bifunction F(x, y) commute — i.e., when does `lfp_x gfp_y F = gfp_y lfp_x F`?

Mordor is a formal system organized as three layers — **bialgebraic axioms** (algebra + coalgebra on one carrier), **dialgebraic axioms** (algebra and coalgebra fused), and a calculus of **bounds and interaction rules** governing how μ- and ν-axioms mix without collapse. The program combines this formal apparatus with exhaustive machine experiments: every claim in the research log is either proved, or enumerated and refuted to the last instance.

## Current status (v3.1 · The Two Crossing, Closed)

**Proven:**
- **Finite Commutation Lemma** — CL holds on every finite chain (§16, rounds 8–12).
- **Sharpness** — the boundary is exactly ω+1: the staircase squeeze fails at ω+1 and CL holds below it (§21–§22).
- **The general lemma is refuted** — finiteness is essential; a two-dimensional failure exists (§23, round 15).
- **No-Room** — CL holds on all complete lattices of height ≤ 3 (§14).
- **Theorem B** — CL holds on E₂ (the 3+3 crown of three columns... see the log for the exact statement; exhaustive machine proof at height 4, §24–§25).

**Machine-clean families (exhaustively censused, zero realizable witnesses):**
- E₃ block-diagonal (round 17), E₃ one-crossing (round 18), and now **E₃ two-crossing — all 21 canonical classes** (rounds 19–20).

**Standing conjecture:** every chain-finite complete lattice satisfies CL. The frontier is exactly the **three-crossing classes on E₃** — by the corollaries of rounds 18 and 20, any E₃ violator must cross all three source columns.

## Repository layout

| Path | Contents |
|---|---|
| `docs/00-foundations.md` | The formal system: ambient setting, bialgebraic & dialgebraic axioms, bounds, interaction rules, metatheorems (§1–§7) |
| `docs/01-early-notes.md` | Early revision notes and first exploration findings (v1.1–v1.2) |
| `docs/rounds/` | The research log, one file per exploration round (rounds 2–20, versions v1.3 → v3.1) |
| `docs/README.md` | Index to the research log with one-line summaries |
| `experiments/` | The machine-experiment stack: exact realizability CSP solver, E₃ census pipeline, validation harness |
| `data/` | Machine-experiment results (JSON) |

## The machine method, in one paragraph

CL fails on a lattice L exactly when some **commuting polar pair** (a, b) — monotone, bound-fixing, a∘b = b∘a — is **realizable** as the derived pair of a monotone bifunction (a(x) = gfp_y F(x, y), b(y) = lfp_x F(x, y)). Realizability is an exact finite constraint problem on F: pin cells F(x, a(x)) = a(x), F(b(y), y) = b(y), the strong exclusions (E2⁺: y ≰ a(x) ⟹ F(x, y) ∉ ↑y; E3⁺: b(y) ≰ x ⟹ F(x, y) ∉ ↓x), and monotonicity in both coordinates. The solver (unary domains → AC-3 on cover arcs → MRV DFS) is exact — validated against the exhaustive chain-4 ground truth, 223 = 223. Censuses kill commuting pairs in bulk with sound relaxations only (T1 block unary tables, 40-cell interface sub-CSPs); every survivor is refuted by the exact solver. See `experiments/README.md`.

## Reproducing the censuses

The census pipeline is a single self-contained TypeScript program (`experiments/e3-two-crossing-census.ts`); each two-crossing class is one parameter line. Each class census runs in about a minute in a sandboxed TypeScript runner. Anchors and tripwires for revalidation are listed in `experiments/README.md`.

## Reading the log

Start with `docs/README.md`. Each round file is self-contained prose: what was asked, what the machine found, what was proved, what remains open, and an honest-scope section stating exactly what the round does *not* cover. Errata are recorded in place and withdrawn explicitly — audits are themselves censuses.