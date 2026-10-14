# Mordor — Machine Experiments

The experimental stack behind the research log. Everything here is exact: sound relaxations are used only to kill pairs in bulk, and every surviving pair is refuted (or witnessed) by the exact realizability solver.

## The realizability CSP

CL fails on a complete lattice L iff some **commuting polar pair** (a, b) — monotone, bound-fixing, a∘b = b∘a — is realizable as the derived pair of a monotone bifunction: a(x) = gfp_y F(x, y), b(y) = lfp_x F(x, y). Realizability is a finite CSP over the cells F(x, y):

- **pins:** F(x, a(x)) = a(x); F(b(y), y) = b(y);
- **E2⁺:** y ≰ a(x) ⟹ F(x, y) ∉ ↑y;
- **E3⁺:** b(y) ≰ x ⟹ F(x, y) ∉ ↓x;
- **monotonicity** in both coordinates (AC-3 over lattice *cover* arcs — never grid-index adjacency; see the log §26.1 for that bug).

The solver: unary domains → AC-3 → MRV DFS (node cap 300). **Exactness anchor:** on the 4-chain the derived-pair ground truth (223 pairs) and the CSP-satisfiable set are equal, 223 = 223.

## Files

- `e3-comm-totals.ts` — commutation-total harness. Structure-aware per-class enumeration of commuting polar pairs (per-column M₅ composition with routing-consistency bits and H4 bound-only relief). Expected totals for six configurations covering every nest structure (STAR/CHN/SGL/ID), h4-relief patterns, and the RB[0] ≠ 0 path are embedded; the run must return `all: true`.
- `e3-two-crossing-census.ts` — the full census pipeline: T1 block unary tables, three 40-cell interface sub-CSP tables, masked structure-aware enumeration, exact solvePair on every survivor. One parameter line per class (`RA`, `RB`, `ST`, `LO`, `HI`, `CLS`).

## Soundness rules (why the censuses prove anything)

1. **T1 (unary conflict):** a realizable pair has a nonempty domain at every cell. A block table entry is computed from the pins and exclusions alone — killing is sound.
2. **Interfaces:** an interface is a sub-CSP (fewer cells, fewer arcs) of the exact CSP; a solution of the full CSP restricts to a solution of the sub-CSP, so sub-unsat ⟹ unrealizable.
3. **Exact solver:** unsat with zero search nodes = unsat by pure propagation from sound unary domains and cover arcs. Nothing unsound can kill a realizable pair, and positive controls (the twisted-meet witness) are found by the same stack.

## Anchors and tripwires (revalidate after any change)

- Comm totals: the six embedded expectations in `e3-comm-totals.ts` — all must be exact.
- Census anchors (survivors, and every kill in pure propagation): `001.010` → 3,814; `002.021` → 9,271; `000.021` → 15,478.
- Chain-4 exactness: 223 = 223 (see the log §26.1).
- **Block-coordinate tripwire:** T1 over all nine blocks is equivalent to full-grid unary nonemptiness. If any census survivor dies at the unary stage (`u0 > 0`), the block builder or the solver is broken — this is exactly how the §28.1 rebuild bug was caught (cells must be evaluated at their true coordinates `e3(i,p)`, `e3(j,q)`, with the map images entering only the constraints).

## Running

Both programs are self-contained TypeScript with a `main()` entry, written for a sandboxed TypeScript runner (no filesystem, no `Math.random`/`Date.now`, ~60 s budget, <16 MiB). Each class census is one full-range pass (~1 minute); classes too large for one pass are sliced with `LO`/`HI` on the `A[0]` range and the per-slice survivor counts summed.

Expected census outcome for every two-crossing class: `sat: 0, cap: 0, dfk: 0, u0: 0, mx: 0` and `surv` equal to the `survivors` value in [`data/e3-two-crossing-census.json`](../data/e3-two-crossing-census.json).