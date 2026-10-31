# Heavy runs (prepared in round 26, §34.3z⁶⁰)

These are the runs that exceed what a cloud session can afford. Each has a precise payoff, and each result is
independently checkable. All of them are CPU and RAM jobs.

**Why not the GPU.** The open fronts are SAT refutations and statements about infinite lattices. CDCL search is
branch-heavy and sequential, and GPU SAT solvers are not competitive on it. The GPU census (`gpu/`) measures finite
lattices, where Cut and CL are theorems (`cut_finite`, `cl_finite`), so it has no signal left to find (§34.3z⁵⁶ S7,
§34.3z⁵⁷ N8). The descent game was solved exactly (§34.3z⁴⁵). Use the cores for a portfolio instead.

Requirements: Python ≥ 3.10 with `python-sat` and `numpy`; `drat-trim` (https://github.com/marijnheule/drat-trim)
as `$DRAT_TRIM`. Strongly recommended: `kissat` (https://github.com/arminbiere/kissat), or `cadical`, for proofs on
large CNFs. `pysat_drat.py` is a slow stand-in with the same calling convention. For Lean replay: the repository's
`lean/` toolchain.

## 1. Edge-height 6: the ground-refutation portfolio (highest value)

```bash
experiments/heavy/h6_portfolio.sh ~/h6 A B          # variants A–D, see the script; default A B C
tail -F ~/h6/*.log | grep --line-buffered -E 'round|UNSAT|exited|stopped'
```

- **Payoff.** UNSAT proves the Cut Lemma, hence semi-CL and CL, on every bounded poset and complete lattice of
  edge-height ≤ 6, including M_ω² × C₃. That settles one of the four open fronts (§34.3z⁵⁴). SAT at the cap is
  inconclusive. Since `cut_finite` the search can only end in UNSAT or never.
- **Variants.** All use frontier selection (`front`), which is better at H = 6 than your current
  `run_height.py 6 4000 1 forget=…` (tightness selection, §34.3z⁴⁰).
  - A: two terms per round.
  - B: four per round, with `allmid`, CaDiCaL 1.9.5.
  - C: one per round, CaDiCaL 1.9.5, no phase seeding.
  - D: eight per round.
- **Resources measured here.**
  - A: 2 GB at 800 terms.
  - B: 8 GB at 1,180 terms.
  - Memory grows roughly with the square of the term count. Time per 25 rounds had reached 20–25 min by 1,000
    terms.
  - Budget: 16–32 GB per variant beyond about 1,500 terms; days of wall clock.
- **Crash safety.** Each variant checkpoints its terms every 25 rounds and restarts itself from the checkpoint if
  the process dies; rare CaDiCaL crashes are recorded in `experiments/sat/README.md`.
- **On UNSAT** (in the work directory):
  ```bash
  DRAT_TRIM=/path/to/drat-trim experiments/heavy/certify_ground.sh 6 <tag> /path/to/kissat
  ```
  - This writes the drat-trim core and `lean/Mordor/CutHeight6.lean`, then builds it with `bv_decide`. The H = 5
    core (832 clauses) took 14 minutes, so expect much longer here.
  - It refuses to overwrite an existing file unless `FORCE=1`.
  - The pipeline was tested end to end on H = 5 outputs: Glucose and drat-trim, `s VERIFIED`, 935-clause core,
    `cut_lean.py`.
- **Send back.** The last `round` line of each log. On UNSAT: the `.cnf`, `.maps.pkl` and `.core` files, and the
  drat-trim summary.

## 2. DC2 on M_ω² × C₃ at larger pools (independent product milestone)

```bash
DRAT_TRIM=/path/to/drat-trim experiments/heavy/run_dc2.sh ~/dc2 /path/to/kissat            # default instances
DRAT_TRIM=/path/to/drat-trim experiments/heavy/run_dc2.sh ~/dc2 /path/to/kissat 5,4 4,5 5,5
```

- **Payoff.** It extends the UNSAT table of §34.3z⁵³/⁵⁸ (largest so far: (3, 3), 1,308 s), now with checked
  proofs. DC2 for M_ω² × C₃ needs every k ≤ 30 and m ≤ M(k) (§34.3z⁵⁸–⁵⁹). This is evidence, and a test of whether
  the cost per instance grows tamely; it is not a proof of DC2.
- **Sizes** (measured: encoder about 20–75 s and 0.2 GB per instance; CNF on disk ≈ 26 bytes per clause):

  | (k, m) | variables | clauses |
  |---|---|---|
  | (4, 2) / (2, 4) | 0.70 M / 0.71 M | 6.9 M / 7.1 M |
  | (5, 2) | 1.24 M | 13.1 M |
  | (4, 3) / (3, 4) | 1.26 M / 1.27 M | 13.4 M / 13.6 M |
  | (5, 3) | 2.10 M | 23.8 M |
  | (4, 4) | 2.12 M | 24.1 M |

- **Expected time.** (3, 3) (0.71 M variables) took 22 min with PySAT CaDiCaL 1.5.3. Expect hours per instance at
  2 M variables with kissat. DRAT proofs are large: the (2, 2) proof was 0.56 GB, verified in 166 s. Delete each
  proof after its `s VERIFIED`.
- **Encoder check.** The dumped CNF reproduces the log: (2, 2) has 171,450 variables and re-solves UNSAT; the
  depth-1 control `[2]` is SAT.
- **Send back.** `dc2_summary.txt`. Any `s SATISFIABLE` is important: rerun that instance with
  `dc2_batch.py solve k,m` and keep the model.

## Not prepared

- *`box_cut.py cut 5`*: you can stop it. Box Cut is a side conjecture with no remaining consequence for CL, and no
  finite box counterexample exists with ≤ 11 elements at edge-height ≤ 5 (§34.3z¹⁵ note).
- *The H = 6 ground search with lattice operations* (meets and joins as terms, so that `capturer_meet_escapes`,
  §34.3z⁵⁹, is expressible): this needs new encoder code, not more compute.
