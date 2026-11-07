# Finite separators (round 26, §34.3z¹²⁰)

- `finite_landmarks.py [samples] [seed]`: the extremal-separator refinement (T₀ = {⊥, ⊤}; every bad cross pair gets a
  maximal upper separator; meet-closure) on random closure-system lattices with random monotone F and down-set D;
  stage counts and |T| by height. `climb SEED SECONDS`: hill-climbing on (F, D) maximizing the stage count.
  `width3 SEED POINTS RESTARTS`: the same on height-3 linear spaces of growing width. Output `out_finite_landmarks.txt`.
  Finite lattices always end (separated or stuck), so these runs only measure stage counts; they cannot exhibit a
  witness-free structure.

## Round 26: separator stages (§34.3z¹²¹)

- `separator_stages.py`: bitset lattices (closure systems), monotone F by a cover DP, the process of
  `lean/Mordor/SeparatorStages.lean` with stuck/separated stops and full traces.
  - `climb SEED SECONDS K OUT.json`: hill-climb maximizing the greedy stage count;
  - `climbx SEED SECONDS K OUT.json`: hill-climb maximizing the *existential* minimum (exact branching over all
    maximal-separator choices);
  - `compare SEED N`: existential minimum ≤ greedy ≤ universal maximum on small instances.
  Output `out_separator_stages.txt`; replayable maximal instances (lattice sets, F table, D, greedy trace) in
  `stage_records.json`.

## Round 26: rank audit (§34.3z¹²²)

- `rank_audit.py random SEED N | records FILE.json`: enumerates every run (all maximal-separator choices) and tests
  the rank-parent property RP (causal and any-parent; stuck stages exempt), plus nesting of the carriers of the
  causal fork. Output `out_rank_audit.txt`.
- `multiset_audit.py FILE.json`: the multisets of response closure ranks along every run; a run that repeats a
  multiset admits no strictly decreasing multiset potential.

## Round 26: ancestry and potentials (§34.3z¹²³)

- `ancestry_audit.py records FILE | aggregate SEED N`: separator tokens with birth stages, minimum meet-supports of
  bad-pair coordinates, fresh-token and coverage-cone checks, row/column fans, cross-generation response matrices;
  aggregate-first greedy against greedy. Output `out_ancestry_audit.txt`.
- `potential_audit.py random SEED N | records FILE | hunt SEED SECONDS K | hunt_from SEED SECONDS FILES...`:
  exhaustive existential test of the parent-decrease property for the potentials resp, col, gap, respgap; `hunt_from`
  mutates hard recorded instances. Output `out_potential_audit.txt`.
