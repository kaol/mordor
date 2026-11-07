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
