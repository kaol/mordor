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

## Round 26: containment and x ≤ y (§34.3z¹²⁵)

- `containment_audit.py records FILE | random SEED N`: existential test of strict interval containment and of the gap
  parent property (causal parents, all separator choices). `xy_audit.py`: bad pairs with x ≰ y over all runs.
  Output `out_containment_audit.txt`; `xy_counterexample.json` (|L| = 12, height 4).

## Round 26: maximum-gap descent (§34.3z¹²⁶)

- `gapmax_audit.py records FILE | random SEED N | hunt SEED SECONDS FILES... | rule FILE | rulehunt SEED SECONDS FILES...`:
  existential and universal maximum-gap descent over all runs, on records, random instances and mutations of hard
  instances; `rule`/`rulehunt` test the one-step lookahead rule (minimize the next maximum gap). Output
  `out_gapmax_audit.txt`; lookahead counterexamples `gapmax_lookahead_counterexample_s7*.json` (|L| = 12, height 4).

## Round 26: shortest runs and selection rules (§34.3z¹²⁷)

- `shortest_audit.py records FILE | hunt SEED SECONDS FILES...`: maximum-gap descent among the shortest runs.
- `nested_rule.py records FILE | hunt SEED SECONDS VARIANT FILES...`: deterministic rules `nested` (prefer a maximal
  separator below the column), `nested_rank`, and `all` (the full process). Output `out_shortest_nested.txt`;
  smallest rule failures `nested_*_counterexample_s*.json`.
- `wide_h6.py SEED SECONDS MIN_SIZE` (§34.3z¹²⁸): shortest-run descent on wide edge-height-6 closure-system lattices
  (|L| 20–69), hill-climbing toward hard instances. Output `out_wide_h6.txt`.

## Round 26: the state graph (§34.3z¹³⁰)

- `state_graph_audit.py records FILE | hunt SEED SECONDS FILES...`: the reachable state graph over all separator
  choices, completion distance d (Lean `ShortestRun.dist`), the optimal gap-successor property at all reachable states
  and at states on shortest paths, and the exchange depth of non-descending shortest runs. Output
  `out_state_graph.txt`; smallest failures `state_graph_fail_*_s*.json` (|L| = 12, height 4).

## Round 26: general separators and the response rule (§34.3z¹³¹)

- `general_sep.py records FILE | hunt SEED SECONDS FILES...`: general (non-maximal) separators; the canonical
  response rule (separator = F(x, y)), polar rules, and existential descent over general separators.
- `response_length.py SEED SECONDS K H`, `response_width3.py SEED SECONDS KS`: hill-climbing the response-run length
  at fixed edge-height against lattice size. Output `out_response_rule.txt`; smallest response-rule descent failures
  `response_rule_counterexample_s*.json`.
