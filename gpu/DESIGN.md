# Mordor GPU census: design

Dense reference for AI readers. Human quickstart: `README.md`. Pattern and conventions follow `kaol/eat-the-fibre`
(static `Plan`, pure batched step, Mealy driver with checkpoints, independent reference, loud self-test).

## 0. Object

For a finite lattice L, the total space is the set of monotone bifunctions F : L×L → L, and the base is the set of
pairs (a, b), with a(x) = νY.F(x,Y) and b(y) = μX.F(X,y). Mordor studies the projection π : F ↦ (a, b): CL, the
semi-commutation lemma, the Cut Lemma and the realizability criterion are all statements about π (round 22, §30).
The SAT layer (`experiments/sat/`) decides those statements per lattice but produces no *measure*. This engine produces
the measure: exact counts over every F (census), or estimates under the uniform law on F (mcmc) where no census fits.

Per F, `observe` computes a, b, m = μ(a), n = ν(b), φ = a∘b, ψ = b∘a, the closure R(F) (least down-set containing ⊥,
closed under a and b⁻¹), and a closed set of features:

| feature | meaning | research use |
|---|---|---|
| `joint` (comm, ψ≤φ, φ≤ψ, polar, m=n) | 32-bin joint law | one-sided characterizations (§30.7(5)); conditional rates such as P(m=n ∣ ψ≤φ) |
| `ncf` | number of common fixed points | I2 (§14), as data |
| `ndef`, `sig` | number of defects φ(x) ≠ ψ(x); signature (rel(φ(x),x), rel(ψ(x),x), rel(φ(x),ψ(x))) ∈ {=,<,>,∥}³ | the L-straddle (§19.5) beyond chains |
| `rstages`, `rfirst` (+ `_polar`) | number of growth stages of R(F); first stage R_k that is not an ideal | the join gap of the Cut Lemma (§31.1): is R(F) built through ideals? |
| `fibres` (census, opt-in) | exact fibre sizes ∣π⁻¹(a,b)∣ and the image size | the leaf-data measure on the base; generalizes "223 derived pairs on C4" |
| `trips` | violations of proved theorems | L1 tripwires (§4) |
| `viols` (cl, semi, cut) | CL, semi-CL, Cut Lemma violated by this F | conjectures; nonzero = discovery, witnesses kept |

## 1. Mu side: the static plan

| element | content | data-dependent? |
|---|---|---|
| `lattices.Lat` | order matrix, covers, join/meet tables, linear extension, height | no |
| `Lat.mon`, `Plan.rowle` | Mon(L) as rows; pointwise order on rows (M×M) | no |
| `Lat.n_bifunctions` | exact census total by DP (state = rows of elements with an unprocessed upper cover); `None` if too wide | no |
| `Plan.colors` | greedy coloring of the cover graph of L×L (cells); per class: lower/upper neighbour cells, padded with constant ⊥/⊤ cells | no |
| `Plan.cnt`, `Plan.ilist` | for each interval [u, v]: its size and its elements | no |
| `Hist` schema | the closed feature vocabulary above; `SCHEMA = 1` versions it | no |

**Arrow condition holds.** The census is `leaf ∘ level_{n−1} ∘ … ∘ level_j`, where `level_k` assigns the row of the
k-th element of the linear extension subject to row ≥ rows of its lower covers. The schedule and the constraint
layout depend only on L, so one batch can mix partial assignments from any prefix (level-synchronous enumeration),
exactly as eat-the-fibre mixes fibres. The frontier is the only thing that flows. The MCMC sweep is a fixed
composition of color-class kernels, each a pure function of (state, uniforms).

## 2. Observation: a catamorphism into a commutative monoid

`observe` is pure and is the only place where the mathematics of one F lives (both drivers call it). `Hist` is a
compound carrier of counts and bincounts with addition as merge: commutative, associative, unit = empty Hist. This
banana-split is what makes batch splitting, prefix groups, checkpoints, resumption and merging of runs exact and
order-independent. The one non-commutative part is the witness list (first ≤ 20 per kind), which depends on order.
It is kept only to show examples, and its *count* is in the monoid.

## 3. Nu side: the drivers

- `census`: a Mealy machine over a stack of (level, batch). Step: pop; if the batch exceeds `MORDOR_MEM`, split it and
  push the pieces; otherwise push `census_level` (or observe, at the leaves). The measure (n − k, |batch|) decreases
  lexicographically, so it is productive and terminates; memory is bounded by the budget, not by the census size.
  Work is cut into deterministic prefix jobs (the level where the frontier first exceeds 2000 partial assignments).
  A checkpoint is (lattice id, schema, prefix depth, #jobs, jobs done, Hist[, Fibres]); resumption restarts at the
  next job, so resumed and uninterrupted runs give identical JSON (`tests`).
- `mcmc`: chains are a batch dimension. Step = one systematic heat-bath sweep: each cell of a color class is
  resampled uniformly from [⋁ lower-neighbour values, ⋀ upper-neighbour values]. Reversible w.r.t. the uniform law
  on monotone F (heat bath); irreducible, since any F descends cell by cell in a linear extension to constant-⊥;
  aperiodic (self-loops). The checkpoint carries chain states and the RNG state, so resumption is bit-identical.

## 4. Constraint levels

- **L1, exact arithmetic.** Integer gathers and comparisons only, except the down-closure of R(F): a 0/1 matrix
  product of size ≤ 63, exact in float32 (TF32 off). There is no residue arithmetic, so eat-the-fibre's 2^24 bound
  is not needed.
- **L1, tripwires (theorems of the log, checked on every F).** I1 m ≤ n (§13), L1 a(n) = n and L2 b(m) = m (§13),
  fusion Fix(a∘b) = Fix(a) ∩ Fix(b) (§14.1), I2 m = n ⟺ exactly one common fixed point (§14.1). Any nonzero count
  is an engine bug (or a wrong proof) and is reported loudly with witnesses.
- **L2, engine contract.**
  - `Plan.selftest` compares `observe` with `reference.observe_one` on random monotone F at every start. The reference
    is independent: derived maps from fixed-point *sets* rather than Kleene iteration, and a naive closure for R(F).
  - Tests: census totals = DP counts; the log's anchors (C3: 175 / 137 commuting / 20 with m ≠ n / 27 pairs;
    C4: 24,696 / 12,450 / 7,280 / 6,440 polar / 223 pairs; B2: 28,224 / 15,984 commuting); census ≡ reference loop
    over all 28,224 F of B2; MCMC ≈ census on C4 (χ²); checkpoint resumption for both drivers.
- **L3, interpretive.** MCMC rates are estimates under the stationary law only once the chains have mixed. `mixing`
  reports, per joint bit, the rate in the ⊥-started vs the ⊤-started half of the chains (overdispersed starts) with
  a z-score. The z-score is optimistic, because samples within a chain are autocorrelated. Job 5 (N5 MCMC) is there
  to calibrate the sampler against the N5 census. `rfirst` is defined relative to the stage sequence R_0 ⊂ R_1 ⊂ …
  (one step = a, b⁻¹ and down-closure at once); another schedule would give other stage indices, the same R(F).

## 5. Feasibility and budgets

- Census: totals grow fast. C5 has 1.7·10⁷ F, N5 3.1·10⁷, M3 1.3·10⁸, C6 5.5·10¹⁰; the other 6-element lattices are
  too wide for the DP prediction and are measured by the run itself. Lattices with more than 9 elements, or
  |Mon(L)| > 30,000, are refused (use mcmc).
- Measured on this container's CPU (4 threads, torch 2.14): census C5 (16,818,516 F) in 8.7 s and N5 (31,022,611 F)
  in 15.6 s, ≈ 2·10⁶ F/s; `observe` alone ≈ 2.6·10⁶ F/s. The early exit of the R(F) loop (stop when no F in the
  batch grows) was worth 24×. MCMC: ≈ 5·10⁴ chain-sweeps/s on B4 and 7·10⁴ on E4. On the GPU, throughput is
  bandwidth-bound and the first run prints F/s; C6 (5.5·10¹⁰ F) is the first census where the GPU matters.
- `MORDOR_MEM` (MiB) bounds one working set: census level masks B×|Mon| and observe batches B×n²×(≈24 words).

## 6. Structural axioms (working set): choices and traces

| choice | trace | rejected pattern |
|---|---|---|
| one `observe`, called by both drivers and by the self-test | RSing | separate census/mcmc feature code |
| `Hist` as a monoid with a closed, versioned schema | RS (laws carry resumption), CP | ad hoc dictionaries appended per run |
| `Plan` (static) / `observe` (pure) / driver (Mealy) | CR, CL | scheduling interleaved with the mathematics |
| tripwires = proved theorems, evaluated on every F | CP (error at the point of failure), LC | trusting the engine because tests passed once |
| independent reference by a different method | L2 bisimulation at the strongest observation (the per-F record) | a reference that shares code with the engine |
| overdispersed MCMC starts + census calibration job | L3 made explicit | reporting sampler rates as facts (the log's §23.4 lesson) |
