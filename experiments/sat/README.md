# Round 22 — direct SAT decision of CL

Requirements: Python ≥ 3.10, `pip install python-sat z3-solver`. Optional: `drat-trim`
(https://github.com/marijnheule/drat-trim) for proof checking, passed as `$DRAT_TRIM`.

| Script | What it does | Expected result |
|---|---|---|
| `lat.py` | Lattices, the one-hot CNF of the Realizability Criterion (§24.1) with a, b as variables, a semantic re-checker, `CL_holds` (all intervals, §30.2(i)) | library |
| `crosscheck.py` | Calibration against the log (MacMahon counts, chain-3/4 censuses, 223 = 223, twisted-meet and σ-diagonal controls); CL on 28 lattices incl. E₂–E₅, B₄, C₄×C₄, M₃×M₃; all lattices with ≤ 4 join-irreducibles; DRAT certificates | all "CL holds"; 10 × `s VERIFIED` |
| `semicomm.py` | One-sided hypotheses: b∘a ⊑ a∘b vs a∘b ⊑ b∘a | first ⟹ m = n everywhere; second fails everywhere |
| `cutlemma.py [seconds]` | Cut Lemma on every down-set of every lattice with ≤ 4 join-irreducibles and E₃ (full and cover-only forms), then random 5-generator lattices | full form: 0 counterexamples; cover form: 4,030 / 4,685 |
| `theory_z3.py H poset TIMEOUT [nocomm] [chain]` | The universal theory T_H^≤ of §30.5 | H=2: unsat; H=2 nocomm: sat (4 elements); H=3 chain: unsat; larger H: timeout |
| `ladder_z3.py` | The Ladder Construction (§22.3) over the theory of bounded chains with an escape map | 9 × PROVED; without the escape axiom only the gfp exclusion fails |


Round 23 (`docs/rounds/23-v3.4.md`):

| Script | What it does | Expected result |
|---|---|---|
| `cut_onedim.py` | single row/column infeasibility of the cut | 2,134 of 4,519 instances |
| `cut_mus.py` | minimal contradictory cell sets | sizes 1–34; 3,307 of 4,451 non-local |
| `abstract_pairs.py` | semi-commuting abstract pairs without a principal cut | exist (six-element lattice), also with cross-fix |
| `small_lattices.py` | all lattices ≤ 8 elements, every down-set | 299 lattices, 4,809 instances, 0 counterexamples |
| `hunt.py pi4\|b5\|c3cubed SECONDS` | Cut Lemma on Π₄, B₅ class representatives, C₃³ samples | 0 counterexamples |
| `cut_theory_z3.py H TIMEOUT [chain] [poset]` | universal cut theory C_H | C₁, C₂ unsat; C₃ timeout |
| `seam_search.py` | seam-relaxed near-violators on D_k, E_k | SAT (degenerate dump solutions) |
| `seam_equivariant.py` | the same with translation-equivariance and locality | UNSAT for k = 4..8, seams 1 and 2 |

Every satisfying assignment returned by the SAT layer is decoded and re-derived by brute-force fixed-point
computation before it is reported; an unsat answer is only as trustworthy as the solver unless DRAT-checked.

## Round 26: ground refutation of the cut theory (§34.3g–h)

- `cut_ground.py H [maxterms]`: model-guided ground refutation of `C_H^≤` (poset version) with lazy transitivity and
  a rank encoding of the height bound. UNSAT is a proof. Options of `run`: `wlog=True` (unit F(⊥,⊤) ∉ D, sound by
  order duality, Lean `cut_of_wlog`), `room='fit'` (tightness-guided term selection, §34.3h), `stream=path` (clauses
  to disk instead of memory), `lazy_ih=True` (height-induction clauses on violation) and `ih=True` (with `room='fit'`:
  diagonal candidates F(x,x) carrying the height-induction clauses). Neither induction option helps at H ≤ 5
  (H = 5: 128 → 125 terms), and `cut_lean.py` does not translate them. With
  `run(H, 5000, per_round=1, wlog=True, room='fit')`: H = 3, 4, 5 UNSAT with 7 / 19 / 128 terms (H = 5 in 17 s);
  depth-first selection (§34.3g) needed 35 / 388 terms for H = 3, 4 and did not finish H = 5.
- `run(..., forget=B)` / `run_height.py H cap pr forget=B`: memory bound for the lazily added transitivity clauses, which
  are 81% of the solver's clauses at H = 6, 300 terms (3.5M of 4.3M; eager rank clauses 12%). When more than
  max(B, 2 × last kept) are live, the solver is rebuilt from the other clauses (kept as int32 arrays) plus the
  transitivity clauses whose premises hold in the last model, with that model as initial phases. Sound (every clause is
  an axiom instance); another trajectory. H = 6, one thread each, B = 10⁶: 353 terms at 0.47 GB / 275 s against
  0.82 GB / 454 s without, 403 terms at 0.57 GB with live transitivity clauses staying near 10⁶. H ≤ 5 Cut still
  closes (H = 5 with B = 10³ or 2·10⁴). The trajectory can also get worse: the box Cut theory at H = 4 with B = 10³
  was still SAT past 200 terms (33 without forget; 10⁴ and 10⁵ close it). The old solver is deleted before the new one is
  built. A selector-epoch variant (no rebuild; old epochs disabled by a unit) used more memory, not less (H = 6, 300
  terms: 0.70 / 1.30 GB for B = 10⁶ / 3·10⁵), and was dropped. One external run segfaulted inside CaDiCaL 1.5.3's
  `Internal::propagate()` (located from the dmesg code bytes in the same pysolvers build); not reproduced in three H = 6
  stress runs with 113–234 rebuilds each. A second one (CaDiCaL 1.9.5, 753 terms, 112 rebuilds, 45 min) died in
  `get_model` → `Solver::val`. Under an AddressSanitizer build of pysat's CaDiCaL 1.5.3 and 1.9.5 with CaDiCaL's
  assertions on, about 450 rebuilds at H = 5, 6 showed no memory error; the cause is unknown. Hence the term
  checkpoint (`run(..., ckpt=path)`, written every 25 rounds; `run_height.py` resumes from `cut_H<H>_<tag>.ckpt` when
  rerun) and the option `nophases` (no `set_phases` after a rebuild, the one unusual solver call on that path). Option `cd195` (run_height.py) switches to CaDiCaL 1.9.5; run long jobs under
  `python3 -X faulthandler` so a crash prints the Python stack.
- `rescue_terms.sh PID OUT.ckpt`: copies the term list out of a running `cut_ground`-based process (one started before
  checkpoints existed) into a checkpoint, via gdb: it stops at the next entry to pysat's `solve`, runs a few lines of
  Python there, and detaches; the process keeps running (tested: 0.7 s). Rerun `box_cut.py cut` / `run_height.py` with
  the checkpoint under its expected name (`box_H<H>.ckpt`, `cut_H<H>_<tag>.ckpt`) to resume with new options.
- `cut_ground.fit` scores candidates in chunks of `FIT_CELLS` work cells, which bounds its cand × |F| arrays (about
  9 GB transient at 1500 terms otherwise); the scores, and so the search trajectory, are unchanged.
- `cut_lean.py H core.cnf maps.pkl out.lean`: turns a drat-trim core of an UNSAT run into a Lean file
  (`lean/Mordor/CutHeight<H>.lean`) whose clauses are instances of `lean/Mordor/GroundCut.lean`, refuted by `bv_decide`;
  a WLOG unit becomes `cl_wlog` and the final theorem goes through `cut_of_wlog`.
  To reproduce H = 5: `ok, G = run(5, 5000, per_round=1, wlog=True, room='fit')`, `write_dimacs(G, cnf)`, pickle the
  variable maps (`le`, `d`, `g` inverted, `terms`, `F`), solve with a proof-producing solver (Glucose via PySAT
  `with_proof=True`), `drat-trim cnf drat -c core`, then `cut_lean.py 5 core maps out.lean`.
- `cut_finite.py H n_min n_max [--lattice]`: direct SAT search for a finite cut counterexample (poset of n elements
  numbered by a linear extension, F one-hot, WLOG F(⊥,⊤) ∉ D). None with ≤ 11 elements, at any height (§34.3h).
- `cut_ground2.py H`: fully lazy variant (all axiom families added on violation; height bound as direct chain clauses).
  Reproduces H ≤ 3; superseded by `room='fit'`.
- `box_cut.py` (§34.3z¹⁵): `cells H` restricts the tightness search to box cells F(x, y) with x < y in the current
  model (H = 5: UNSAT with 113 terms in 3 s); `cut H [maxterms] [disk,lazyrank]` is the box Cut theory, no-witness
  only for s < t (UNSAT for H ≤ 4). Memory at H = 5, 300 terms: 1.14 GB default, 0.55 GB with `disk` (clauses
  streamed to `box_H<H>.body`, same trajectory), 0.17 GB and 3× faster with `disk,lazyrank` (chain clauses on
  violation instead of eager rank clauses; another trajectory, not translated by `cut_lean.py`); `finite k` checks the box Cut Lemma on every lattice of closure systems on k points (k = 4: 932 cuts, all
  have a box witness); `minimize H T.pkl` gives a deletion-minimal subterm-closed term set (H = 3, 4, 5: 7, 17, 71).

## Round 26: grid-capture clauses (§34.3z¹¹⁶)

- `grid_ground.py H maxterms per_round J P [seconds]`: `lattice_ground` plus derived clause instances of Lean
  `InfCapture.uncaptured_column_upto` (rows = terms in D, orbits = F-terms, grid columns = meet terms). P instances on
  incomparable D-class pairs per round, or P = −1: one instance on all maximal D-classes (k ≤ 3, N = H). H = 5:
  baseline 147 terms / 4.9 s; P = 1: 321 terms / 24.8 s; P = −1: no result in 590 s. H = 6, P = 1: SAT at 434 terms / 540 s.
- `grid_bite.py H rounds P`: share of live instances already satisfied by a single orbit point (96 % at H = 5, 100 % at H = 6).
- `grid_maxd.py H rounds`: class counts of the partial models (H = 6: |Max D| ≤ 2, |Min Dᶜ| ≤ 3 over 120 rounds).

## Round 26: axis-capture graphs (§34.3z¹¹⁷)

- `axis_capture.py classify | ladder H [jobs] | minh [jobs] | controls`: loopless digraphs with out-degree ≥ 1
  (k = 2: 1, k = 3: 7 up to isomorphism); the cumulative ladder S0–S6 (graph, maximal rows, interior pivot,
  Alternative I, new maximum, its orbit and joins, minimal complement witnesses) on preorder partial models with a rank
  bound; least H with S0–S6 SAT (max Eᵢ + 1 in every case); controls for `no_loop` and `orbit_support_bound`.
  Output `out_axis_capture.txt`.
- `axis_iterate.py k n_max Hmax`: n iterated cycle-to-new-maximum steps; least edge-height 3 for n ≤ 4 (k = 2) and
  n ≤ 3 (k = 3). Output `out_axis_iterate.txt`.

## Round 26: cross cells and the seeded ground search (§34.3z¹¹⁸)

- `cross_cells.py [k2|k3|branch] [graph indices]`: the S0–S6 ladder plus the full cross rectangle F(c, x), F(q, x),
  F(c, ⋁x), F(q, ⋁x), output-branch representatives and (k = 2) the boundary join/meet layer; least edge-height per
  configuration (always max Eᵢ + 1); `branch` forces all q-responses into D or out of D. Output `out_cross_cells.txt`.
- `axis_iterate.py k n Hmax cross`: iterated new maxima with cross-generation cells F(q_s, u_r(1)).
- `seeded_ground.py H maxterms per_round J seed|noseed [seconds] [I|II]`: `lattice_ground` without the WLOG unit, seeded
  with the two-cycle mixed-pivot configuration (constants g₀, g₁, q maximal over all terms). H = 3, 4 UNSAT
  (seeded 17 / 65 terms, branch I 21 / 39, unseeded 13 / 38); H = 5, 6 SAT within 590 s. Output `out_seeded_ground.txt`.

## Round 26: certificate anatomy (§34.3z¹¹⁹)

- `core_anatomy.py LEANFILE`: rows, ⊥-row share, orbit chains, no-witness sides and clause families of the generated
  certificates `lean/Mordor/CutHeight4.lean`, `CutHeight5.lean` (drat-trim cores). Output `out_core_anatomy.txt`
  (H = 5: 84 F-terms over 17 rows, 20 ⊥-row cells, 25 terms on orbits from ⊤).

## Round 26: extremal-separator Skolem constants (§34.3z¹²⁹)

- `sep_ground.py H maxterms per_round J K [seconds] [wlog|nowlog]`: `lattice_ground` plus, for K new cross pairs per
  round, an upper (maximal) and a lower (minimal) separator constant with their extremality clauses over every term.
  Sound but counterproductive: H = 3: 7 → 31–37 terms; H = 4: 20 → 309 terms (K = 2) or SAT at 358 (K = 1);
  H = 5, K = 1: no result in 190 s against 4.1 s. Output `out_sep_ground.txt`.

- `dheight_ground.py H r maxterms per_round J [seconds]` (§34.3z¹⁴³): `lattice_ground` plus "the cut D has height
  ≤ r". UNSAT for H ≤ 5 (r ≤ 3) and H = 6, r = 1 (control); no verdict at H = 6, r = 2 within 2,500 s.
  Output `out_dheight_ground.txt`. Options: `--every N` (progress), `--dimacs OUT.cnf` (write the clause set on UNSAT,
  for `drat_certify.py`), `--stream LOG` (clause log on disk), `--forget B` (bounded live transitivity clauses).
  r = H − 1 is the unrestricted theory (⊤ ∉ D).
