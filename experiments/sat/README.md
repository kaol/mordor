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
  was still SAT past 200 terms (33 without forget; 10⁴ and 10⁵ close it).
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
