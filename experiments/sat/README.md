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
