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

Every satisfying assignment returned by the SAT layer is decoded and re-derived by brute-force fixed-point
computation before it is reported; an unsat answer is only as trustworthy as the solver unless DRAT-checked.
