# Brief, run 15 (adjoint-math-research v1.0, frontier-only, no seed): one fixed atom

Status of everything below: **briefer's, unverified until the worker re-runs it in an independent encoding.** "Paper"
means a proof written here, not checked in Lean.

## Repository, pinned commit

- /home/user/mordor at `37c3c50c9584c0db6a20cc34d09662560d875be7`. It was read-only throughout: no file under it was
  created, edited or deleted.
- Read at source:
  - docs/rounds/26-v3.7.md §34.3z²⁸²–²⁸⁴;
  - lean/Mordor/LateParent.lean, section `Landing` (lines 5452–5836) and the definitions it uses;
  - experiments/amalgamation/{bank.py, orbit_probe.py, tight_probe.py (`lattices`)} and brief282/toplayer{,2,3}.py;
  - the run-13 ctlA encoding `w0lean.py`, from the scratchpad.
- All files of this brief are in
  /tmp/claude-0/-home-user/3b6fdd2c-c95c-5c07-b47c-6ae28c687a4c/scratchpad/amr_run15/brief/:
  - `brief.md`;
  - the tester `probe15.py`, with its copied dependency `w0lean.py` (run-13 ctlA, unchanged);
  - the bank-replay driver `bankx.py` and its predicate files `cands.py`, `cands2.py`;
  - diagnostics `diag2.py`–`diag4.py` and `insp.py`, on stored models only;
  - the run outputs `run1`–`run6_*.txt`;
  - every SAT model, as `m15_*.json` (see "Banked candidates").

## Failure signature (recomputed)

Every refuted route **predicts which row certifies**, in one of three ways:
- by a walk from ⊥ (the BotOrbit family);
- by an extremal index (MaxIdx, MaxIdx2);
- for every member of a family (ExitDom, TopAbsorb, GoodFix, OneGood, and this round's GoodToFix).

None of them argues about the *set* of certificates as a whole.

## Mission

Prove that the set of μ-fixed atoms is nonempty by an argument about the whole set — its size is exactly one — and
never by naming in advance the row that certifies.

## Frontier

**Definitions (as in source).**
- F : L → L → L is monotone in both arguments, L finite, h = `height H`.
- a(x) = gfp F(x,·) (`a`, Derived.lean); b(y) = lfp F(·,y) (`b`, Derived.lean).
- R_k is `Rk` (Orbit.lean).
- World **W0 ∧ n1**: a(⊥) = ⊥; h ≤ 2 on R_2; ⊤ ∉ R_2; R_1 not tight. Then R_1 = Z = {y : F(⊥,y) = ⊥}, and Z has heights
  ≤ 2. This is the hypothesis block of `GoodAtom1`, `Cert1` and `OwnCell1`.
- High = height ≥ 3. (T): no x ∈ Z has, at a high column y, a lower cell F(x,y) ≤ x (Tb) or an upper cell y ≤ F(x,y) (Ta).
- t_j = (F⊥)^j ⊤; d = its last nonzero element; N = the index of d.
- λ(x) = the first element of height ≤ 2 on row x's descent from ⊤, at index i(x).
- x exits iff λ(x) ∉ Z. Then c(x) = F(⊥,λ(x)) is an atom of Z (`exit_atom`).
- μ(x) = λ(x) if λ(x) ∈ Z, else c(x). A μ-fixed atom q: λ(q) ∉ Z and F(⊥,λ(q)) = q.
- IsGood p ⟺ p ≤ a(p) ∨ ∃ i, (F p)^i ⊤ = p (LateParent.lean:4709).
- M2 = {m ∈ Z : h(m) = 2}.
- Branches: a (h(d) = 2), b (d a bad atom), g (d a good atom).

**Open target (as commissioned): TopExit.** Off g, some m ∈ M2 exits with c(m) ≤ m. The audit below finds it to be
TopCert itself. The actual open programme target is `GoodAtom1`.

**Established results used** (all checked in source, section `Landing` unless noted):
- descents and landings: `land_not_le`, `land_bot_lt`, `exit_atom`, `land_unique`;
- certificates and goodness: `cert_of_exitFixed`, `goodAtom_of_exitFixed`, `goodAtom_of_inCert`, `domCoLand`,
  `trap_of_tb`, `tb_of_tight`, `exitFixed_of_dom`, `upTrap_stay`, `upTrap_land`, `goodAtom_of_greatestZ`;
- the top layer: `land_of_good_below`, `good_atom_unique_below` (Lemma U), `topCell_iff_goodBelow` (Lemma T),
  `certAt_of_fixed_below` (Lemma D), `fixedBelow_of_exitDom`;
- elsewhere: `ownCell_of_good`, `good_of_dominating_desc(_bot)`, `goodAtom1_iff_ownCell1`, `goodAtom1_of_cert1`.

## Ladder audit

Each live rung is re-derived from its lemmas. Then TopCert, NMGood, ExitM2 and FixBelow are tested for equivalence with
the target and with each other.

**A1. TopExit ≡ TopCert ≡ FixBelow** (definition; Lean).
- TopExit says "some m ∈ M2 exits to an atom below m".
- TopCert says "some m ∈ M2 exits with c(m) ≤ m".
- These are the same sentence: c(m) is automatically an atom (`exit_atom`).
- FixBelow ⟺ TopCert holds row by row (`fixedBelow_of_exitDom`, `certAt_of_fixed_below`).
- So the frontier's "provisional rung TopCert" and its "open step TopExit" are **one statement**. TopCert's evidence is
  evidence for the target, not for a rung. *Disguised target.*

**A2. TopExit lies above Cert1** (the definition of Cert1 in LateParent.lean:5258, with x = m).
- TopExit is therefore no reduction of GoodAtom1 below Cert1: it is Cert1 plus a placement condition.
- The weakest rung on file that gives GoodAtom1 off g is NMGood.

**A3. NMGood ⟹ ExitM2** (paper; new). Lemma **GoodUp**: let q be a good atom of Z, m ∈ Z with q ≤ m, and h(⊤) > 2.
Then m lands at λ(q), λ(q) has height 2 and λ(q) ∉ Z, so m exits to c(q).
- *Proof.* `land_of_good_below` gives a height-2 p on q's descent, with q ≤ F(q,p) and q ≤ p, and makes p the landing of
  every row of R_1 above q.
- Suppose p ∈ Z (F(⊥,p) = ⊥). Then p ∈ R_1 (`mem_succ_of_cell` at ⊥, or Z ⊆ R_1).
- `land_of_good_below` at row p makes p's landing the height-2 element of q's descent, which is p itself: two height-2
  elements of one descending chain are equal (`eq_of_le_of_height_ge`).
- This contradicts `land_not_le` at row p. ∎
- Bank replay: passes on 26 of 26 models (`GoodExitUp` in `bankx.py`).
- Ladder: TopExit ⟹ NMGood ⟹ ExitM2. All three were "provisional with the same evidence"; only TopExit is the target.

**A4. A non-fixed good atom sits in the upper cell** (paper). If q is good and not μ-fixed, then F(q,λ(q)) = λ(q) = a(q),
and λ(q) = q ⊔ c(q).
- *Proof.* q ≤ F(q,p) ≤ p with p = λ(q) of height 2, so F(q,p) ∈ {q, p}.
- If F(q,p) = q: F(⊥,p) ≤ q, and F(⊥,p) ≠ ⊥ (A3), so F(⊥,p) = q and q is fixed.
- Hence F(q,p) = p. ∎
- Bank replay: 26 of 26 (`NonFixGoodUpper`).

**A5. Ta ⟺ landing** (paper, two lines: `row_a`, `le_a`).
- Ta at row x ⟺ h(a(x)) ≤ 2 ⟺ row x lands. This is because a(x) is the largest post-fixed point of F(x,·).
- Consequence: §34.3z²⁸³'s "Ta matters only through landing" and the design rule's Ta clause are tautologies.
- Every "`land`" relaxation there (TbOnly+land, Tb1+land, Tb2+land) *is* the full world (T) at those rows.
- The role analysis's real content is only: Tb is needed at the atom rows and at the height-2 rows.

**A6. Tb is the b-side** (paper: `b_le`, `(col F y).map_lfp`, `Rk_down`).
- Tb at every row of Z ⟺ b(y) ∉ Z for every high y.
- Tb at ⊥ and at every atom row ⟺ for every high y, b(y) is neither ⊥ nor an atom of Z. Because b(y) is the least
  pre-fixed point of F(·,y), q pre-fixed ⟹ b(y) ≤ q.
- So the set-aside "column ascents" have been used all along, inside `trap_of_tb` and `tb_of_tight`, just never in lfp
  form.

**A7. Landing index is monotone on Z** (paper: `iter_row_mono` and height monotone).
- x ≤ y in Z ⟹ i(x) ≤ i(y), and at equal index λ(x) ≤ λ(y).
- Bank: 26 of 26 (`LandIdxMono`).

**A8. Predecessor dichotomy** (paper).
- Let p = λ(x) ∉ Z with predecessor s on row x's descent. Then F(⊥,s) ∈ {c(x), p}: c(x) = F(⊥,p) ≤ F(⊥,s) ≤ F(x,s) = p,
  and c(x) is an atom.
- Bank: always c(x) (`diag3.py`). Whether F(⊥,s) = p can occur is open.

**A9. Fixed-atom forms** (paper).
- **fixed(q) ⟺ q ≤ F(⊥, λ(q))**. This mirrors the own-cell form good(q) ⟺ q ≤ F(q, λ(q)) (`goodAtom1_iff_ownCell1`).
- **BotBelowFix**: if q is μ-fixed with landing index i, then t_{i+1} ∈ {⊥, q}, and t_{i+1} = q iff q = d (so branch g).
  *Proof:* t_{i+1} = F(⊥,t_i) ≤ F(⊥,(Fq)^i ⊤) = F(⊥,λ(q)) = q.
- Off g, therefore, N ≤ i(q) for every μ-fixed q.
- Bank: both 26 of 26 (`FixIff`, `BotBelowFix`).

**A10. Search-tested equivalences** (probes below).
- **FixMax** (off g, every μ-fixed atom lies below M2) is provisional. With it, off g, TopExit ⟺ CertAtom ⟺ Cert1
  (`fixedBelow_of_exitDom`, `certAt_of_fixed_below`, `exitFixed_of_dom`). The top-layer restriction then costs nothing,
  and TopExit is exactly as hard as Cert1.
- **GoodToFix** (every good atom is μ-fixed or exits to a μ-fixed atom) is **refuted** at h10, |L| = 34, on branches a, b
  and g:
  - a maximal good atom exits to a non-fixed atom;
  - so NMGood ⟺ Cert1 does not follow this way;
  - and GoodAtom1 ⟹ CertAtom stays open.

**Placement summary (off g).**
- TopExit = TopCert = FixBelow ⟹ NMGood ⟹ ExitM2.
- TopExit ⟹ Cert1 ⟺ CertAtom ⟹ GoodAtom1; and NMGood ⟹ GoodAtom1.
- With FixMax: CertAtom ⟹ TopExit, so TopExit ⟺ Cert1.

## Reuse (real names, files)

**LateParent.lean, section `Landing`:**
- descents and landings: `land_index_pos`, `land_not_le`, `land_bot_lt`, `exit_atom`, `land_unique`;
- fixed and dominated exits: `cert_of_exitFixed`, `goodAtom_of_exitFixed`, `goodAtom_of_inCert`, `coland_of_stall`,
  `trap_of_tb`, `domCoLand`, `tb_of_tight`, `exitFixed_of_dom`;
- traps and breaks: `upTrap_stay`, `upTrap_land`, `break_in_Z`, `breakExists`, `goodAtom_of_greatestZ`;
- the top layer: `land_of_good_below`, `good_atom_unique_below`, `topCell_iff_goodBelow`, `certAt_of_fixed_below`,
  `fixedBelow_of_exitDom`.

**LateParent.lean, elsewhere:**
- `IsGood` (4709), `GoodAtom1` (5045), `Cert1` (5258), `goodAtom1_of_cert1` (5264), `OwnCell1` (5413),
  `goodAtom1_iff_ownCell1` (5418);
- `good_of_dominating_desc` (5182), `good_of_dominating_desc_bot` (5188), `iter_row_mono` (5194);
- `a_le_rowDesc` (5364), `rowDesc_reaches_a` (5372), `ownCell_of_good` (5377), `rowIter_succ_le` (3891),
  `eq_of_le_of_height_ge` (4092).

**Other files:**
- Derived.lean: `a`, `b`, `row_a`, `le_a`, `b_le`.
- TightTransfer.lean: `b_le_of_lower`.
- GapPotential.lean: `height_strictMono`.
- OrbitHeight.lean: `mem_succ_of_cell`.
- ParentAncestry.lean: `aIter_mem`.
- Orbit.lean: `Rk`, `Rk_down`.

## Lead programme: OneFix — exactly one μ-fixed atom

- **Candidate (conjectural).** In W0 ∧ n1 with h(⊤) ≥ 3, on every branch, *exactly one* atom q of Z is μ-fixed: λ(q) has
  height 2 and F(⊥, λ(q)) = q, equivalently q ≤ F(⊥, λ(q)) (A9). It splits into two halves:
  - **AtMost1Fix** (uniqueness): two μ-fixed atoms are equal.
  - **Existence** = CertAtom ⟺ Cert1 (the old core).
- **Conditional payoff (proof).**
  1. Existence ⟹ GoodAtom1, by `goodAtom_of_exitFixed`.
  2. Existence ∧ FixMax ⟹ TopExit off g: the fixed atom q lies below some m ∈ M2, and `certAt_of_fixed_below` makes m
     exit to q ≤ m.
  3. AtMost1Fix alone ⟹ every Cert1 witness of Z exits to the same atom q*. `exitFixed_of_dom` makes each dominated exit
     atom fixed, and AtMost1Fix identifies them. Every row of Z above q* exits to q* (Lemma D).
  4. So AtMost1Fix globalizes Lemma U for fixed atoms. OneGood, its "every good atom" relative, is refuted (two good
     atoms occur; GoodToFix shows a second good atom need not even point at q*).
- **Placement.**
  - AtMost1Fix is a new rung, beside `good_atom_unique_below`. It neither implies nor needs any rung of the ladder.
  - OneFix ⟹ CertAtom ⟺ Cert1 ⟹ GoodAtom1.
  - OneFix ∧ FixMax ⟹ TopExit (off g).
  - Nothing on file implies OneFix.
- **Testability.** Finitely refutable; a level-1 stage form.
- **Hypothesis world.** Every branch has models in every corpus used. Unlike TopExit, OneFix holds on branch g too
  (there the fixed atom is d).
- **Counterexample anatomy.**
  - Against uniqueness: two μ-fixed atoms q1 ≠ q2, with landings p1 ≠ p2 of height 2 outside Z.
  - No row of Z lies above both (Lemma U), so q1 ⊔ q2 ∉ Z.
  - BotBelowFix makes N ≤ min i(q_k) off g.
  - That needs |A| ≥ 2, two height-2 descent elements outside Z, and two descents of length ≥ 2 through different high
    columns. Smallest hosting coordinates are not known.
  - Against existence: a Cert1 counterexample; anatomy unknown.
- **Room reached** (height, generator M, largest antichain, N):
  - height 10, 12 and 13;
  - M = 4 and 6;
  - largest antichain up to 13 (the bank reaches 11);
  - N ≥ 5 imposed, with models at N up to 9;
  - |A| up to 8, |M2| up to 9.
- **Mode.** Signature inversion: a statement about the size of the certificate set, not a predicted row.
- **Limit.** OneFix names no row. Its existence half *is* CertAtom; only the uniqueness half is new content.
- **Decisive open step: "count-to-existence".** Prove AtMost1Fix (Lean), then derive existence from a global invariant of
  the fixed-atom set rather than from a construction of its member. Two concrete mechanisms are left for the worker:
  - (i) a parity argument. OddFix held wherever OneFix did, in the bank; the search tested OneFix only.
  - (ii) a deformation argument: |Fix| is constant under a one-cell change of F inside W0, and is 1 on a base F.
- **Partial tools.** A9's BotBelowFix is a partial tool for uniqueness: at most one fixed atom equals d, and the others
  have landing index ≥ N. How the two fixed atoms' rows interact is the missing part.

## Other programmes

### P2 (ladder audit): FixMax — the fixed atom is never maximal in Z off g

- **Candidate (conjectural).** Off g, every μ-fixed atom of Z lies below some m ∈ M2.
- **Payoff.** Off g, CertAtom ⟹ FixBelow ⟹ TopExit (`certAt_of_fixed_below`). So TopExit ⟺ Cert1, and the top-layer
  programme collapses onto Cert1.
- **Placement.** Universal over fixed atoms. Under OneFix it is a statement about one atom.
- **Testability.** Finitely refutable.
- **Hypothesis world.** Branches a and b.
- **Sharpness.** It fails on g: the stored models `m15_main_tall_10_4_2_8_g_MGoodFix_min22.json` and `_g_MOneGood_min22`
  have fixed atom d, maximal in Z.
- **Mutant** (nearest refuted relative): M:GoodNonMax, "every good atom lies below M2". It is refuted in the bank
  (s282_goodfix, s282_onegood) and by search on every corpus below.
- **Anatomy.** A fixed atom q ≠ d with no element of M2 above it, while M2 ≠ ∅.
- **Mode.** Ladder audit (equivalence test).
- **Limit.** Even when proved, FixMax says that TopExit is no easier than Cert1. That is a negative placement result.
- **Open step.** A direct proof, plausibly from BotBelowFix (N ≤ i(q)) and `upTrap_land`.

### P3 (set-aside reversal, the b-side): DescTb2 — at height-2 rows only λ(m) ≰ m is needed; at atom rows the column form is

- **Candidate (conjectural).** TopExit holds in the world **desc2**: W0 ∧ n1 with Tb at the height-2 rows of Z weakened to
  its descent form. That is, F(m,t) ≰ m only for high t on m's own descent, which is λ(m) ≰ m.
  - Ta (= landing, A5) is kept at every row.
  - Tb in full is kept at ⊥ and at the atoms: by A6, b(y) ∉ {⊥} ∪ A for every high y.
- **Payoff.** desc2 ⊇ W0, so DescTb2 ⟹ TopExit. A proof then needs, at height-2 rows, only `land_not_le`.
- **Companion result (exact, refuted).** **DescTb12**, the same weakening also at the atom rows, makes TopExit **fail**:
  - on every lattice of every corpus, branches a and b;
  - smallest |L| = 22 at h10;
  - its NOV column (the weakening is really used) is SAT.
  So the off-descent column condition at atom rows — the b-side, as `trap_of_tb` uses it at columns r ⊓ s_j — is
  genuinely needed.
- **Placement.** A strengthening of TopExit by weakening hypotheses.
- **Hypothesis world.** desc2 has models in which an M2 row has a high lower cell:
  - NOV SAT on branch a on every lattice of R2–R6 (R5 ran before the NOV column existed);
  - NOV SAT on branch b on most lattices; NOV UNSAT on 4 of 8 at `tall 10 4 2 8` and 2 of 5 at N ≥ 5, where those
    lattices are silent.
- **Mutant** (nearest refuted relative): TopExit in noTb2, §34.3z²⁸³'s Ta2+land, refuted there at h10 20/20. It fails on
  every lattice here.
- **Mode.** Set-aside reversal. The old objection ("no recorded reason") does not apply: A6 shows Tb *is* the lfp
  condition.
- **Limit.** A design rule, not a proof.
- **Open step.** Restate `trap_of_tb`'s hypothesis hTb as "b(y) ∉ {⊥} ∪ A for high y". Then check that the TopExit or
  Cert1 argument uses the height-2 rows only through `land_not_le`.

### Refuted this round: GoodToFix

Every good atom is μ-fixed or exits to a μ-fixed atom. It passed the bank (26 of 26) and was refuted by search on every
corpus:
- smallest |L| = 34, H = 10, largest antichain 9, branches a (N = 2), b (N = 3) and g;
- model `m15_main_tall_10_4_2_8_a_GoodToFix_min34.json`.

In that model the fixed atom is 5 (below M2), and the good atom 2 is maximal in Z. Atom 2 exits through λ = 8 to atom 4,
and atom 4 steps into Z at 11. The relative M:GoodFix fails on the same lattices.

## Probe scripts

**Tester: `probe15.py`** (pysat Cadical153; one solver per lattice; branch and world by assumptions).

*Encoding in words.*
- Rows F(x,·) exist only for low x (h ≤ 2). They are one-hot and monotone in x (covers inside the low set) and in y.
- Z(y) = [F(⊥,y) = ⊥]; a(⊥) = ⊥; n1.
- Ta at every row of Z and Tb at ⊥ are always on. Tb at the atom rows and at the height-2 rows sit behind selectors, in
  full or descent form, so one solver serves the worlds full, desc2, noTb2, desc12 and noTb1.
- Exact descents it(x,j,·) from ⊤ up to index h(⊤). Landing = the first low element. Every row of Z lands; Ta implies
  this, so the clause is harmless.
- ext(x,c), fixq(q) = Z(q) ∧ ext(q,q), good(q) = q on its descent ∨ q ≤ the index-h(⊤) element (= a(q)).
- d comes from the exact ⊥-descent. The branches are a = h(d) = 2, b = ¬a ∧ d bad, g = d good.
- `Nmin=K` asserts t_K ≠ ⊥. `maxn` skips large lattices, and each skip is printed. `budget` sets a per-solve conflict
  limit; an exhausted budget prints `undec`, which is **silent, never UNSAT**.
- Every SAT model is decoded (rows of non-low elements set to ⊤) and replayed in Python from the definitions before it is
  counted:
  - full world: `rstages.stages`, and the W0 ∧ n1 check including R_1 = Z;
  - relaxed worlds: `replay_world`, plus NOV and the statement.

*Self-check (no search).* `python3 probe15.py selfcheck` pins F to each banked W0 model and compares every query with its
Python replay. Result: 26 models, 0 mismatches.

*Quantifier, printed by the tester.* Per lattice and branch, over all F: a column is SAT iff some F makes the named
statement FAIL; vac is SAT iff the branch has a model.

*Runs.* The budget was 5 exact runs. R1 hit the 40-CPU-minute cap and is returned; R2–R6 count.

| run | invocation | corpus reached |
|---|---|---|
| R5 | `bside tall 10 4 2 20` | 20 lattices, h10, M4, \|L\| 22–50, antichain 5–12 |
| R2 | `main tall 10 4 2 8 B=1 budget=400000` | 8, h10, M4, \|L\| 22–44, antichain 5–10 |
| R1 | `main tall 12 4 1 8` (no budget) | **stopped at the CPU cap** in lattice 5; lattices 0–4 (\|L\| 32–52, antichain 7–9) completed; *returned, reported as partial* |
| R3 | `main tall 13 4 1 8 maxn=46 B=1 budget=400000` | 6, h13, M4, \|L\| 33–46, antichain 6–9 (lattice 0, \|L\| 58, skipped) |
| R4 | `main tall 10 6 1 8 maxn=51 B=1 budget=400000` | 4, h10, M6, \|L\| 35–51, antichain 8–13 (\|L\| 54, 59, 66, 54 skipped) |
| R6 | `main tall 12 4 1 8 maxn=46 Nmin=5 B=1 budget=400000` | 5, h12, M4, N ≥ 5 (models at N 5–9), \|L\| 27–45, antichain 6–9 |

Its `m15_main_tall_12_4_1_8_*` model files are R6's (N ≥ 5); R1 wrote none.

*Bank replays* (free; `bankx.py --file cands.py | cands2.py`): OneFix, AtMost1Fix, OddFix, FixIff and BotBelowFix 26/26;
FixMax 23/23 off g; GoodToFix 26/26; M:OneGood and M:GoodFix fail on 2 (s282); M:GoodNonMax fails on 2 (s282); M:MaxIdx2
fails on 3. TopExit, FixBelow, NMGood and ExitM2 pass on 23 of 23 at 37c3c50.

**Report lines.** Each cell is UNSAT (decided) / undec, then the mutant's failures, out of the lattices with models.

```
OneFix (exactly one mu-fixed atom) | exact | per lattice/branch over all F; SAT = count of mu-fixed atoms != 1
  room: h10/12/13, M4/6, antichain <=13, N>=5 (to 9) | anatomy needs: |A|>=2, two height-2 descent columns outside Z
  R2 h10M4:  a 8/0  b 4/0  g 7/1  | M:OneGood fails a8 b2 g8
  R1 h12M4 (partial, capped): a 5  b 4  g 5 | M:OneGood a4 b3 g4
  R3 h13M4:  a 4/2  b 6/0  g 6/0  | M:OneGood a6 b4 g6
  R4 h10M6:  a 2/2  b 3/1  g 3/1  | M:OneGood a4 b4 g4
  R6 h12 N>=5: a 4/1 b 2/1 g 4/1  | M:OneGood a3 b2 g3
  -> provisional on a, b, g (undec instances silent)
AtMost1Fix | exact | SAT = two distinct mu-fixed atoms
  UNSAT on every decided instance: R2 8/4/8, R1 5/4/5, R3 6/6/6, R4 3(+1 undec)/4/4, R6 5/3/5 | mutant M:OneGood as above
  -> provisional on a, b, g
FixMax | exact | SAT = off g, some mu-fixed atom lies below no m in M2
  R2 a8 b4; R1 a5 b4; R3 a6 b6; R4 a3(+1 undec) b4; R6 a5 b3: all UNSAT | M:GoodNonMax fails R2 a8 b2, R1 a4 b3,
  R3 a6 b4, R4 a4 b4, R6 a3 b2 | sharpness: fails on g (stored g models)
  -> provisional on a, b
GoodToFix | exact | SAT = some good atom is neither fixed nor exits to a fixed atom
  SAT: R2 2/2/2, R1 3/3/3, R3 3/3/3, R4 4/4/4, R6 1/1/1 -> refuted (smallest |L| 34, h10)
TopExit (the target; pushes owed for TopCert) | exact | SAT = off g, no m in M2 exits with c(m) <= m
  R2 a8 b4; R1 a5 b4; R3 a6 b6; R4 a3(+1 undec) b4; R6 a5 b3: all UNSAT
  | M:MaxIdx2 fails R2 a5 b3, R1 a3 b3, R3 a5 b5, R4 a4 b4, R6 a3 b2
  -> calibrated-mutant pushes at h13 and at M6 done, N pushed to >= 5 (one encoding)
DescTb2 (TopExit in desc2) | exact | SAT = TopExit fails in desc2; NOV SAT = desc2 really relaxes
  R5 a19 b12 UNSAT; R2 a8 b8; R3 a6 b6; R4 a4 b4; R6 a5 b5 UNSAT
  | NOV a all; b R2 4/8, R3 6/6, R4 4/4, R6 3/5 | mutant noTb2 fails everywhere (R5 20/20 each branch)
  -> provisional on a; on b provisional where NOV is SAT
DescTb12 (TopExit in desc12) | exact | SAT = TopExit fails -> refuted (fails on every lattice, a and b; |L| 22, h10)
```

## Pushes owed

- **OneFix / AtMost1Fix:**
  - a second encoding;
  - resolve the undec instances (R3 a 2, R4 a 2 b 1 g 1, R6 one per branch) with a larger budget;
  - h14; M7 or the skipped wide lattices (|L| 54–66 of `tall 10 6 1 8`); N ≥ 6;
  - closure corpora.
- **FixMax:** the same, plus R4's undec instance.
- **DescTb2:** a second encoding; branch b on lattices where NOV is SAT; h14, M7, N ≥ 6.
- **TopExit (TopCert):** a second encoding of the h13, M6 and N ≥ 5 mutant pushes done here.

## Banked candidates (for the worker to add to experiments/amalgamation/bank/ after re-checking)

- GoodToFix:
  - `m15_main_tall_10_4_2_8_{a,b,g}_GoodToFix_min34.json` (h10, |L| 34, largest antichain 9, N 2 / 3 / 2);
  - larger instances in `m15_main_tall_13_4_1_8_*_GoodToFix_min42.json` and `m15_main_tall_10_6_1_8_*_GoodToFix_min35.json`.
- DescTb12 (TopExit in desc12): `m15_main_tall_10_4_2_8_{a,b}_desc12_TopExit_min22.json` (relaxed world).
- The noTb1 and noTb2 TopExit models are relaxed-world relatives.

## Already failed (do not repeat)

- **Anchored at ⊥ or a walk from it:**
  - BreakCert, OrbitDom, JoinCert, Orbit3/4, BotOrbit (the ⊥-orbit cycles at |L| 59), StrictDep, ExactDrop;
  - ChainT1, ChainDom′, ChainDom, L2;
  - the run-13 set: BreakFix, BreakTrap, MaxExitFix, MaxIdx, AtomOrb, LateCert, LinkFix.
- **Universal over a family:**
  - ExitDom, QEany, ExitCert, ExitCoLand, ExitGood, MuLoop, DropProp(′);
  - TopAbsorb, GoodFix, OneGood, **GoodToFix** (this round).
- **Extremal choice:** MaxIdx2.
- **Tightness-free descent statements:** ExitBelow, PredBelow, LandBelow, InStepUp, BreakDom.
- **Relaxed worlds:**
  - noTb2 and noTb1 (§34.3z²⁸³ and here);
  - **desc12** (this round): Tb at atoms in descent form only.

## Hard constraints

- **Sharpness:**
  - TopExit, NMGood and FixMax fail on branch g (the fixed or good atom is d, maximal in Z);
  - OneFix and AtMost1Fix do **not** need "off g";
  - everything fails without R_2 tightness.
- **Design rule, sharpened (provisional):**
  - Ta = landing (A5), so it is a single hypothesis, h(a(x)) ≤ 2 on Z.
  - At height-2 rows a proof of TopExit should need Tb only as λ(m) ≰ m (DescTb2).
  - At atom rows it needs Tb off the atom's own descent (DescTb12 refuted). By A6 that is the column condition
    b(y) ∉ {⊥} ∪ A for high y.
- **Lemmas are stage forms at level 1:** every statement here is finitely refutable.

## Formalization order (Lean, section `Landing`, no `sorry`, no new axioms; names are proposals)

1. `ta_iff_land` : (∀ y, 2 < height H y → ¬ y ≤ F x y) ↔ height H (a F x) ≤ 2 (`row_a`, `le_a`, `height_strictMono`).
2. `tb_iff_b_notin` : (∀ q ∈ Rk F 1, ∀ y, 2 < height H y → ¬ F q y ≤ q) ↔ ∀ y, 2 < height H y → b F y ∉ Rk F 1. Also its
   atom form: b F y is neither ⊥ nor an atom of R_1.
3. `landIdx_mono` (A7).
4. `goodUp` (A3), giving `exitM2_of_nmGood`.
5. `nonfixed_good_upper` (A4).
6. `fixed_iff_le_bot_land` (A9).
7. `botDesc_le_fixed` (BotBelowFix, A9).
8. `predStep` (A8).
9. Then AtMost1Fix, attempted directly, and FixMax.

## Expected report

One verdict per programme, in §6's taxonomy, each with its ladder update:

| programme | expected verdict |
|---|---|
| Ladder audit A1–A9 | `normal form` / Lean lemmas; A1 removes TopCert as a separate rung |
| OneFix, split | AtMost1Fix (`new conjecture` if pushed, or Lean); existence = Cert1 |
| FixMax | `conditional lemma` or `refuted`; if it holds, the ladder records TopExit ⟺ Cert1 off g |
| DescTb2 | `provisional` → `normal form` of the hypothesis set |
| DescTb12, GoodToFix | `refuted` (bank them) |

## Frontier corrections

1. **TopExit and TopCert are the same statement** (and ⟺ FixBelow, in Lean). Remove one of the two from the ladder; the
   "provisional rung" is the target.
2. **TopExit ⟹ Cert1.** The open step sits above Cert1, so it is not a reduction of GoodAtom1 beyond Cert1. NMGood is the
   weakest off-g rung that gives GoodAtom1.
3. **Add NMGood ⟹ ExitM2** (A3, paper), with GoodUp: every good atom exits, and all rows of Z above it land at its
   landing.
4. **Ta at a row ⟺ the row lands** (A5). §7's design-rule clause "Ta only to land the rows of Z" is vacuous, and §283's
   "TbOnly + land", "Tb1 + land" and "Tb2 + land" are the full world, not relaxations.
5. **§8, set-aside b-side:** Tb *is* the column (lfp) condition (A6), already used through `trap_of_tb` and `tb_of_tight`.
   DescTb12's refutation shows the column condition at atom rows is needed. DescTb2 suggests it is not needed at
   height-2 rows beyond `land_not_le`.
6. **§5:** the replay results quoted "at 1c68a4e" reproduce at 37c3c50.
7. **§6 room vector:** every banked branch-a model has N = 1. Width (largest antichain) now reaches 13 (R4). N ≥ 5 with
   models up to N = 9 is reached (R6). The tester `orbit_probe.py` modes are slow; `probe15.py` with `budget` and `maxn`
   prints per-solve progress.
8. **§4:** add GoodToFix (refuted, |L| 34, h10) and DescTb12 (refuted, relaxed world, |L| 22, h10) to the refuted
   routes. The failure signature now includes GoodToFix among the universal routes.
9. **§2:** the TopCert pushes owed were partly paid in one encoding: the calibrated mutant MaxIdx2 fails at h13 and at
   M6; N was pushed to ≥ 5. A second encoding is still owed.
10. **§7 role analysis (samples):** "exactly one μ-fixed atom below M2" was recorded as a sample. Exact search now
    supports the stronger *global* OneFix on all branches, g included.
