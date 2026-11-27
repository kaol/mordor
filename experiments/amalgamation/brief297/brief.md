# Brief, run 22: outside briefer (adjoint-math-research v1.0)

**Repository:** /home/user/mordor at **833f066**. I treated it as read-only. Nothing in the checkout was written, built
or changed, and the only git command I ran was `git log --oneline -3`. Lean work happened in a scratch copy:
`leanw/`, copied from the session's `leanw` with the repository's current `StairB1.lean` and `PairTrap.lean`.

**Work directory** (everything below lives here):
`/tmp/claude-0/-home-user/3b6fdd2c-c95c-5c07-b47c-6ae28c687a4c/scratchpad/amr_run22/brief/`
- `TwoColour.lean` is the new Lean file. It is also at `leanw/Mordor/TwoColour.lean`, and its axiom check is in
  `lean_twocolour_axioms_out.txt`.
- `open_probe.py` is the tester for runs 1 to 5. It is a patched copy of the repository's `orbit_probe.py` (§9).
- `run1/` … `run5/` hold each run's `runK.sh`, outputs, `*_wall.txt` and a JSON dump of every SAT model.
- The free analyses are `*.py`, with outputs in `*_out.txt`.
- Refuting models are in `cex/` (JSON with source, statement refuted and coordinates).

**Checked at source:**
- `PairTrap.lean`, all of it: `pairStair`, `certAtom_of_N1_all`, `certAtom_of_topRow`, `certAtom_of_topRow'`,
  `colourGain`, `certAtom_N1`, `certAtom_of_boundedAtoms`.
- `StairB1.lean`: `exists_first_low` and the header.
- `Normalize.lean`: `CertAtom`, `mem_one_iff`.
- `LateParent.lean`, section `Landing`: `land_index_pos`, `land_not_le`, `land_bot_lt`, `exit_atom`, `land_unique`,
  `cert_of_exitFixed`, `trap_of_tb`, `domCoLand`, `tb_of_tight`, `exitFixed_of_dom`, `upTrap_stay`, `upTrap_land`,
  `ta_iff_lands`. Also `iter_antitone_of_le` and `eq_of_le_of_height_ge`.
- The log `docs/rounds/26-v3.7.md`, §34.3z²⁹³–²⁹⁶.
- `experiments/amalgamation/brief295/brief.md`, in full.
- `orbit_probe.py` (all of it), `jstuck296.py`, `bank.py` (the model API) and `brief291/world.py`.

**Mission (the negation of the failure signature).** Every refuted route either picks the row that certifies, or
relaxes what a landing-preserving deformation restores. This brief takes neither path.
- It keeps every certificate implicit and works in contradiction mode only.
- It asks which W0 consequences are already inconsistent with "no fixed atom".
- It answers with a world that contains **no Tb at all**. Only the two colour rows and row ⊥ are constrained there,
  and the hypotheses are exactly the theorems `colourGain`, `ta_iff_lands`, `land_not_le` and `exitFixed_of_dom`.

---

## 0. Summary

1. **Lead: ColourGain at the two colour rows already rules out NoFix (provisional; room reached in every dimension the corpora allow).**
   - **World R3.** It keeps a(⊥) = ⊥, ZT, n1, h(⊤) ≥ 3 and (T) at ⊥. At the **two colour rows only** it adds:
     - Ta (the row lands);
     - `land_not_le`;
     - no dominated exit;
     - ColourGain (λ(a) ≥ b and λ(b) ≥ a).

     Every other row of Z is left free, constrained only by monotonicity. Tb is gone at every row except ⊥.
   - **Result.** R3 ∧ NoFix ∧ (𝒜 = {a, b} unbounded in Z) has no model on 161 lattices (runs 4–5): H 4–14, width M up to
     7, exact N 3–6, |L| up to 45.
   - **Mutant.** CGone keeps ColourGain at one colour row only. It has models on 101 of 105 lattices at the same
     coordinates, in both branches (N 2–8).
   - **Conditional payoff.** R3-emptiness implies CertAtom whenever |𝒜| = 2, at any N. The payoff is a composition
     of existing Lean theorems (§5.2).
2. **New Lean, scratch copy, standard axioms only, no `sorry`: `TwoColour.lean`.**
   - `desc_ge_of_postfixed` and `desc_ge_of_phi_last` (general).
   - `twoColour_gain`, `twoColour_shadow`, `twoColour_not_above`, `twoColour_noTrap` (W0, NoFix, two unbounded
     colours).
   - Together they prove steps 1–4 of the lead. They also prove the §296 paper claim "λ(a) ≱ a", whose cited
     argument does not cover the exit case (ladder audit A2).
   - They give a **normal form**: at |𝒜| = 2, CertAtom holds iff some colour row lands above its own colour
     (SelfCover2, §5.3).
3. **Decisive open step: ShadowLemma.** In R3 with ColourGain at the colour row b only, NoFix forces a ≤ φ(r_a), where
   r_a is the last high element of row a. With `twoColour_not_above` this closes the case.
   - It lives in a world that has models (the CGone mutant world), so it is finitely refutable, not vacuous.
   - The free check holds on all 247 SAT models of runs 1–5 that meet its hypothesis. These are samples: one model per
     lattice. An exact probe is owed (§10).
4. **Ladder audit.**
   - JointStuck is the target in other words (A1).
   - TopRow′ is exhausted as a single-row device. On 31 stored W0 models no real or virtual row satisfies its
     hypothesis (smallest |L| 10, H 5, N 2, |𝒜| = 2).
   - Virtual rows landing below their own element (LowLand) are refuted on 60 stored models.
   - The located lift through self-closed restrictions (LiftFix) is refuted on 20.
5. **P3 (all colour counts in the same world) is refuted**: with three colours R3 has NoFix models (42; smallest |L| 15,
   H 5). The two-colour swap is what the lead uses.
6. Sixteen frontier corrections (§15).

## 1. Frontier (restated; checked at source)

- **Lattice and rows.** L is finite (`NoChain α (H+1)`). F is monotone in both arguments, φ = F(⊥, ·), and
  a(x) = gfp F(x, ·). "High" means height ≥ 3 and "low" means height ≤ 2.
- **Descents and landings.**
  - The descent of row x is v_j(x) = (F x)^j ⊤.
  - The landing λ(x) is its first low element, at index i(x). Write r_x = v_{i(x)−1}(x), the last high element.
  - Row x exits when λ(x) ∉ Z.
- **W0 ∧ n1.** a(⊥) = ⊥, R_2 is tight, ⊤ ∉ R_2, and R_1 is not tight. Then Z = R_1 = φ⁻¹(⊥) (`mem_one_iff`), a
  down-set of heights ≤ 2 (ZT). At every row x of Z:
  - Ta: x lands (`ta_iff_lands`);
  - Tb: F(x, y) ≰ x for every high y (`tb_of_tight`);
  - `land_not_le`: λ(x) ≰ x;
  - `exit_atom`: if λ(x) ∉ Z, then h(λ(x)) = 2 and φ(λ(x)) is an atom of Z below λ(x) (`land_bot_lt`).
- **Colours.** 𝒜 is the set of atoms c ∈ Z with c = φ(w) for some w.
- **Target.** **CertAtom** (`Normalize.lean`): some atom q of Z has λ(q) ∉ Z and φ(λ(q)) = q.
  **NoFix** is its negation; it is the `hno` of `colourGain`.
- **Proved cases.**
  - N = 1 (`certAtom_N1`).
  - 𝒜 bounded in Z (`certAtom_of_boundedAtoms`).
  - TopRow (`certAtom_of_topRow`): any landing row lies above every colour.
  - TopRow′ (`certAtom_of_topRow'`): only the colours below the landing are needed.
  - `colourGain`: under NoFix, every landing row x (any x ∈ L) has a colour c ≤ λ(x) with c ≰ x.
- **Free rows.** Rows outside Z are free (`w0_of_T`). For x ∉ Z, every monotone g ≥ G_x := ⋁_{z ∈ Z, z ≤ x} F(z, ·) is a
  legitimate row of x in a monotone extension that keeps W0 and CertAtom unchanged. This brief checked the extension
  on paper (§7.1).
- **Open case.** N ≥ 2 and 𝒜 unbounded in Z. The smallest open subcase is |𝒜| = 2: 𝒜 = {a, b} with no z ∈ Z above
  both, and P := a ⊔ b ∉ Z.

## 2. Failure signature, sharpness, already tried

- **Signature on file**, kept: routes predict where the certificate sits or which row certifies; walks are anchored
  at ⊥; deformations relax what a landing-preserving deformation restores.
- **Widened this round.** Every route on file, TopRow, pairStair and TopLand among them, argues from **one row's
  landing at a time**, real or virtual.
  - The census `trall.py` shows this cannot close the open case. On 31 stored W0 models no single row, real or
    virtual (any legitimate redefinition), satisfies TopRow′'s hypothesis. There the certificate is an exit whose
    landing carries an undominated second colour.
  - The inversion: argue from the **two colour rows at once**, through the colour each one carries for the other.
    That is the lead.
- **Sharpness.**
  - Every statement here fails once R_2 tightness is dropped entirely (file).
  - In the lead's world, dropping ColourGain at either one of the two colour rows gives NoFix models (the CGone
    mutant, 101 of 105 lattices).
  - Dropping ColourGain at both rows gives models on 58 of 59 lattices (run 4, `R3 CGWnoCG`).
- **Testability.**
  - CertAtom at |𝒜| = 2 in W0 is `vacuous here` as a NoFix world: run 1 found 0 of 42 lattices.
  - The lead world R3 is a strict relaxation, with no Tb at the rows of Z other than ⊥. It is tested as a
    contradiction-mode statement. Its relaxation (CGone) has models.

## 3. Ladder audit

**A1. JointStuck is the target in other words.**
- JointStuck reads: from a high joint fixed point Y of the colour rows, produce a Tb violation or a smaller unbounded
  𝒜.
- Its hypothesis, "the joint colour rows are stuck", is not an extra hypothesis. Under NoFix ∧ 𝒜 unbounded it is
  automatic:
  - for G_X, the minimal legitimate row of X = ⋁𝒜, by `certAtom_of_topRow` and the free-row extension of §7.1;
  - for the other g_S, by brief295's paper TopRow-S.
- Its disjunct "a smaller unbounded 𝒜" names no construction, so it is not a step.
- So JointStuck is CertAtom on the class N ≥ 2 ∧ 𝒜 unbounded. Verdict: **restatement**, unless a deformation is
  specified. The previous brief flagged the risk; this audit confirms it.

**A2. The §296 claim "λ(a) ≱ a" had a gap; now proved in Lean.**
- The cited argument (ColourGain) gives b ≤ λ(a). It excludes a ≤ λ(a) only when λ(a) ∈ Z.
- In the exit case λ(a) = a ⊔ b with φ(a ⊔ b) = b is not excluded by it.
- `twoColour_not_above` closes the case: under NoFix, row b's descent carries a (shadow), so it stays above P and
  lands at P with exit atom b. That makes b fixed (§5.1).

**A3. ColourGain's alternation does have a contradiction-mode consequence.**
- It yields `twoColour_shadow`, `twoColour_noTrap` and `twoColour_not_above` (Lean).
- Empirically it yields the lead: R3 is inconsistent. Alternation at the two colour rows, plus landing, is all the
  contradiction uses.
- The §296 remark that "by itself it is no contradiction, since even μ-cycles occur" is right for μ-cycles. It does
  not cover the two colour rows' descents, which carry more than μ does.

**A4. TopRow′ is exhausted as a single-row device** (free censuses; models in `cex/`):

| statement (exists, per stored W0 model) | fails on | smallest |
|---|---|---|
| TRall: some real or virtual row satisfies TopRow′'s hypothesis (landing p, all colours ≤ p below x) | 31 (all unbounded; 18 with \|𝒜\| = 2) | \|L\| 10, H 5, N 2, \|𝒜\| 2 (`brief295/run3/m2_closure_5_11_4_30.json#18`) |
| LowLand: some x ∉ Z has a legit row landing at p ≤ x | 60 (also at N = 1) | \|L\| 8, H 4, N 1 |
| SelfLand: T ∉ Z with gfp(G_T ∨ T) = T, and G_T lands from T | 60 | same |
| TRexists: TRall over virtual rows only | 41 | \|L\| 8 |
| LiftFix: a T-fixed atom (T high and self-closed) is μ-fixed | 20 instances | \|L\| 10, H 4, N 2 |

Each of the first four would give CertAtom (paper; TopRow′ plus free rows). LiftFix would give it together with the
T-fixed atoms of A6. None of the five is universal.

**A5. Placement of the new rungs, re-derived from their proofs.**
- CertAtom(|𝒜| = 2) ⟸ R3-emptiness (§5.2).
- R3-emptiness ⟸ ShadowLemma(R3₁) (§5.4).
- CertAtom(|𝒜| = 2) ⟺ SelfCover2, a normal form:
  - (⟹) a fixed q* has λ(q*) ≥ φ(λ(q*)) = q* (`land_bot_lt`);
  - (⟸) `twoColour_not_above`.

  As a condition, SelfCover2 drops the clause "φ(λ(q)) = q" and the exit. In W0 at |𝒜| = 2 it is equivalent to the
  target. It is a normal form, not a rung of new strength, and it gives the target a sharper statement to aim at.
- None of the new rungs uses Tb at rows of Z other than ⊥.

**A6. Restriction.** The §296 entry "F ⊓ Y keeps Tb at atom rows but not at height-2 rows" concerns Y from the
colour rows only. Use instead a **self-closed** T: F(z, T) ≤ T for every z ∈ Z ∩ ↓T, that is G_T(T) ≤ T.
- Then every row of Z ∩ ↓T maps ↓T into itself.
- ↓T is a W0-type world with Ta, Tb, ZT and a(⊥) = ⊥ all inherited. n1 may fail, and none of the proofs uses it.
- Self-closed elements are closed under meets and form a Moore family.
- Free census: every one of the 1483 high self-closed restrictions of stored W0 models has a T-fixed atom.
- Under minimal high T, G_T(T) is low in 100 of 124 cases in the |𝒜| = 2 unbounded class. There TopRow inside ↓T
  applies.
- Only the lift is missing (P2).

**A7. Tb at height-2 rows** (design rule on file, "used only through land_not_le").
- In the D2 world, Tb at height-2 rows is replaced by λ(m) ≰ m. It has no NoFix ∧ |𝒜| = 2-unbounded model on 42
  lattices (run 1).
- R3 drops Tb at every row of Z other than ⊥ and is still empty. The design rule is consistent with this, and it is
  now stronger: in this class a proof needs no Tb at rows of Z other than ⊥ beyond what ColourGain packages.

## 4. Reuse (real names)

- `PairTrap.lean`: `colourGain`, `certAtom_of_topRow`, `certAtom_of_topRow'`, `pairStair`.
- `LateParent.lean`: `exit_atom`, `exitFixed_of_dom`, `land_not_le`, `land_bot_lt`, `land_index_pos`,
  `ta_iff_lands`, `mem_succ_of_cell`, `iter_antitone_of_le`, `eq_of_le_of_height_ge`, `height_strictMono`,
  `height_bot_eq_zero`, `Rk_mono`.
- `Normalize.lean`: `mem_one_iff`, `w0_of_T`.
- `StairB1.lean`: `exists_first_low`.
- New, in scratch `TwoColour.lean`: `desc_ge_of_postfixed`, `desc_ge_of_phi_last`, `twoColour_gain`,
  `twoColour_shadow`, `twoColour_not_above`, `twoColour_noTrap`.

---

## 5. LEAD: TwoColourCG (two colour rows carry each other's colour; that is already inconsistent)

### 5.1 What is proved (Lean, scratch: `TwoColour.lean`, `[propext, Classical.choice, Quot.sound]`)

**Hypotheses throughout:**
- W0: `ha`, `hk2`, `htop`;
- NoFix: `hno`;
- the colour atoms `ca ≠ cb` of Z;
- `hA2`: every atom value of φ in Z is `ca` or `cb`;
- `hU`: no z ∈ Z lies above both.

Write a = ca, b = cb, P = a ⊔ b.

1. **`desc_ge_of_postfixed`** (general). If c ≤ v_{j+1}(x) for every j < i, and Q ≤ F(x, Q) ⊔ c, then
   Q ≤ v_j(x) for every j ≤ i. Induction: Q ≤ F(x, Q) ⊔ c ≤ F(x, v_j) ⊔ v_{j+1} = v_{j+1}.
2. **`desc_ge_of_phi_last`** (general). If c ≤ φ(v_k(x)), then c ≤ v_{j+1}(x) for every j ≤ k. Here
   v_{j+1} = F(x, v_j) ≥ φ(v_j) ≥ φ(v_k), since v_k ≤ v_j.
3. **`twoColour_gain`.** b ≤ λ(a). `colourGain` gives a colour c ≤ λ(a) with c ≰ a, and `hA2` forces c = b.
4. **`twoColour_shadow`.** b ≤ φ(r_a). Put p = λ(a) and s = φ(r_a), so ⊥ ≠ s ≤ p.
   - If p ∈ Z:
     - when s is an atom, `hA2` gives s ∈ {a, b}, and s = a would put a, b ≤ p ∈ Z, against `hU`;
     - when h(s) = 2, s = p ≥ b.
   - If p ∉ Z: `exit_atom` makes φ(p) a colour. It is not a, because then a is fixed (`exitFixed_of_dom` with x = a).
     So b = φ(p) ≤ φ(r_a).
5. **`twoColour_not_above`.** a ≰ λ(a). Suppose a ≤ p = λ(a).
   - Since b ≤ p, p ∈ Z would contradict `hU`. So p ∉ Z, h(p) = 2 and p = a ⊔ b.
   - φ(p) is a colour other than a (NoFix), so φ(p) = b, hence b ≤ F(b, p) and p ≤ F(b, p) ⊔ a.
   - By shadow at b, a ≤ φ(r_b), so a ≤ w_k for 1 ≤ k ≤ i(b) (item 2).
   - Item 1 gives p ≤ λ(b), so λ(b) = p and φ(λ(b)) = b: b is fixed. Contradiction.
6. **`twoColour_noTrap`.** No Q ≥ a has Q ≤ F(a, Q) ⊔ b. By items 4, 2 and 1, Q ≤ λ(a), so a ≤ λ(a), against item 5.

**Consequences (paper, one line each):**
- No colour row lands at P.
- F(a, P) ≱ a, F(b, P) ≱ b, and φ(P) ≱ a, b.
- The descent of a leaves ↑P at a high y_a with F(a, y_a) ≱ a. The descent of b leaves it at a high y_b with
  F(b, y_b) ≱ b.
- y_a and y_b are incomparable. Proof: U = {y : F(b, y) ≥ b} and U′ = {y : F(a, y) ≥ a} are up-sets, with
  y_a ∈ U ∖ U′ and y_b ∈ U′ ∖ U.

### 5.2 Candidate lemma and conditional payoff

**Candidate (TwoColourCG; conjectural).** Let L be a finite lattice and F : L × L → L monotone. Write φ = F(⊥, ·)
and Z = φ⁻¹(⊥). Assume:
- a(⊥) = ⊥: no y ≠ ⊥ has y ≤ φ(y);
- Z is a down-set of heights ≤ 2 (ZT), contains a height-2 element (n1), and h(⊤) ≥ 3;
- the colour atoms (atoms of Z in φ(L)) are exactly a ≠ b, and no z ∈ Z lies above both;
- for c ∈ {a, b}, row c lands: no high y has y ≤ F(c, y), and λ(c) is its first low descent element;
- ColourGain at the two colour rows: b ≤ λ(a) and a ≤ λ(b).

Then some c ∈ {a, b} has λ(c) ∉ Z and φ(λ(c)) = c. No hypothesis is placed on any other row of Z, and no Tb on any
row.

Tested as R3 (`open_probe.py nofix 0 R3 UNB A2`):
- R3 also keeps `land_not_le` and no dominated exit at the colour rows. Both follow from ColourGain and NoFix at
  colours.
- The variants without them are also empty: `R3 CGWnoLN` and `R3 CGWnoND`, 0 of 59 each in run 4.

**Conditional payoff: TwoColourCG ⟹ CertAtom whenever |𝒜| = 2, at every N, in every branch.** In W0 ∧ NoFix ∧
|𝒜| = 2 unbounded, every hypothesis holds:
- landing is `ta_iff_lands`;
- λ ≰ c is `land_not_le`;
- λ(a) ≥ b is `twoColour_gain` (that is, `colourGain`);
- no dominated exit is `exitFixed_of_dom` with NoFix.

The conclusion contradicts NoFix. ∎ All four steps are Lean theorems. Once TwoColourCG is stated over an abstract
"three-row" hypothesis set, the payoff is a composition of them.

### 5.3 Placement

- CertAtom(|𝒜| = 2) ⟸ TwoColourCG. TwoColourCG is a statement about a world R3 ⊋ W0 ∧ NoFix; it uses no Tb at rows
  of Z other than ⊥.
- **Normal form:** CertAtom(|𝒜| = 2) ⟺ SelfCover2 (∃ colour c with c ≤ λ(c)). Lean for ⟸; paper for ⟹.
- With 5.1 item 5, TwoColourCG is ⟺ "R3 ∧ CG at both colour rows forces some c ≤ λ(c)". In R3 the Lean lemmas hold
  with the R3 hypotheses in place of W0, because their proofs use only Ta, `exit_atom` and `exitFixed_of_dom`'s
  domination at colour rows.
- It is not the target restated: its world contains R3 models without NoFix, and its relaxation CGone has NoFix
  models.

### 5.4 Decisive open step: ShadowLemma

**ShadowLemma (conjectural).** Take R3 with ColourGain at the colour row b only (world R3₁). NoFix implies a ≤ φ(r_a),
where r_a is the last high element of row a.

**Payoff, proved.** In W0 ∧ NoFix, CG(b) holds (`twoColour_gain`). ShadowLemma gives a ≤ φ(r_a) ≤ F(a, r_a) = λ(a),
against `twoColour_not_above`. So ShadowLemma ⟹ CertAtom(|𝒜| = 2). In R3 it gives R3-emptiness.

**Status:**
- Free check on every SAT model of runs 1–5 that has a CG colour and two landing colour rows (`shadow.py`): 247 of
  247. The models come from run 4's R3 CGWnoCG, run 2's CGWnoCG, run 1's Desc1/Row1/LastEither and run 5's CGone,
  and reach H 14, M 7 and exact N 3–6.
- In all 179 CGone models, λ(a) ∈ Z lies above a. Row a lands inside its own colour.

  These are samples (one model per lattice). The exact probe is owed (§10).

**Hint from the data, not evidence** (`cgone_stats.py`, `r3look.py`):
- φ(r_a) = a in 147 of 179 models.
- r_a = r_b in 108 of 179, and r_a ≥ P in 141 of 179.
- In the smallest model (|L| 9, H 4), both descents pass through P with φ(P) = a.
- So the natural route is a trap at P from b's side. The case to handle is a descent of a that leaves ↑P before the
  descents meet (r_a ≱ P: 38 of 179).

### 5.5 Remaining programme fields

| field | content |
|---|---|
| testability | TwoColourCG: `finitely refutable`, tested in contradiction mode in R3 (it is `vacuous here` in W0). ShadowLemma: `finitely refutable` in R3₁, which has NoFix models (101 of 105 lattices) |
| hypothesis world | R3 ∧ NoFix ∧ \|𝒜\| = 2 unbounded (no models found). Relaxation: CGone (ColourGain at one colour row), with models in both branches at every room point |
| counterexample anatomy | by 5.1: two colour rows whose descents carry the other colour from index 1 on; neither lands above its own colour or at P; they leave ↑P at incomparable high y_a, y_b. Smallest coordinates: H ≥ 4 (two incomparable high elements above P plus ⊤), width ≥ 2 above P, N ≥ 2. The mutant's smallest model is \|L\| 9, H 4 |
| room reached (candidate 0 SAT) | H 4–14; width M 4, 6, 7; exact N 3–6; \|L\| 9–45; closure corpora with 5–8 points (up to 6–7 atoms) |
| mode | signature inversion (two rows at once, invariant carried along both descents: v_j ≥ b, w_k ≥ a), then set-aside reversal (Tb dropped, which nrmHom never restores, so it is not a W0♭-type relaxation) |
| limit | |𝒜| = 2 only. For \|𝒜\| ≥ 3 see P3. It gives no proof of ShadowLemma |
| decisive open step | ShadowLemma (5.4), or directly: in R3, CG at both colour rows ⟹ some c ≤ λ(c) |

## 6. Other programmes

### P2. Self-closed restriction (deformation inside W0; induction on |L|)

| field | content |
|---|---|
| candidate | **Lift** (conjectural): if T is high and self-closed (G_T(T) ≤ T), then CertAtom in ↓T (descents from T) implies CertAtom in L |
| payoff (conditional, paper) | (a) Take a minimal high self-closed T. G_T(T) is self-closed, since Z ∩ ↓G_T(T) ⊆ Z ∩ ↓T. So G_T(T) is low or equals T. (b) If G_T(T) is low, TopRow inside ↓T, with x = T, gives a T-fixed atom; Lift then gives CertAtom. (c) The remaining case, G_T(T) = T with no smaller high self-closed element, is **open**. It covers 24 of 124 minimal T's in the \|𝒜\| = 2 unbounded class (`selfclosed_out.txt`). So the payoff is CertAtom ⟸ Lift ∧ Base, where Base is that case |
| placement | normal form: the restriction is a W0-type world (A6), and it is checked on 1483 restrictions. Lift sits at CertAtom |
| testability | Lift is `vacuous here` in W0, which already has fixed atoms. Its located form LiftFix is **refuted** (20 stored instances, `cex/LiftFix.json`). The existence form needs a relaxation (Desc1) |
| anatomy | a self-closed T whose T-fixed atom does not lift: smallest \|L\| 10, H 4, N 2 |
| mode | set-aside reversal (restriction, which the file has as F ⊓ t_j, refuted) with the correct closure condition |
| limit | the Base case is a second open problem. Only a proof of Lift that also handles Base would be leverage |
| decisive open step | Lift: from a T-fixed atom q (descent from T to p, φ(p) = q), build a legitimate row of some x ≥ q whose ⊤-descent reaches p. A chain ⊤ = y_0 > … > y_k = T with G_x(y_j) ≤ y_{j+1} suffices (`exitFixed_of_dom` plus the chain construction of §7.1). LowLand's refutation shows it cannot always be the row of T itself |

### P3. ColourGraph: all colour counts. In R3 it is REFUTED; the refined candidate is ColourGain at every row of Z

| field | content |
|---|---|
| candidate as proposed | R3 with ColourGain at every colour row, NoFix and 𝒜 unbounded in Z, any \|𝒜\| ≥ 2: no model. **Refuted (run 5).** 40 of 40 SAT on closure 6 12 1 40 and 2 of 2 at \|𝒜\| = 3 on tall 10 6 1 8. All 42 models, \|𝒜\| 3–4 and both branches, are in `cex/ColourGraph_R3.json`; the smallest has \|L\| 15, H 5, N 3 |
| anatomy of the refutation | in all 42 models, every pair of colours that swap (each below the other's landing) is **bounded in Z**, so `hU` fails for the pair and the trap of 5.1 item 5 cannot start. ColourGain also fails at some non-colour row of Z, which R3 leaves free (42 of 42) |
| refined candidate (CGW-any) | CGW, that is Ta, `land_not_le`, ColourGain and no dominated exit at **every** row of Z, Tb only at ⊥, with NoFix and 𝒜 unbounded in Z for any \|𝒜\|: no model. **Untested** at \|𝒜\| ≥ 3, because the budget was spent |
| payoff | CGW-any plus `colourGain` (any landing row), `ta_iff_lands`, `land_not_le` and `exitFixed_of_dom` gives CertAtom on the whole open case. Every CGW hypothesis is a W0 ∧ NoFix theorem |
| placement | CGW-any ⟹ CGW at \|𝒜\| = 2, which run 2 found empty on 71 lattices (subsumed by the lead's R3). CGW-any ⟹ CertAtom |
| testability | finitely refutable; `open_probe.py nofix 0 CGW UNB <corpus>` (no `A2`). The calibrated mutant is R3 UNB (refuted above) |
| mode | signature inversion: one invariant carried by every row of Z, with no row named |
| limit | the Lean two-colour lemmas need `hA2` and `hU` for the pair. With three colours the mechanism must pass through a height-2 row m ∈ Z above a swapping pair; ColourGain at m then supplies a third colour |
| decisive open step | the pair-bounded case: colours a, b that swap, with m ∈ Z above both. Show that ColourGain at m, carried along row m's descent (the analogue of `twoColour_shadow` for m), traps a colour row above its own colour |

## 7. Free-row and chain constructions (paper, used above)

### 7.1 Legitimate rows (`w0_of_T`)

For x₀ ∉ Z, let g ≥ G_{x₀} be monotone. Define the rows:
- F′(x, ·) = F(x, ·) for x ∈ Z;
- F′(x₀, ·) = g;
- F′(x, ·) = g ∨ G_x for x > x₀ with x ∉ Z;
- F′(x, ·) = G_x for the other x ∉ Z.

F′ is monotone in x: G_x is monotone in x, F(z, ·) ≤ G_x for z ≤ x, and G_x ≤ G_{x₀} ≤ g for x < x₀. Row ⊥ and the
rows of Z are unchanged, so W0 and CertAtom are unchanged.

**Chains.** A legitimate row of x₀ lands at p iff there is a chain ⊤ = y_0 > … > y_i = p with y_j high for j < i,
p low and G_{x₀}(y_j) ≤ y_{j+1}. Take g(y) = G_{x₀}(y) ∨ y_{j₀(y)+1}, where j₀(y) is the least j with y_j ≤ y.

### 7.2 Self-closed elements

T is self-closed iff F(z, T) ≤ T for every z ∈ Z ∩ ↓T.
- Self-closed elements are closed under ⊓, and ⊤ is self-closed.
- For self-closed T, G_T(T) is self-closed.
- ↓T inherits Ta, Tb and ZT at the rows of Z ∩ ↓T, and a(⊥) = ⊥.

## 8. Probe report lines (exact runs; every SAT model replayed from F in Python and asserted)

The quantifier is "for each lattice of the corpus, does a model of the stated world exist". In every line, SAT means
a model of that world with no μ-fixed atom of Z and the stated colour conditions. Every line below reached
`|𝒜| = 2, unbounded` unless it says otherwise. Branch and N of SAT models were read off the `model:` lines.

```
CertAtom |A|=2 in W0 (sanity, vacuous world) | open_probe nofix 0 UNB A2 (exact) | run 1
  closure 5 11 4 30 (H4-5, |L| 9-27) 0/30; tall 8 4 1 12 (H8, |L| 16-33) 0/12
  mutants (refuted relatives, bank s292_row1_h8 / s292_lasteither_h10): Row1 0/30, 8/12 (atom N2-3);
  LastEither 0/30, 3/12 (atom N2); Desc1 18/30, 11/12 (a and atom, N2-5)
  footprint: every relaxed model violates ColourGain at a real row (cgcheck.py: 0 informative of 52)
      -> silent (the W0 world is vacuous as expected); the mutants show the corpora reach the class at H8
D2 world (Tb at height-2 rows only as land_not_le) | run 1 | 0/30, 0/12   -> provisional (design rule)
CGW (Tb dropped at all rows but bot; Ta, land_not_le, ColourGain, no dominated exit at every Z-row) | run 2
  closure 5 11 4 30 0/30; tall 8 4 1 12 0/12; tall 10 4 2 20 maxn 40 0/17; tall 12 4 1 8 maxn 45 0/5;
  tall 13 4 1 8 maxn 45 0/5; tall 10 6 1 8 maxn 45 0/2
  mutant CGWnoCG (ColourGain dropped): 16/30, 11/12 (a and atom, N2-3); CGWnoND 0/30, 0/12; CGWnoLN 0/30, 0/12
      -> provisional (subsumed by R3)
CG sub-worlds of CGW | run 3 | CGcol (CG only at colour rows) 0/30, 0/12; CGh2 0/30, 0/12; CGat 0/30, 0/12
R3 (LEAD world) | run 4 | closure 5 11 4 30 0/30; tall 8 4 1 12 0/12; tall 10 4 2 20 maxn 40 0/17
  R3 CGWnoND 0/30, 0/12, 0/17; R3 CGWnoLN 0/30, 0/12, 0/17
  mutant R3 CGWnoCG: 30/30, 11/12, 17/17 (branch a N2-6, atom N2-7)
  hand lattices run4/hand_lattices.json (built for lambda(b)=a, lambda(a)=P): R3 0/2, CGW 0/2, CGWnoCG 1/2
R3 LEAD push | run 5 | candidate R3 UNB A2  vs  calibrated mutant CGone (CG at one colour row only)
  room coordinates reached: H 4-14, width M 4/6/7, exact N 3-6, |L| 9-45, closure corpora 5-8 points
  see the table in 8.1
      -> provisional at H <= 14, M <= 7, N <= 6 (pushes owed: second encoding; |L| > 50; N >= 7 exact)
P3 ColourGraph (R3, any |A|) | run 5 | open_probe nofix 0 R3 UNB [A3] (exact) | SAT = R3 model, NoFix, colours unbounded
  closure 6 12 1 40: 40/40 SAT (|A| 3-4); tall 10 6 1 8 maxn 45 A3: 2/2 SAT
      -> REFUTED (cex/ColourGraph_R3.json, 42 models; smallest |L| 15, H 5, N 3, |A| 3, branch atom)
ShadowLemma (decisive step) | free check on run dumps (samples only: one model per lattice) | 247/247 hold
      -> silent (an exact probe is owed, see 10)
```

### 8.1 Run 5 table (candidate | mutant CGone)

| corpus | candidate R3 SAT / lattices (H, \|L\|) | mutant CGone SAT / lattices (branch, N of its models) |
|---|---|---|
| closure 6 12 1 40 | 0 / 40 (H 4,5,6, \|L\| 15-38) | 40 / 40 (H 4,5,6, \|L\| 15-38) a N2:6, a N3:3, a N4:2, atom N2:18, atom N3:9, atom N4:2 |
| closure 8 10 1 300 maxn 45 (capped) | 0 / 33 (H 5,6,7, \|L\| 21-44) | — |
| closure 5 11 4 30 | — | 30 / 30 (H 4,5, \|L\| 9-27) a N2:4, atom N2:26 |
| tall 13 4 1 8 maxn 45 | 0 / 5 (H 13, \|L\| 33-44) | 5 / 5 (H 13, \|L\| 33-44) atom N3:1, atom N4:1, atom N6:2, atom N8:1 |
| tall 14 4 2 20 maxn 45 (capped) | 0 / 5 (H 14, \|L\| 35-44) | 6 / 6 (H 14, \|L\| 35-45) a N5:1, atom N2:1, atom N3:2, atom N4:2 |
| tall 10 6 1 8 maxn 45 (M 6) | 0 / 2 (H 10, \|L\| 35-42) | 2 / 2 (H 10, \|L\| 35-42) a N2:1, atom N3:1 |
| tall 10 7 1 5 maxn 50 (M 7) | 0 / 1 (H 10, \|L\| 42-42) | 2 / 2 (H 10, \|L\| 42-49) a N2:1, atom N2:1 |
| tall 12 4 1 8 maxn 45, exact E3 | 0 / 5 (H 12, \|L\| 27-45) | 4 / 5 (H 12, \|L\| 27-45) atom N3:4 |
| tall 12 4 1 8 maxn 45, exact E4 | 0 / 5 (H 12, \|L\| 27-45) | 4 / 5 (H 12, \|L\| 27-45) atom N4:4 |
| tall 12 4 1 8 maxn 45, exact E5 | 0 / 4 (H 12, \|L\| 32-45) | 4 / 5 (H 12, \|L\| 27-45) a N5:2, atom N5:2 |
| tall 12 4 1 8 maxn 45, exact E6 | 0 / 2 (H 12, \|L\| 32-33) | 4 / 5 (H 12, \|L\| 27-45) a N6:1, atom N6:3 |
| P3 candidate: closure 6 12 1 40, UNB only (any \|A\|) | 40 / 40 (H 4,5,6, \|L\| 15-38) | 40 / 40 (H 4,5,6, \|L\| 15-38) a N2:5, atom N2:23, atom N3:12 |
| P3 candidate: tall 10 6 1 8 maxn 45, \|A\| = 3 | 2 / 2 (H 10, \|L\| 35-42) | — |

TOTAL over the \|A\| = 2 rows: candidate 0 / 102, mutant 101 / 105.

All run-5 jobs ran within their per-job caps; jobs marked "(capped)" stopped at the cap before finishing the corpus.
Across runs 4 and 5, R3 at |𝒜| = 2 has **0 SAT on 161 lattices**:
- run 4: 59 lattices, H 4–10;
- run 5: 102 lattices, H 4–14, M 4/6/7, exact N 3–6, \|L\| ≤ 45.

The calibrated mutant CGone has 101 SAT on 105 lattices at the same coordinates, in branches a and atom and at
N 2–8. The mutant R3 CGWnoCG (run 4) has 58 SAT on 59.

**P3 result.** R3 with any number of colours (UNB without A2) is **refuted**:
- closure 6 12 1 40: 40 of 40 SAT;
- `R3 UNB A3` on tall 10 6 1 8: 2 of 2 SAT;
- all 42 models are in `cex/ColourGraph_R3.json`; the smallest has \|L\| 15, H 5, N 3 and \|𝒜\| = 3.

In every one of the 42 models, each pair of colours that swap (each lies below the other's landing) is bounded in
Z. ColourGain also fails at some row of Z that is not a colour row (`colourgraph.py` and the check printed in §6
P3).

## 9. Probe scripts (all in the work dir; `PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation`)

**`open_probe.py`** is the repository's `orbit_probe.py` with the following flags added.
- **Colour flags.**
  - `UNB`: every z ∈ Z misses some colour atom. A colour atom is col(c) ⟺ Z(c) ∧ ∃w F(⊥, w) = c, with both
    directions encoded.
  - `A2` / `A3`: exactly two or three colour atoms.
- **`D2`:** Ta2 plus λ(m) ≰ m at height-2 rows.
- **`CGW`:**
  - Tb is dropped at every row of Z except ⊥.
  - At every Z-row: `land_not_le`; no dominated exit (λ(x) = p ∉ Z with φ(p) = c ≤ x is forbidden); and ColourGain
    (some p, c with lam(x, p), col(c), c ≤ p, c ≰ x).
  - Mutants `CGWnoCG`, `CGWnoND`, `CGWnoLN`.
- **CG sub-worlds:** `CGcol`, `CGat`, `CGh2`.
- **`R3`:** CGcol, with Ta, `land_not_le` and no-dominated-exit guarded by col(x), so they bind at colour rows only.
- **`CGone`:** CG only at colour rows with a selector, and at least one selected colour row.
- **Replay.** Every relaxed world is replayed from F in Python: colours, unboundedness, count, Ta at the constrained
  rows, Tb at ⊥, `land_not_le`, ColourGain, NoFix. A mismatch asserts. The mode `nofix` prints its SAT meaning and one
  line per lattice.

**Free analyses (no SAT):**
- `census0.py` and `lib.py` (the model cache).
- `look.py` and `look2.py` (two-colour anatomy, stuck rows).
- `selfclosed.py` (A6, P2).
- `lowland.py` and `trall.py` (A4).
- `footprint.py` and `cgcheck.py` (relaxed footprints).
- `cgviol.py`, `selfshadow.py`, `shadow.py`, `cgone_stats.py`, `r3look.py` (lead).
- `twocol_census.py` (stored two-colour models).

**Smoke tests** (encoding checks, not evidence; disclosed): 6 lattices each, `smoke/`. They are `Desc1 UNB A2`
(twice, about 30 s) and `CGW UNB A2` (about 20 s).

## 10. Pushes owed

- **Second encoding of R3-emptiness**, written from §5.2's statement rather than from `open_probe.py`.
- **Exact probe of ShadowLemma.**
  - World: CGone, with the selected colour b, NoFix, UNB and A2.
  - Add: the other colour a has a ≰ φ(r_a). Encode r_a through the `RL(x, w)` variables, as `orbit_probe.py` builds
    them under Row1/Meet2.
  - SAT = ShadowLemma fails. Calibrate on the 247 dumped models, which must all be UNSAT.
- **Room for the lead:**
  - |L| > 50;
  - exact N ≥ 7;
  - width M 8;
  - closure 8 10 beyond the 33 lattices reached before the cap.
- **Lean:** move `TwoColour.lean` into `lean/Mordor/` and re-run `#print axioms`. Then state TwoColourCG over abstract
  three-row hypotheses and prove "TwoColourCG ⟹ CertAtom(|𝒜| = 2)" as a composition (§5.2).
- **P3:** `CGW UNB` (any |𝒜|) on closure 6 12 1 40, tall 10 6 1 8 and tall 13 4 1 8. The mutant is R3 UNB, which has models on 42 of 42 lattices.

## 11. Already failed (do not repeat)

All of frontier §4, plus:
- JointStuck as a step: a restatement (A1).
- **TRall, LowLand, SelfLand, TRexists:** single-row TopRow′ in every real or virtual form (A4; `cex/TRall.json`,
  `cex/LowLand.json`, `cex/SelfLand.json`, `cex/TRexists.json`).
- **LiftFix:** a located lift through self-closed restrictions (`cex/LiftFix.json`).
- **ColourGraph in R3:** ColourGain at the colour rows alone, with three or more colours (`cex/ColourGraph_R3.json`).
  Every swapping pair there is bounded in Z.
- Footprints of the Desc1, Row1 and LastEither NoFix models in the open class are uninformative: every one violates
  ColourGain at a real row (`cgcheck.py`). Relaxations that break ColourGain test TopRow′, not the open case.

## 12. Hard constraints and design rules (updated)

- **Colour bound:** φ(L) ⊆ ↓t_1, and with |𝒜| = 2 both colours lie below t_1 ∉ Z (N ≥ 2).
- **New design rule (provisional):** in the class |𝒜| = 2 unbounded, a proof needs only rows ⊥, a, b, and from them
  only landing, ColourGain and NoFix. No Tb is needed at rows of Z other than ⊥, and no row of Z other than the
  colours.
- **Invariant on file now (Lean):** each colour row's descent carries the other colour from index 1 to its landing
  (`twoColour_shadow` with `desc_ge_of_phi_last`).

## 13. Formalization order (no `sorry`, no new axioms)

1. `TwoColour.lean` as is. It compiles against `PairTrap.lean`; axioms in `lean_twocolour_axioms_out.txt`.
2. SelfCover2 (⟹ direction), using `land_bot_lt`.
3. An abstract `ThreeRow` structure (the R3 hypotheses), with the 5.1 lemmas restated over it and the composition
   W0 ∧ NoFix ⟹ ThreeRow.
4. ShadowLemma, if a proof is found.

## 14. Expected report (one verdict each)

- **LEAD (TwoColourCG):** `provisional` (pushes owed in §10) plus `conditional lemma` (5.2, Lean-composable) plus
  `normal form` (SelfCover2). ShadowLemma: `provisional` once the exact probe is run, else `needs direct proof`.
- **P2 (Lift):** `conditional lemma` with an open Base case. Its located form is `refuted` (LiftFix).
- **P3 (ColourGraph):** `refuted` in R3 (42 banked models). The refined CGW-any is `untested`, and its first probe is owed.

## 15. Frontier corrections

1. **§2 open-case bullet, "Decisive step JointStuck".** This is a restatement (A1). Its "stuck" hypothesis is
   automatic under NoFix ∧ 𝒜 unbounded: TopRow at X = ⋁𝒜 with the minimal row G_X, which is legitimate by `w0_of_T`
   (§7.1). The "smaller 𝒜" alternative names no construction.
   - Replace it with: decisive step **TwoColourCG** (|𝒜| = 2), and within it **ShadowLemma** (brief run 22, §5).
2. **§2 "|𝒜| = 2 under NoFix (paper, §296): … and λ(a) ≱ a".** The cited ColourGain argument covers only λ(a) ∈ Z. The
   exit case λ(a) = a ⊔ b with φ(a ⊔ b) = b was open. It is now proved: `twoColour_not_above` (scratch Lean,
   `TwoColour.lean`, standard axioms; to be installed).
3. **§2 "restriction F ⊓ Y to ↓Y keeps Tb at atom rows but not at height-2 rows".** This is true for Y built from the
   colour rows only.
   - For a **self-closed** T (F(z, T) ≤ T for every z ∈ Z ∩ ↓T), the restriction keeps Ta, Tb at every row of
     Z ∩ ↓T, ZT and a(⊥) = ⊥. Only n1 can fail.
   - Self-closed elements form a Moore family.
   - Add this as a normal form (paper) with its census: 1483 restrictions of stored W0 models all have a T-fixed atom.
4. **§2 ladder, add these entries:**
   - `desc_ge_of_postfixed`, `desc_ge_of_phi_last` (general);
   - `twoColour_gain`, `twoColour_shadow`, `twoColour_not_above`, `twoColour_noTrap` (W0, NoFix, two unbounded
     colours) [scratch Lean];
   - CertAtom(|𝒜| = 2) ⟺ SelfCover2 (some colour c ≤ λ(c)) [⟸ Lean `twoColour_not_above`; ⟹ paper via
     `land_bot_lt`];
   - CertAtom(|𝒜| = 2) ⟸ TwoColourCG [paper composition of Lean theorems];
   - TwoColourCG ⟸ ShadowLemma(R3₁) [paper, via `twoColour_not_above`].
5. **§4 refuted routes, add these entries** (models in `brief run 22/cex/`):

   | route | stored W0 models | smallest |
   |---|---|---|
   | TRall: some real or virtual row satisfies TopRow′'s hypothesis | 31 | \|L\| 10, H 5, N 2, \|𝒜\| 2 |
   | LowLand / SelfLand: a virtual row landing below its element | 60 | \|L\| 8, H 4, N 1 |
   | TRexists | 41 | — |
   | LiftFix | 20 instances | \|L\| 10, H 4, N 2 |
6. **§4 failure signature, widen it.** Every route argues from one row's landing at a time, real or virtual.
   TopRow′ is exhausted in that form (TRall).
7. **§9 vacuity map, add these entries:**
   - W0 ∧ NoFix ∧ 𝒜 = {a, b} unbounded: 0/42 lattices (run 1).
   - D2 (Tb at height-2 rows only as λ(m) ≰ m): 0/42.
   - CGW (Tb dropped at all rows of Z other than ⊥): 0/71.
   - R3 (rows ⊥, a, b only): none found, see §8 of the brief.
   - Worlds with models in this class:
     - Desc1 (H 4–8);
     - Row1 and LastEither (H 8 only; none at H 4–5);
     - CGWnoCG;
     - R3 without ColourGain;
     - CGone (ColourGain at one colour row; H 4–14, M ≤ 7, exact N 3–6, both branches).
8. **§10 corpora / testers, add this note.** In the open class, the NoFix models of the relaxations Desc1, Row1 and
   LastEither all violate ColourGain at a real row (`cgcheck.py`, 0 informative of 52). Their footprints test
   TopRow′, not the open case. A footprint of the open case needs a world that keeps ColourGain (CGW, R3).
9. **§7 hard constraints, "Tb at atom rows is used at three-row pair columns".** This is a property of the N = 1 proof,
   not of every proof. In the |𝒜| = 2 class the lead world uses no Tb at rows of Z other than ⊥ (provisional). Mark it
   proof-specific.
10. **§7 design rules, add these rules:**
    - (Lean) each colour row's descent carries the other colour from index 1 to its landing;
    - no colour row lands above its own colour;
    - no Q ≥ a has Q ≤ F(a, Q) ⊔ b.
11. **§7 design rule (provisional), add it.** In the |𝒜| = 2 class a proof needs only rows ⊥, a, b, and from them only
    landing, ColourGain and NoFix.
12. **§2 ladder line "CertAtom ⟸ TopRow".** State that any legitimate row g ≥ G_x of x ∉ Z counts (§7.1 of the brief,
    a paper extension of `w0_of_T`). A legitimate row of x lands at p iff a chain ⊤ = y_0 > … > p with
    G_x(y_j) ≤ y_{j+1} exists.
13. **§6 room vector, add these dimensions:**
    - |𝒜|: 2 to 5 on stored W0 models, 2 and 3 in runs;
    - the number of points of closure corpora: closure 6 12 and closure 8 10 now used, up to H 7;
    - the colour-count flags `UNB` / `A2` / `A3` of `open_probe.py`.
14. **§3 buckets, Unverified, add these entries:**
    - TwoColourCG: provisional, one encoding (`open_probe.py R3`);
    - ShadowLemma: samples only, 247 of 247 SAT models;
    - CGW, D2: one encoding.
15. **§2 census sentence.** "The joint row over {⊥} ∪ 𝒜 is stuck high in 109" agrees with this brief's recount: 109 of
    167, of which 65 have |𝒜| = 2. Add that, for |𝒜| = 2, the minimal virtual row G_P of P = a ⊔ b is stuck in 65 of
    81 models. In the other 16 it lands, and TopRow gives the fixed atom (`look2.py`).
16. **§8 set-aside choices, add this entry.** The restriction to a self-closed T (P2 of brief run 22), not to t_j or to
    a colour-row fixed point. It was set aside pending Lift, because the located lift LiftFix is refuted.
