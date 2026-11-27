# Brief, run 17 — outside briefer (adjoint-math-research v1.0)

**Repository** /home/user/mordor at **32526d4** (read-only; nothing in the checkout was written, built or changed; no git
command was run except `git log -1`). Sources checked: `lean/Mordor/LateParent.lean` section `Landing` (lines 5455–6010,
including `selfLow`, `GoodTop`, `certAtom_of_goodTop`, `fixed_or_stall_of_good`, `goodAtom1_iff_fixed_or_stall`,
`trap_of_tb`, `domCoLand`, `upTrap_stay`, `upTrap_land`, `exitFixed_of_dom`, `certAt_of_fixed_below`, `exit_atom`,
`land_not_le`, `ta_iff_lands`), `not_good_of_ahead` (line 4510), `Derived.lean` (`b`, `b_le`, `le_a`, `row_a`),
`OrbitHeight.lean` (`mem_succ_of_cell`), `SingletonLowerTransfer.lean` (`mem_succ_of_b`), `Orbit.lean` (`Rk`, `Rk_succ`);
log `docs/rounds/26-v3.7.md` §34.3z²⁸⁹–²⁹⁰; `experiments/amalgamation/brief289/brief.md`; `bank.py`, `bank/`, `direct290/`.
Everything this brief produced is in this directory (scripts, outputs, models).

**Mission (negation of the failure signature).** *Normalize before you relax.* First deform F, inside the world and
without moving any landing, into its canonical form; only the hypotheses that survive the normal form are ones a proof
must use, and only relaxations the normal form cannot undo give contradiction-mode lemmas real models.

---

## 0. Summary

1. **Ladder audit, main result (paper, complete, checked on 192 stored models): GoodTop ⟺ CertAtom.** A
   landing-preserving normalization of the height-2 rows maps every W0♭ model with no self-landing row into W0 with the
   same Z, the same descents and the same μ (§2, N2). So GoodTop is the target in other words; "GoodnessTransfer" *is*
   CertAtom; G1 ⟺ ExitZ(W0) and G2 ⟺ ExitToFix(W0). Every W0♭ ∧ NoFix model ever sampled (§289–290) has a witness and is
   therefore outside the target's counterexample world; the §290 statistics carry no information about the target.
2. **Normal form DMax (paper, complete, checked on 192 stored models).** For CertAtom one may assume
   F(x, y) = ⋀{u_{j+1}(x′) : x′ ∈ Z, x ≤ x′, y ≤ u_j(x′)} on every row x ≠ ⊥ of Z (rows outside Z constant ⊤).
   Consequences, as a theorem: Ta is used only as "every row of Z lands"; Tb at the height-2 rows only as λ(m) ≰ m; Tb at an
   atom row q only at meets of descent elements of rows of Z above q.
3. **Lead (TwoRowTb):** existence survives with Tb at an atom row q imposed only at columns u ⊓ v, u on row q's descent,
   v on the descent of one row x ∈ Z with q ≤ x — exactly the instances `trap_of_tb`/`domCoLand` consume. Exact: no
   counterexample on 68 lattices (H 4–10, width ≤ 15); calibrated mutant desc1 fails on 64/68 (branches a, b, g).
   `provisional`; H 13–14, M 7 and exact N owed.
4. **P2 (LfpMin, column form of the target)**: no counterexample on 74 lattices (H ≤ 13), mutant fails on 72/74; placed
   *above* the target (a located strengthening), low priority.
5. Frontier corrections: 16 (§14).

## 1. Frontier (restated; checked at source)

- L finite (`NoChain α (H+1)`), F monotone in both arguments, h = `height H`, a(x) = gfp F(x,·), b(y) = lfp F(·,y)
  (`Derived.lean`), φ = F(⊥,·). R_0 = ↓⊥, R_{k+1} = ↓(R_k ∪ a(R_k) ∪ b⁻¹(R_k)) (`Rk`, `Rk_succ`; membership lemmas
  `mem_succ_of_cell`, `mem_succ_of_a`, `mem_succ_of_b`). "High" = height ≥ 3.
- **W0 ∧ n1**: a(⊥) = ⊥, R_2 tight, ⊤ ∉ R_2, R_1 not tight. Then R_1 = Z = φ⁻¹(⊥). With h(⊤) ≥ 3 it is equivalent to
  a(⊥) = ⊥, ZT, n1 and (T) at every row of Z: Ta(x): no high y with y ≤ F(x,y); Tb(x): no high y with F(x,y) ≤ x.
  (The ⟸ direction, needed below, is re-derived in §2 N2, step 6.)
- Row descent u_j(x) = (F x)^j ⊤; λ(x) = first element of height ≤ 2 (`ta_iff_lands`: Ta(x) ⟺ the row lands); r_x =
  u_{i(x)−1}(x) the last high element; exit: λ(x) ∉ Z, then c(x) = φ(λ(x)) is an atom (`exit_atom`). μ(x) = λ(x) if
  λ(x) ∈ Z, else c(x). μ-fixed atom = CertAtom witness. M2 = height-2 elements of Z.
- **W0♭** = W0 ∧ n1 with Tb dropped at the height-2 rows (`GoodTop`'s hypotheses, `LateParent.lean` 5979).
  **W0^desc** = W0♭ ∧ (∀ m ∈ M2: λ(m) ≰ m). By `selfLow`, W0^desc = W0♭ ∧ (no m ∈ M2 self-lands).
- **Open target CertAtom** (W0 ∧ n1 ⟹ some atom of Z is μ-fixed). Lean: `certAtom_of_goodTop` (GoodTop ⟹ CertAtom).
- GoodTop = G1 ∧ G2 (§290): G1: W0♭ ∧ no row of Z exits ⟹ some m ∈ M2 self-lands; G2: W0♭ ∧ some exit ∧ NoFix ⟹ same.

## 2. Ladder audit

### A1. Lower cells at height-2 rows (paper, Lean-ready) — *Bcell*
In W0♭, m ∈ M2, y high: F(m,y) ≤ m ⟹ F(m,y) = m. Hence b(y) ∈ Z ⟹ b(y) ∈ M2 and F(b(y),y) = b(y); and
b(y) ∈ Z ⟺ ∃ m ∈ M2 with F(m,y) = m.
*Proof.* F(m,y) ≥ φ(y) ≠ ⊥ (else y ∈ Z, against ZT). If F(m,y) = q is an atom, q ≤ m gives F(q,y) ≤ F(m,y) = q, a lower
cell at the atom row q at a high column, against Tb(q). So F(m,y) = m. For b(y) ∈ Z: b(y) = F(b(y),y) (lfp), b(y) ≠ ⊥
(φ(y) ≠ ⊥), not an atom (Tb), so b(y) ∈ M2. Conversely F(m,y) = m gives b(y) ≤ m (`b_le`). ∎
So **W0♭ ∖ W0 is exactly "some height-2 row of Z has a fixed cell F(m,y) = m at a high column"** (= b(y) ∈ Z for some high
y), and every self-landing m is b(r_m).

### A2. The normalization N2 — **GoodTop ⟺ CertAtom** (paper, complete; checked by `dmax_check.py` on 192 stored models)
For F ∈ W0^desc define F′: rows ⊥ and atoms of Z unchanged; rows x ∉ Z constant ⊤; for m ∈ M2 and high y,
F′(m, y) = ⋀{u_{j+1}(m) : y ≤ u_j(m)} = F(m, σ_m(y)), where σ_m(y) is the least element of row m's descent that is ≥ y
(the descent is a finite chain containing ⊤); for m ∈ M2 and y of height ≤ 2, F′(m,y) = F(m,y).
1. *Monotone in y* at m: y ≤ y′ both high ⟹ σ_m(y) ≤ σ_m(y′); y low, y′ high: F(m,y) ≤ F(m,y′) ≤ F(m,σ_m(y′)).
2. *Monotone in x*: atom/⊥ q ≤ m: F(q,y) ≤ F(m,y) ≤ F(m,σ_m(y)) = F′(m,y) (σ_m(y) ≥ y). Rows above a row of Z are either
   outside Z (constant ⊤) or, for m ∈ M2, do not exist inside Z (heights ≤ 2). Rows outside Z: ⊤.
3. *Same Z, same a(⊥)*: row ⊥ unchanged. *Same descents*: for every j, F′(m, u_j(m)) = F(m, u_j(m)) (σ_m(u_j(m)) = u_j(m)
   when u_j(m) is high; F′ = F at low columns). So λ, i, exits, c and μ are unchanged; NoFix is unchanged.
4. *Ta at m*: y high, σ_m(y) = u_j. If u_{j+1} ≠ u_j then y ≰ u_{j+1} (else σ_m(y) ≤ u_{j+1} < u_j). If u_{j+1} = u_j then
   u_j = a(m) ≥ y has height ≥ 3, against Ta(m) in F (`ta_iff_lands`, a(m) ≤ every descent element). So y ≰ F′(m,y).
5. *Tb at m*: y high ⟹ σ_m(y) = u_j high and F′(m,y) = u_{j+1}. If u_{j+1} is high it is not ≤ m (height). If not, u_j is
   r_m and u_{j+1} = λ(m) ≰ m (W0^desc). So F′(m,y) ≰ m.
6. *F′ ∈ W0*: R′_1 = Z. R′_2 = ↓(Z ∪ a′(Z) ∪ b′⁻¹(Z)): a′(x) = a(x) has height ≤ 2 (Ta); if b′(y) ∈ Z then
   F′(b′(y), y) ≤ b′(y) with b′(y) a row of Z, so y is low by Tb′. Hence R′_2 tight, ⊤ ∉ R′_2 (h(⊤) ≥ 3), R′_1 not tight (n1).
**Corollary.** If CertAtom holds for every F in W0 on a lattice, it holds for every F in W0^desc on that lattice (apply
it to F′: same μ). And CertAtom on W0^desc is GoodTop (contrapositive + `selfLow`). With `certAtom_of_goodTop`:
**GoodTop ⟺ CertAtom**, as statements quantified over all F on a given lattice (F′ is another F on the same lattice;
lattice coordinates H, width, N are unchanged). The
same map preserves exits, so **G1 ⟺ ExitZ(W0)** and **G2 ⟺ ExitToFix(W0)** (W0 ∧ some exit ⟹ CertAtom): the G1/G2 normal
form is the ExitZ/ExitToFix split already filed `collapses` (brief run 3), transported by `selfLow`.
**Why it works at height-2 rows and not at atom rows.** No row of Z lies above an M2 row, so the raise in step 2 meets only
rows outside Z, which are free. Raising an atom row q would have to stay below the rows m ≥ q of M2, whose descents are fixed;
that is the role table's desc1 failure (79/82, brief289 run 1; 58/62 here, run 4).

**Verdict asked of the worker: GoodTop is a `restatement` (disguised target).** Its pushes are CertAtom's pushes on the
same lattices. The open step "GoodnessTransfer" is CertAtom. The 49/50 "no exit" statistic, "every landing type occurs",
"the witness is not λ(⊥)", and every other W0♭ ∧ NoFix observation describe models that have a witness; by N2 a model of
the target's counterexample world has none. They do not bear on the target. (Stored W0 models: all 190 distinct ones have
an exit — samples only.)

### A3. Normal form DMax (paper, complete; `dmax_check.py`: 190 W0 + 2 W0^desc∖W0 stored models, all checks pass)
For F ∈ W0^desc define F♯: row ⊥ unchanged; rows outside Z constant ⊤; for x ∈ Z ∖ {⊥}
  F♯(x, y) = ⋀{u_{j+1}(x′) : x′ ∈ Z, x ≤ x′, j ≥ 0, y ≤ u_j(x′)} = ⋀_{x′ ∈ Z, x′ ≥ x} F(x′, σ_{x′}(y)).
Then F ≤ F♯ on the rows of Z, F♯ is monotone, has the same Z and the same descents of every row of Z (hence the same μ),
and F♯ ∈ W0. *Proof sketch (each step as in N2).* Monotone in y: each σ_{x′} is monotone. Monotone in x: a smaller row
ranges over more x′; F(⊥,y) ≤ F(x′, σ_{x′}(y)). F ≤ F♯: F(x,y) ≤ F(x′,y) ≤ F(x′,σ_{x′}(y)). Descents: F♯(x,u_j(x)) ≤
F(x, u_j(x)) = u_{j+1}(x) (take x′ = x) and ≥ by F ≤ F♯. Ta: F♯(x,y) ≤ F(x,σ_x(y)) ≱ y (step 4 of N2). Tb at atom rows:
F♯ ≥ F and Tb(F). Tb at M2 rows: F♯(m,y) = F(m,σ_m(y)) (only x′ = m), step 5 of N2. ∎
**Design rule this proves (replaces the §7 rule on file).** Since F♯(q, y) ≥ F(q, w) for w = ⋀_{x′ ∈ Z, x′ ≥ q} σ_{x′}(y):
CertAtom(W0) is equivalent to CertAtom in the world **W0^meet** where Ta holds as "every row of Z lands", Tb at M2 rows as
λ(m) ≰ m, Tb at ⊥ as ZT, and Tb at an atom row q only at high columns of the form ⋀_{x′ ∈ Z, x′ ≥ q} c_{x′} with c_{x′} on
row x′'s descent (⊤ allowed). Every value of a row of Z is then an infimum of descent successors: CertAtom is a statement
about the descent data (φ, (desc x)_{x∈Z}) alone.

### A4. μ-normal form (paper, Lean-ready) — *MuLow*
In W0♭: (∃ m ∈ M2, λ(m) = m) ∨ CertAtom ⟺ μ has a fixed point in Z ∖ ⊥ ⟺ Low ≠ ∅, Low := {x ∈ Z∖⊥ : μ(x) ≤ x}; and
Low = Z ∩ ↑Fix(μ). *Proof.* x ∈ Low with λ(x) ∈ Z: x is not an atom (λ(x) = F(x, r_x) ≤ x is a high lower cell, against
Tb), so x ∈ M2 and `selfLow` gives λ(x) = x. With an exit: c(x) ≤ x and `domCoLand` (Tb at c(x) only) makes c(x) fixed
(this is `exitFixed_of_dom` with `tb_of_tight` replaced by the W0♭ hypothesis). Conversely a fixed atom c ≤ x ∈ Z makes x
exit to c (`upTrap_land` with Tb at c and Ta at x, as in `certAt_of_fixed_below`). ∎ (The W0♭ form of `exit_atom` needs
only λ(x) ≠ ⊥, which ZT gives: λ(x) = F(x,r_x) = ⊥ ⟹ φ(r_x) = ⊥.)

### A5. The M2-row mechanism (paper, Lean-ready) — *Swap*, *ConfLand* (ConfLand generalizes `selfLow`)
- **Swap.** W0♭, m ∈ M2, y high, F(q,y) ≤ m for every atom q ≤ m ("y is m-confined") ⟹ m ≤ F(m,y). *Proof.* Take an atom
  q1 < m. F(q1,y) ≠ ⊥ (φ(y) ≠ ⊥), ≰ q1 (Tb), ≤ m: so F(q1,y) = m (done) or an atom q2 ≠ q1. Then F(q2,y) ≤ m, ≠ ⊥ and
  ≰ q2, so F(q2,y) is m or an atom other than q2; either way F(m,y) ≥ F(q1,y) ∨ F(q2,y) = q2 ∨ F(q2,y) = m (a join of two
  distinct nonzero elements of ↓m, one an atom, has height 2). ∎
- **ConfLand.** W0♭, m ∈ M2, z on row m's descent with m < z and z m-confined ⟹ λ(m) = m. *Proof.* Every later descent
  element ≥ m: if u_j > m it is high and ≤ z, so confined, and Swap gives u_{j+1} ≥ m. The descent ends at a(m), height ≤ 2
  (Ta), so a(m) = m and m is on its descent; earlier elements are > m, hence high. ∎ (`selfLow` is the case z = r_m.)
- Free check `lemma_check.py`: Swap, Bcell, ConfLand, MuLow, Low = ↑Fix, "self-landing m = b(r_m)" hold on all 258
  stored W0♭ models.

### A6. Placement of the rungs on file (re-derived)
- `certAtom_of_goodTop`: correct; by A2 the arrow is an equivalence.
- "G1 in W0 gives ExitZ": correct; by A2, G1 ⟺ ExitZ(W0) exactly.
- "DescTb2: CertAtom survives it": now a theorem (A2), not data.
- Column ladder (A1 + A2): target ⟺ [W0♭ ∧ NoFix ⟹ some m ∈ M2 has F(m,y) = m at some high y]; GoodTop pins y = r_m;
  LfpCol (y = r_x for some x ∈ Z) and LfpY (y on some descent) lie between and are all equivalent to the target by A2.
- TopExit/TopCert/FixBelow, AtMost1Fix, FixMax, N1: unchanged.

## 3. Failure signature (recomputed) and constraints

On file: every refuted route predicts where the certificate sits; the fixed set was argued about only where non-empty.
**Widened:** *the last two rounds relaxed a hypothesis that a landing-preserving deformation restores.* W0♭ adds to W0 only
models with a witness (A2); NoFix "has models" there only because the witness absorbs it. Every located step of §290 (S2, X,
DWitness) and the §290 statistics live on those models. **Inversion:** normalize first (A2, A3); relax only what the normal
form cannot restore — Tb at atom rows at meet columns — and argue there.
**Sharpness boundary** (refined): Tb at atom rows cannot be cut down to the atom's own descent (desc1: SAT on 58/62, run 4);
it can (conjecturally) be cut to two-row meets (TwoRowTb: no counterexample on 68 lattices, runs 4–5). Branch g and dropping R_2 tightness as on file.
**Testability.** CertAtom is a stage form, finitely refutable. Contradiction-mode lemmas need a relaxation with models that
N2/DMax cannot normalize away: desc1-type relaxations of the atom rows qualify, W0♭ does not.

## 4. Reuse (real names; `LateParent.lean` unless noted)
`selfLow`, `not_good_of_ahead`, `trap_of_tb`, `domCoLand`, `upTrap_stay`, `upTrap_land`, `exitFixed_of_dom`,
`certAt_of_fixed_below`, `exit_atom`, `land_not_le`, `land_unique`, `ta_iff_lands`, `tb_of_tight`, `rowDesc_reaches_a`,
`a_le_rowDesc`, `iter_antitone_of_le`, `iter_row_mono`, `certAtom_of_goodTop`, `GoodTop`; `b`, `b_le`, `le_a`, `row_a`
(`Derived.lean`); `mem_succ_of_cell` (`OrbitHeight.lean`); `mem_succ_of_b` (`SingletonLowerTransfer.lean`); `Rk_succ`,
`Rk_down` (`Orbit.lean`).

---

## 5. LEAD — DMax and TwoRowTb: which Tb instances existence uses (normal form + hypothesis anatomy)

**Candidate lemma (conjectural) TwoRowTb.** Let L be finite, F monotone, a(⊥) = ⊥, ZT, n1, h(⊤) ≥ 3, every row of Z lands,
λ(m) ≰ m for m ∈ M2, and for every atom q of Z: F(q, u ⊓ v) ≰ q whenever u is on row q's descent, v is on the descent of a
row x ∈ Z with q ≤ x, and u ⊓ v is high (u = ⊤ or x = q allowed). Then some atom of Z is μ-fixed.

**Conditional payoff (complete).** W0 ⊆ W0² (W0 has Ta and full Tb at every row of Z, `tb_of_tight`) ⟹ CertAtom ⟹
GoodAtom1 (`goodAtom1_of_cert1` with Cert1 ⟺ CertAtom) and GoodTop (A2). Beyond existence it fixes the proof's diet: the
only Tb instances used are two-row meets — exactly those `trap_of_tb` consumes in `domCoLand`, `goodUp`,
`land_of_good_below`, `certAt_of_fixed_below` (there x := q and r is on the row-q or row-m descent). By A3 one may moreover
assume F = F♯, so every cell value is an infimum of descent successors.

**Placement.** Strengthening of the target to the larger world W0² ⊇ W0^meet ≡ W0 (A3). Between: W0^meet (all meets, ≡
target) ⊆ W0² (meets with at most one factor off row q) ⊆ desc1 (only row q's own descent; CertAtom fails there).
**Testability.** Finitely refutable: an existence statement in the world W0² (which contains W0, so it has models on every
lattice); a counterexample is a model of W0² ∧ NoFix, which N2/DMax cannot normalize into W0 (F♯ does not restore Tb at
3-row meets). **Hypothesis world:** W0², the target's world with the Tb instances at meets of three or more descents dropped
at atom rows; its counterexample branch is empty on every lattice run, while the calibrated mutant's world desc1 ∧ NoFix has
models on 58/62 base lattices (branches a 28, b 27, g 3).
**Counterexample anatomy.** An atom q with at least two M2 rows above it in Z whose descents, together with q's, meet in a
high column w not of the two-row form, with F(q,w) ≤ q the only escape from a fixed atom. Room dimensions: k = number of
height-2 elements above one atom (corpora reach k 1–7, `corpus_coords.txt`), height, width, N. Smallest coordinates unknown.
**Mode.** Ladder audit (DMax) + signature inversion (the normal form is the set-level object; no row or column is
predicted). **Limit.** Does not prove existence; it removes hypotheses and canonicalizes F. If TwoRowTb fails at room, the
3-row meets are needed and the refutation is the anatomy a proof must handle.
**Decisive open step (named): MeetViolation.** In W0² with F = F♯ and NoFix, exhibit an atom q, a row x ∈ Z above q and
descent elements u ∈ desc(q), v ∈ desc(x) with u ⊓ v high and ⋀_{x′ ∈ Z, x′ ≥ q} F(x′, σ_{x′}(u ⊓ v)) ∈ {⊥, q}. The
dominated-exit case is already this (`exitFixed_of_dom` → `trap_of_tb`); the open cases are (i) no row of Z exits (ExitZ,
= G1) and (ii) every exit atom lies outside its row (c(x) ≰ x for every exit x).

**Probes.** Bank replay: the statement holds on the 30 W0 + n1 bank models (each has a fixed atom: `bank.py replay
CertAtom`, and W0 ⊆ W0²); no stored model is a W0² ∧ NoFix model. Runs 4 and 5 (§8).

## 6. Other programmes

### P2 — LfpMin: the target in column form, with the forced cell at a minimal descent column
- **Candidate (conjectural).** In W0♭ with NoFix, some minimal element y of Y := {high elements on the descents of rows of
  Z} has b(y) ∈ Z (equivalently, A1: some m ∈ M2 has F(m,y) = m).
- **Payoff (complete).** In W0, b(y) ∈ Z = R_1 gives y ∈ R_2 (`mem_succ_of_b`), so h(y) ≤ 2: contradiction. Hence
  LfpMin ⟹ CertAtom. (Lean: a few lines.)
- **Placement.** LfpMin ⟹ LfpY ⟺ CertAtom (A2). It is *above* the target: by A2 the slice where it says more than the target
  consists of witness models, which the target does not need. Not implied by GoodTop on paper.
- **Testability / world.** Finitely refutable in W0♭ ∧ NoFix (models on every lattice); its content beyond the target is
  on witness models only. **Anatomy.** A W0♭ ∧ NoFix model whose fixed M2 cells sit only at non-minimal or off-descent
  columns; needs |Ymin| ≥ 2 or Y with two levels (59 of 61 stored no-exit models have |Ymin| = 1). Room: H, M, N.
- **Mode.** Signature inversion to the lfp side (an ascent ⊥ < φ(y) ≤ F(φ(y), y) of at most three elements in Z) + an
  extremal choice whose extremality is used (every row of Z through a minimal y lands right after it, so φ(y) ≤ λ(x) ∈ Z in
  the no-exit case). **Limit.** Located strengthening; low priority after A2. **Decisive step:** for y ∈ Ymin, produce
  m ∈ M2 with φ(y) ≤ m = F(m,y). The mechanism "the ascent runs along rows through y" (AscentRows) is refuted by 5 stored
  models (`cex/ascentrows_*.json`).
- **Probes:** runs 1–3, §8. Refuted relatives banked: LfpMinAll (every minimal column), LfpLand (b(y) a witness with y on its
  descent).

### P3 — DescentData: an exact tester over descent families (finite abstraction; infrastructure)
- **Candidate (normal form, proved on paper: A3).** A family (φ; desc x for x ∈ Z) is realized by some F ∈ W0^meet iff F♯
  built from it is monotone, reproduces every chain (F♯(x, u_j(x)) = u_{j+1}(x), i.e. for x ≤ x′ in Z:
  F(x′, σ_{x′}(u_j(x))) ≥ u_{j+1}(x), and u_{j+1}(x) ≥ φ(u_j(x))), lands, has λ(m) ≰ m, and satisfies Tb at atom rows at meet
  columns. **Payoff.** The search ranges over chain families (one chain per row of Z) instead of n²-valued tables, which is
  where height and width room are currently capped (H 14, M 7; one |L| 75 lattice took about 17 minutes in run 3).
- **Placement:** ≡ CertAtom (A3). **Testability:** equivalence check against `orbit_probe.py` on shared lattices.
  **Mode:** canonical form / finite abstraction. **Limit:** no existence argument. **Decisive step:** an encoding of
  "chain family realizable" with O(|Z|·h(⊤)) choice variables.

**Observations (samples only; not programmes).** On all 258 distinct stored W0♭ models μ has exactly one fixed point in
Z ∖ ⊥ (190 W0: one fixed atom; 66 witness models: one witness; 2 others: one fixed atom). By A2 the witness half concerns the
slice, so this adds only AtMost1Fix on W0 (pushed, corollary side). In the 66 witness models the witness is μ(d) — a
⊥-anchored location whose W0 analogue (BotOrbit) is refuted: do not pursue.

## 7. Probe scripts (this directory; run with PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation)

- `world.py` — independent checker of W0♭ / W0 / NoFix / landings / b from the definitions; loader of every stored model JSON
  in the repository (read-only). `census.py`, `feat1.py`–`feat11.py`, `lemma_check.py`, `dmax_check.py`, `save_cex*.py`:
  free replays of stored models (no search). `pred_lfpmin*.py`: `bank.py replay --file` predicates.
- `lfp_probe.py` — exact SAT, one-hot rows of height ≤ 2; world W0♭ (a(⊥) = ⊥, ZT, n1, Ta at Z rows, Tb at atom rows); modes
  `lead` (SAT = NoFix ∧ every y ∈ Ymin has b(y) ∉ Z: LfpMin fails), `mutA` (SAT = NoFix ∧ some y ∈ Ymin has b(y) ∉ Z: the
  refuted relative LfpMinAll), `gt` (SAT = NoFix ∧ no self-landing: GoodTop fails, control), `uniq`, `mutU`, `nofix`; flags
  E1–E6 (exact N), maxn. Y is encoded by w(x,j,y) ↔ Z(x) ∧ it(x,j,y); b(y) ∉ Z as "no x ∈ Z with F(x,y) ≤ x".
- `meet_probe.py` — exact SAT; common world a(⊥) = ⊥, ZT, n1, Ta at Z rows, λ(m) ≰ m at M2 rows; Tb at atom rows only at the
  columns of the mode: `w0d` (all high columns; control), `two` (u ⊓ v, u ∈ desc(q), v ∈ desc(x), x ∈ Z, q ≤ x; the lead),
  `desc1` (q's own descent; calibrated mutant). SAT = NoFix in the mode world. Flag E<k>, maxn.
- Every SAT model of both testers is decoded and replayed in Python from the definitions (`world.W`) — an assertion aborts
  on mismatch; every output prints the quantifier, the SAT meaning and per-lattice progress.
- Smokes (0–1 s, `smoke/`): 3 bank lattices for `lfp_probe.py`, 2 lattices for `meet_probe.py` (desc1 reproduces brief289's
  desc1 refutation on its own lattice, |L| 10).

## 8. Runs and report lines (budget: 5 exact runs, each ≤ 1500 s, ≤ 2 in parallel)

| run | command (cwd `runK/`) | wall |
|---|---|---|
| 1 | `lfp_probe.py lead,mutA,gt calib tall 12 4 1 1` (calibration, one lattice |L| 52, H 12) | 178 s |
| 2 | `lfp_probe.py lead,mutA base closure 5 11 4 30 + tall 8 4 1 12 + tall 10 4 2 20` | 352 s |
| 3 | `lfp_probe.py lead,mutA room tall 13 4 1 8 + tall 10 7 1 5` | 1500 s (cap; 11 of 13 lattices) |
| 4 | `meet_probe.py two,desc1 base closure 5 11 4 30 + tall 8 4 1 12 + tall 10 4 2 20` | 616 s |
| 5 | `meet_probe.py two,desc1` on `tall 10 6 1 8 maxn 55`, then `tall 13 4 1 8`, then `tall 12 4 1 8 E4 maxn 45`, `E5` (one job, one cap) | 1500 s (cap; 6 M6 lattices, 0 of H 13) |

```
TwoRowTb (LEAD) | meet_probe.py two (exact) | exists F in W0^2: SAT = NoFix (existence fails with Tb at atom rows only at
                  two-row meet columns u ⊓ v, u ∈ desc(q), v ∈ desc(x), x ∈ Z, q <= x)
  run 4: closure 5 11 4 30 + tall 8 4 1 12 + tall 10 4 2 20 — 62 lattices, H 4/5/8/10, |L| 9–50, width 3–12, k 1–5
     candidate SAT 0/62 | mutant desc1 (refuted relative, brief289 run 1) SAT 58/62: branch a 28, b 27, g 3; N 1–3, 5, 6
  run 5: tall 10 6 1 8 maxn 55 — 6 lattices finished (|L| 35–54, H 10, width 8–15, k 3–5); then capped at 1500 s inside
     tall 13 4 1 8 (no H-13 lattice finished; exact-N parts E4/E5 not reached)
     candidate SAT 0/6 | mutant desc1 SAT 6/6: branch a 2, b 4; N 1–2
  stored-model replay (free, replay_two.py): candidate in its world on 200 stored models, 0 failures; desc1 fails on 10
  room reached: H 10, width 15, k 5, N up to 6 (mutant models; not controlled) | anatomy needs: an atom with >= 2 rows of
     M2 above it (k >= 2: present on 29/30, 12/12, 19/20, 6/6 lattices) and a 3-row meet column; smallest unknown
  branch a: mutant models 30 lattices | candidate failures 0 | mutant failures 30
  branch b: mutant models 31          | candidate failures 0 | mutant failures 31
  branch g: mutant models 3           | candidate failures 0 | mutant failures 3
          -> provisional in H (<= 10), width (<= 15), k (<= 5); one encoding (this briefer's); N, H 13–14, M 7 owed
LfpMin (P2) | lfp_probe.py lead (exact) | exists F in W0-flat: SAT = NoFix and every minimal descent column y has b(y) ∉ Z
  run 1 (calibration): tall 12 4 1 1 — 1 lattice, |L| 52, H 12 | lead SAT 0/1 | mutant LfpMinAll SAT 1/1 (b, N 1) |
     control gt (GoodTop fails) SAT 0/1
  run 2: base corpus as run 4 — 62 lattices | lead SAT 0/62 | mutant SAT 60/62: a 14, b 36, g 10; N 1–2; exit 8, no exit 52
  run 3: tall 13 4 1 8 (8/8, H 13, |L| 33–58) + tall 10 7 1 5 (3 of 5 finished: |L| 75, 42, 49, width 21, 10, 13), capped at
     1500 s | lead SAT 0/11 | mutant SAT 11/11: a 3, b 5, g 3; N 1, 2, 7
  room reached: H 13, width 21 (M 7, 3 lattices), N up to 7 (mutant; not controlled) | anatomy needs: |Ymin| >= 2 or a
     second level of Y (unknown smallest)
  per branch: mutant failures a 17, b 42, g 13; candidate failures 0 on every branch
          -> provisional (H <= 13, M 7 partial); one encoding; exact N owed; placed above the target (A2)
GoodTop control | lfp_probe.py gt | run 1 only (1 lattice): UNSAT, agrees with lead2_probe / orbit_probe on file
```

**Models saved.** Smallest SAT model per mode and run (`runK/*_min*.json`; runs 3 and 5's H-13 part were stopped at the cap
before their summary, so run 3 has no saved mutant model); all SAT models of the candidate and control modes `two`, `lead`,
`gt` would have been saved (none occurred). `run1/run1_console.txt` also holds a 1-lattice exact-N smoke (`lead` E1–E3 on
the s290 lattice, 0 s). Modes `uniq`/`mutU` (AtMost1Mu) were only smoke-tested. The full sets of mutant SAT models were not stored (only the smallest per run); they are reproducible
(seeded corpora, deterministic solver). Refuting stored models, with statement and coordinates: `cex/*.json`.

## 9. Pushes owed
- TwoRowTb: independent encoding (worker); H 13 (`tall 13 4 1 8`, not reached in run 5) and H 14 (`tall 14 4 2 20 maxn 45`);
  width M 7 / k 6–7 (`tall 10 7 1 5`); exact N = 4, 5, 6 (`meet_probe.py … E4` etc. on `tall 12 4 1 8 maxn 45`). At |L| ≥ 50
  the one-hot encoding needs 1–6 minutes per lattice per mode (run 5); P3 would remove that limit. Sharpness probe owed: **OneRowAbove** (Tb at q
  only at single descent elements of rows x ∈ Z above q, no meets) — the next weaker world between desc1 and W0².
- LfpMin: exact N; H 14; width M 7 (run 3's M7 lattice did not finish).
- A2/A3: formalize (they settle the GoodTop question without search).

## 10. Already failed — do not repeat
All of frontier §4, plus: GoodTop/GoodnessTransfer as a reduction (A2: restatement); every located step on W0♭ witness
models (S2, X, DWitness, μ(d)-witness); LfpMinAll and LfpLand (stored models `cex/direct290_nf_t8.json_4.json`,
`cex/direct290_nf_cl.json_18.json`; mutant runs 1–3); AscentRows (5 stored models); "the witness is maximal in Z" (vacuous:
no element of Z lies above an M2 element).

## 11. Hard constraints
- Ta is used only as landing; Tb at M2 rows only as λ(m) ≰ m; Tb at atom rows only at meets of descent elements of rows of
  Z above the atom (A3, theorem). Tb at atom rows cannot be reduced to the atom's own descent (desc1: SAT 58/62).
- Only rows x ∈ Z with x ≥ q enter the meet columns of A3; meets with the ⊥-descent (as in `breakExists`) are not needed.
- Sharpness on file (branch g; R_2 tightness) unchanged.

## 12. Formalization order (no sorry, no new axioms)
1. `Bcell` (A1) and the W0♭ form of `exit_atom` (hypothesis λ ≠ ⊥ from ZT instead of `hk2`).
2. `swap`, `confLand` (A5); check `selfLow` as a corollary.
3. N2 (A2): define the normalized family with `sInf {(F m)^[j+1] ⊤ | y ≤ (F m)^[j] ⊤}` at M2 rows (monotonicity is then
   immediate), prove descents preserved and the W0 hypotheses of `certAtom_of_goodTop`; conclude
   `goodTop_of_certAtom` (as a statement over all F) and hence GoodTop ⟺ CertAtom.
4. DMax (A3) as the same construction with the infimum over x′ ∈ Z above x.
5. MuLow (A4). 6. LfpMin payoff via `mem_succ_of_b`. 7. Then the open step MeetViolation.

## 13. Expected report
Lead: A2 `restatement` verdict for GoodTop + `normal form` for N2/DMax (Lean); TwoRowTb `provisional` → `new conjecture`
(pushed) or `refuted` (banked). P2: `provisional`, placed above the target. P3: infrastructure (`normal form` if the tester
agrees with `orbit_probe.py`).

## 14. Frontier corrections
1. **§2 ladder**: "CertAtom (W0) ⟸ GoodTop (W0♭) [P]; GoodTop: new conjecture, pushed" — GoodTop ⟺ CertAtom (A2, paper
   complete). Reclassify GoodTop as a restatement (disguised target); its pushes are CertAtom's.
2. **§2 OPEN TARGET line**: "GoodnessTransfer — the open step" is CertAtom itself, not a step below it.
3. **§2 G1/G2**: G1 ⟺ ExitZ(W0), G2 ⟺ ExitToFix(W0) (A2); the split is the ExitZ/ExitToFix split filed `collapses`.
4. **§2 samples** ("49 of 50 … no exit", "every landing type occurs", "witness not λ(⊥) in 5 of 8", "does not stall in 4 of
   8"): all are W0♭ models with a witness, outside the target's counterexample world (A2). Delete or mark irrelevant. All 190
   distinct stored W0 models have an exit (samples).
5. **§2 DescTb2 bullet / §7 role table**: "CertAtom survives DescTb2" is a theorem (A2), not data; the desc2 column (0/82,
   0/78) is explained.
6. **§7 design rule** "Tb at the height-2 rows only through not_good_of_ahead / land_not_le": now a theorem; add the A3 rule
   (Ta only as landing; Tb at atom rows only at meet columns of descents of rows above the atom).
7. **§9 vacuity map**: "NoFix … in W0♭ has models on every lattice tried" — every such model has a witness (if CertAtom
   holds); W0♭ is not a relaxation that gives the target's contradiction-mode lemmas models. desc1 is (58/62, run 4).
8. **§1**: add W0♭ ∖ W0 = {some m ∈ M2 has F(m,y) = m at a high y} = {b(y) ∈ Z for some high y} (A1).
9. **§3 buckets**: add paper lemmas Bcell, Swap, ConfLand (generalizes `selfLow`), MuLow, N2, DMax (all Unverified until
   formalized; free checks on 192–258 stored models in this directory).
10. **§4 refuted**: add LfpMinAll, LfpLand, AscentRows (`cex/`), each W0♭ ∧ NoFix, H 5–12.
11. **§5 bank count**: `bank.py replay` reports 30 W0 + n1 models and 15 others (45), not 14 others.
12. **§6 room vector**: add k = number of height-2 elements above one atom (Tb-instance statements; corpora reach k 1–7).
13. **§2 "witness … not λ(⊥)"**: on all 66 distinct stored witness models the witness is μ(d); a ⊥-anchored location on the
    slice — record it so it is not pursued (W0 analogue BotOrbit refuted).
14. **§10 corpora**: `tall 10 7 1 5` needs about 1000 s for its |L| 75 lattice (two modes, LfpMin encoding, run 3) and
    `tall 10 6 1 8` 1–6 minutes per lattice (run 5); add these speeds.
15. **§2 "Paper (W0♭, no exit)" facts** are facts about witness models; keep only those used in a proof.
16. **§8 set-aside choices**: add "relaxing Tb at the height-2 rows (W0♭)" as set aside, reason A2 (undone by N2).
