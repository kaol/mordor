# Brief run 25: thin colours closed in Lean; the open case is a pair of colours joined inside Z

**Repository:** /home/user/mordor at 07c9506. The briefer read it read-only and nothing in the checkout was changed.
**Work dir:** `/tmp/claude-0/-home-user/3b6fdd2c-c95c-5c07-b47c-6ae28c687a4c/scratchpad/amr_run25/brief/`. It holds this
file, `ThinColour.lean`, `probes/`, `runs/` and the Lean scratch copy `leanw/`.

**Mission.** The refuted routes each predict *where* the certificate sits. This brief does not. It carries a colour
**set** along a staircase and lets a capture lemma do the work. The certificate is never located. The contradiction comes
from all landings sharing one exit colour, or from one universal colour.

---

## 0. Result first (verdict asked: `proves`)

**`certAtom_of_thin`** (new Lean, compiled in the scratch copy, axioms propext / Classical.choice / Quot.sound, no
`sorry`). In W0, suppose no element of Z lies above two distinct colours ("thin"). Then some atom of R_1 is μ-fixed.
- This holds for any number of colours and any N.
- Two colours with no common upper bound in Z are thin. So `certAtom_of_twoColours` is the case |𝒜| = 2.
- File: `ThinColour.lean`, to go in `lean/Mordor/`; it imports `Mordor.TwoColourShadow`.
- Build: `lake build Mordor.ThinColour` in `leanw/` gives 1287 jobs, OK. `AxCheck_ThinColour.lean` prints the axioms
  (`lean_thin_axioms.txt`).

New declarations:

| name | statement |
|---|---|
| `land_capture` (**GK0**) | if c ≤ (F x)^[i] ⊤ and A ≤ F(⊥, A) ⊔ c, then A ≤ (F x)^[i] ⊤. Any row x, any i. It is `desc_ge_of_postfixed` with Q = A |
| `join_of_two_atoms` | two distinct atoms below an element of height ≤ 2 join to it, and it has height 2 |
| `phi_low_colour` | if A is low, A ∉ Z and φ(A) ≤ A, then φ(A) is a colour and h(A) = 2 |
| `shadow_start` | under NoFix, a landing row y has a colour c with c ≤ λ(y) and c ≤ φ(r_y) |
| `thinStair` (**SCL**, thin form) | for landing rows x and y (any elements), if a colour of λ(y) lies below φ(r_y), then a colour of λ(y) lies below φ(r_x) |
| `colourStair` (**SCL**, general form) | as `thinStair`, with thinness replaced by `hnb`, i.e. NoPairBreak at the corners of this one staircase: a corner (F x)^[j] ⊤ ⊓ (F y)^[m] ⊤ in Z that carries a colour of λ(y) carries only colours of λ(y). This is D1's exact Lean interface |
| `certAtom_of_thin` | thin ⟹ CertAtom (W0) |

**Paper proof.** K(y) := the colours below λ(y); r_y is the last high element of row y's descent; e(y) := φ(r_y).
1. **GK0 (capture).** Let A ∉ Z be low and c ≠ φ(A) an atom below A. Every row whose landing lies above c lands at A.
   - Since F(x, A) ≥ φ(A), we get A = c ⊔ φ(A) ≤ F(x, A) ⊔ c.
   - `desc_ge_of_postfixed` starts the induction at ⊤.
   - Lemma K of §298 is this lemma. It needs no index m at which A lies below the descent.
2. **SCL.** Walk the `pairStair` staircase of rows x and y with value row ⊥, from the y end. The invariant is "some
   colour c ∈ K(y) lies below the boundary value e_l".
   - Start: `shadow_start`.
   - At a low corner A ∈ Z, e_{l+1} is a colour of A or is A itself. Thinness keeps the colour in K(y).
   - At a corner A ∉ Z, φ(A) ≤ e_{l+1} is a colour. If it were outside K(y), GK0 at c would give A ≤ λ(y), so φ(A) ∈ K(y).
   - The last boundary value lies below e(x).
   - The A ∈ Z branch is the **only** use of thinness. Without thinness, the invariant can break only at a corner
     A ∈ Z of height 2 with C(A) ∩ K(y) ≠ ∅, C(A) ⊄ K(y), and e_{l+1} ∈ C(A) ∖ K(y). Call such a corner a *pair-join
     break*.
   - Replay (free, `probes/scl_check.py`): 0 violations of this break claim over 41,103 ordered row pairs of the 291
     stored NoFix models (holding/cgall_*, ColourGraph_R3, s299). All 640 breaks are of that kind.
3. **Case A: some colour row a lands in Z.** Then e(a) ∈ Z carries a single colour c₀.
   - SCL with x = a and any colour row y gives c₀ ∈ K(y).
   - So c₀ ≤ λ(c₀).
   - If λ(c₀) ∈ Z, thinness contradicts ColourGain at c₀.
   - Otherwise λ(c₀) = c₀ ⊔ c*, with exit colour c* ≠ c₀. Row c* lands above c₀, so GK0 gives λ(c*) = λ(c₀) and c* is
     μ-fixed.
4. **Case B: every colour row exits.** Let a be a colour row and y any colour row.
   - SCL gives a common colour of λ(a) and λ(y).
   - By GK0, two distinct exit landings share only their common exit colour.
   - So every colour row exits to one colour s, and row s exits to s: s is μ-fixed.

**What it uses.** ZT, a(⊥) = ⊥, landing and ColourGain at the colour rows, and NoFix at the colour rows.
- Given ColourGain at the colour rows as a hypothesis, it uses **no Tb at any row**. NoFix at a colour row's own landing
  is the definition, and `exitFixed_of_dom` in the Lean file is used only with x = q.
- In W0 the Lean proof obtains ColourGain from `colourGain`, whose proof (TopRow′) uses Tb at λ(x) and at x ⊓ λ(x).

**Two encodings** (briefer's `rowset_probe.py`, world `Lc Gc thin`; see §6):
- 0 SAT on 62 lattices: the 43 bank lattices of the refuted R3-any relative, and 19 lattices at H 10–14, widths 5–13,
  |L| ≤ 49.
- The calibrated mutant (same world without `thin`, i.e. P3 of §297) is SAT on 62/62.

**Ladder update proposed.**
```
CertAtom ⟸ Thin (no z ∈ Z above two distinct colours), any N, any |𝒜|   [P certAtom_of_thin]
certAtom_of_twoColours = Thin at |𝒜| = 2 (unbounded pair ⟹ thin)
OPEN: N ≥ 2, 𝒜 unbounded, |𝒜| ≥ 3, and some pair-join m = c ⊔ c' ∈ Z (c ≠ c' colours)
```

---

## 1. Frontier used (checked at source)

**Definitions.**
- φ = F(⊥, ·) and Z = φ⁻¹(⊥) = R_1. A colour is an atom of Z that is a value of φ; 𝒜 is the set of colours.
- λ(x) is the first element of height ≤ 2 on row x's descent from ⊤; r_x is the element just before it.
- x exits iff λ(x) ∉ Z, and its exit colour is φ(λ(x)).
- CertAtom: some atom q ∈ Z with λ(q) ∉ Z and φ(λ(q)) = q.
- C(z) is the set of colours below z, and K(y) := C(λ(y)).
- A **pair-join** is m ∈ Z with |C(m)| ≥ 2. It has height 2, and m = c ⊔ c' for any two of its colours.
- R* is the set of colour rows together with the pair-join rows.

**Established and used (Lean, checked).**
- `pairStair`, `colourGain`, `certAtom_of_topRow'`, `certAtom_of_boundedAtoms` (PairTrap.lean).
- `desc_ge_of_postfixed`, `twoColour_*` (TwoColour.lean).
- `twoColour_selfShadow`, `certAtom_of_le_two_colours` (TwoColourShadow.lean). Its staircase block is reused verbatim
  in `thinStair`.
- `exit_atom`, `land_bot_lt`, `land_not_le`, `exitFixed_of_dom`, `tb_of_tight`, `ta_iff_lands`, `land_index_pos`
  (LateParent.lean, section `Landing`).
- `exists_first_low` (StairB1.lean) and `mem_one_iff` (Normalize.lean).

**Exact open target.** CertAtom in W0 with N ≥ 2, 𝒜 unbounded in Z, |𝒜| ≥ 3, and at least one pair-join.

---

## 2. Ladder audit

1. **Lemma K is GK0 from ⊤.** `twoColour_selfShadow`'s `hK` takes an index m with J ≤ w_m. The statement holds from
   m = 0 for every row (`land_capture`).
   - Its general form is a capture law for exits. If A ∉ Z is a landing-height element and c ≠ φ(A) is an atom below
     A, then every row landing above c lands at A.
   - This is not on the ladder. It is the strongest single fact this round found. It also gives "distinct exit landings
     share at most their common exit colour".
2. **ShadowLemma and TwoColourCG are theorems.** The ladder lines marked "new conjecture, pushed" are proved
   (`twoColour_selfShadow`, `certAtom_of_twoColours`) and are now subsumed by `certAtom_of_thin`. Remove them.
3. **The §299 design rule is branch-specific.**
   - On the thin branch, existence needs neither Tb at any row nor ColourGain at height-2 rows, once ColourGain at the
     colour rows is given (paper proof above; runs 1–2).
   - The rule "Tb at atom rows + landing/ColourGain at height-2 rows" belongs to the non-thin branch.
   - Sharpened by run 3 (§6): there, the height-2 rows needed are exactly the **pair-join rows**, and Tb at the colour
     rows is used (run 5's no-Tc world is SAT).
4. **R3 ≠ "colour rows only".** The R3 world sets every row other than ⊥ and the colour rows to ⊤, so the other rows of
   Z do not land. The 42 P3 models, and every stored NoFix model of every relaxed world (291 models), are **non-thin**:
   0 thin (`probes/thin.py`). This is why colour rows sufficed at |𝒜| = 2 and seemed insufficient at |𝒜| ≥ 3.
   Thinness, not the count, is the divide.
5. **JointStuck stays a restatement.** No rung uses it.

---

## 3. Lead programme P1: PairSelf (the non-thin branch)

**Candidate lemma (conjectural, finitely refutable).** **PairSelf.** Let F be monotone on a finite lattice, with every
row other than ⊥ and R* unconstrained. Assume:
- a(⊥) = ⊥, ZT, n1, h(⊤) ≥ 3;
- 𝒜 unbounded in Z, |𝒜| ≥ 3, and a pair-join exists;
- every colour row lands, has ColourGain and Tb, and is not μ-fixed (NoFix);
- every pair-join row m lands and λ(m) ≰ m (Tb in descent form, `D_p`).

Then this world is empty. Equivalently: under the colour-row hypotheses, some pair-join row fails to land or lands
below itself.

**Conditional payoff (proof).** W0 ∧ NoFix ∧ non-thin ∧ unbounded lies inside PairSelf's world:
- landing: `ta_iff_lands` (Ta at rows of Z);
- ColourGain: `colourGain`;
- Tb at colour rows: `tb_of_tight`;
- λ(m) ≰ m: `land_not_le`.

So PairSelf ⟹ CertAtom on the non-thin branch. With `certAtom_of_thin` and `certAtom_of_boundedAtoms`,
**PairSelf ⟹ CertAtom.**

**Placement.**
- CertAtom ⟸ PairSelf (above).
- PairSelf is strictly stronger than the open case: it drops landing, ColourGain and Tb at every row of Z outside R*,
  and keeps only the descent form at the pair-join rows.
- Known conditions do not imply it.
- It is not on the W0♭/nrmHom restatement list: the §299 UNSAT worlds have Tb at **all** atom rows and landing at
  **all** Z-rows, and PairSelf has neither.
- It is the |𝒜| ≥ 3 analogue of TwoColourCG.

**Testability.** Finitely refutable (exact per lattice).
- **Hypothesis world:** the non-thin branch.
- The world has no model wherever PairSelf holds, which is the point: it is a statement of emptiness.
- **Relaxations** with models, so the rule of §2 applies:
  - drop `D_p`: SAT (60/60 run 3 mutant, 63/63 run 4 mutant, 48/55 run 5 mutant);
  - drop Tb at the colour rows: SAT (run 5).
  - So any proof uses both, as below.

**Probes (exact; mutant = the §299 colour-rows + TbA world, the nearest refuted relative, restricted to non-thin).**

| run | world | corpus | lead SAT | mutant SAT |
|---|---|---|---|---|
| 3 | `Lc Gc Tc Gp Tp` (ColourGain and Tb at pair-joins) | closure 6 12 1 40, tall 8 4 1 12, tall 10 4 2 20 (maxn 40); H 4–10, width 4–12 | **0/60** | 60/60 |
| 3 | `Lz Gc Gp Tq Tp` (every Z-row lands, Tb at every atom) | same | 0/60 | — |
| 4 | **PairSelf** `Lc Gc Tc Dp` | tall 12/13/14 4 (maxn 45), tall 10 6 1 8 (maxn 45), tall 10 7 1 5 (maxn 50), tall 10 4 2 20, closure 6 12 1 40; H 4–14 (H 12: 2, H 13: 3, H 14: 5 lattices), width 5–13, \|L\| 15–49 | **0/63** | 63/63 |
| 5 | **PairSelf**, \|𝒜\| ≥ 4 | closure 6 12 1 40, tall 8 4 1 12, tall 10 4 2 20, tall 10 6 1 8 (maxn 40–42); H 4–10, width 5–13, \|L\| ≤ 42 | **0/55** | 48/55 (\|𝒜\| = 4 models); no-Tc sharpness world `Lc Gc Dp`: 47/55 SAT |

**Counterexample anatomy.** A counterexample needs:
- three or more colours;
- a pair-join m = c ⊔ c' ∈ Z;
- a colour row whose SCL invariant breaks at a pair-join corner (if no colour pair ever breaks, the Case A/B proof
  below goes through except at the step D2);
- ⊥-orbit and staircase lengths of order H.

Smallest coordinates that could host one: |𝒜| = 3, one pair-join, H 5 (the mutant's smallest models are |L| 15–16,
H 5). Room reached is in §6.

**Proof skeleton (paper; what is proved, and the two open steps).**
- (S1) **SCL with breaks** (proved, §0.2): for x, y ∈ R* the invariant breaks only at a pair-join corner.
- (S2) **Case B** (proved given S1 without breaks between colour rows): if every colour row exits, all exit to one
  colour, and that colour is μ-fixed. The proof of §0.4 uses SCL only between colour rows.
- (S3) **Universal-pair endgame** (proved, paper). Suppose two colours u₁, u₂ lie below λ(z) for every z ∈ R*.
  - If u₁ ⊔ u₂ = m ∈ Z, then λ(m) ≥ m is low, so λ(m) = m, against `D_p`.
  - Otherwise every landing equals J = u₁ ⊔ u₂ ∉ Z, and φ(J) is μ-fixed.
- (S4) **Universal-singleton endgame, exit case** (proved, paper). Suppose c₀ ≤ λ(z) for all z ∈ R*.
  - If λ(c₀) ∉ Z: by GK0 and row c*, c* is μ-fixed.
  - If λ(c₀) = m ∈ Z: m = c₀ ⊔ c' is a pair-join (ColourGain at c₀). If λ(m) ∉ Z, GK0 at c₀ forces λ(c₀) = λ(m) ∉ Z
    when the exit colour is not c₀; when it is c₀, `exitFixed_of_dom` (Tb at c₀) makes c₀ fixed. So λ(m) ∈ Z, of
    height 2, above c₀, and different from m.
- **D1 (open) — NoPairBreak.** In PairSelf's world ∧ NoFix, no staircase (x colour row, y ∈ R*) breaks at a pair-join
  corner. In Lean this is exactly the hypothesis `hnb` of `colourStair`.
  - Located test form, in the relaxation without `D_p`: **BreakCornerSelf.** If the (x, y) staircase breaks at corner
    A, then row A lands at or below A.
  - Free replay: 14/14 breaks have λ(A) ≤ A (`probes/break_anatomy.py`). 10 are in the 127 stored colour-rows + TbA
    models and 4 in the 63 run 4 mutant models. Samples only.
  - `D_p` certainly enters at S3, S4 and D2. Whether D1 also needs it is open. Tb at colour rows may enter D1 through
    P2.
- **D2 (open) — pair-join cycle above a universal colour.** After S4, μ maps the pair-joins above c₀ into
  Z ∩ ↑c₀ ∖ {itself}.
  - For consecutive m → m₂ = λ(m), `pairStair`(q = c₀ = m ⊓ m₂, x = m, y = m₂) gives λ(m₂) = m₂, against Tb or
    `D_p`. That needs absorption.
  - Absorption fails only at a boundary B with F(c₀, B) = φ(B) = d, where d is the other colour of m₂.
  - **D2 is: such a cell cannot occur on the (m, m₂) staircase when c₀ ≤ λ(z) for every z ∈ R*.**
  - If m₂ is not a pair-join, absorption holds. The contradiction then needs Tb or landing at row m₂ ∈ Z ∖ R*. If
    run 4 stays UNSAT, that is evidence this branch is empty in the lean world, a third small step to settle.
- With D1 and D2, Case A (some colour row lands in Z, so e(a) ∈ Z):
  - if e(a) is a single colour, it is universal by SCL, and S4 and D2 close the case;
  - if e(a) is a pair-join m₀, SCL makes C(m₀) meet every K(y). This uses D1 again, and one more step: either
    C(m₀) ⊆ K(m₀) (then S3), or a universal singleton (then S4).
  - This last split is the third open item, **D3** (a transversal of size 2 that lies inside a pair-join).

**Where the relaxed models sit (free analysis, `probes/endgame_check.py`).** This tells which open step is decisive.
- The models are the 238 NoFix models of the world without `D_p`: the mutants of runs 3, 4 and 5 and the stored
  colrows+TbA models.
- **All 238 are in Case A.**
- **235 have a colour c₀ that is universal over R*.**
- **In all 235, λ(c₀) = m is a pair-join and row m lands at m itself.**
- SCL breaks between a colour row and an R* row are rare: 4 in the 171 fresh mutant models, 10 in the 127 stored ones.
- So the relaxed world escapes exactly at S4/D2, in its shortest form. That suggests a sharper D2:
  **D2′ (SelfPair).** If c₀ is universal over R* and λ(c₀) = m = c₀ ⊔ c′ ∈ Z, then c′ ≤ λ(m).
  - Then λ(m) ≥ m, so λ(m) = m, and `D_p` gives the contradiction.
  - Test form in the world without `D_p` (models exist): "universal c₀ and λ(c₀) = m ∈ 𝒫 ⟹ λ(m) = m". Samples
    235/235. One exact run is owed.
- **The decisive step is therefore D2′, not D1.**

**Mode.** Signature inversion: a colour set carried along staircases, with capture (GK0), instead of a located
certificate.

**Limit.** PairSelf is a finite-search conjecture until D1–D3 are proved. Its world is vacuous where it holds, so it can
only ever be `provisional` → `pushed` by emptiness runs. The proof skeleton is what carries information.

**Decisive open step.** D2′ (SelfPair): universal c₀ with λ(c₀) = m = c₀ ⊔ c′ ∈ Z ⟹ c′ ≤ λ(m).
- Candidate tools:
  - `pairStair` with value row c′ or c₀ between rows c′ and m. Absorption fails only at cells F(q, B) = φ(B) equal to
    the other colour of m.
  - Row c′ lands above c₀ (universal), and row m dominates rows c₀ and c′.
- D1 (NoPairBreak, `colourStair`'s `hnb`) is second, and is rarely active in the relaxed models.
- D3 covers the case where e(a) is itself a pair-join: 82 of the 238 relaxed models have such an a as well.

---

## 4. Other programmes

### P2: SCL with a colour as value row (Tb at colour rows kills the breaks through that colour)

**Candidate lemma (paper, proved here; needs Lean).** Let q be a colour with Tb at q, and let x, y ≥ q be landing rows.
Walk the `pairStair` staircase with **value row q**. The boundary values are f_l = F(q, B_l) ≥ φ(B_l). The invariant
"some colour of K(y) lies below f_l" behaves as follows:
- It starts, since f_0 ≥ e(y) (`shadow_start`).
- It survives every corner A ∉ Z, by GK0 as in SCL.
- At a Z-corner it can break only at a pair-join A with an atom value f ∈ C(A) ∖ (K(y) ∪ {q}). Tb at q gives f ≠ q,
  and an atom value of row q is φ(B), a colour.
- In particular, if q ∉ K(y), no 2-colour pair-join containing q can be a break corner.
- The last value lies below F(q, r_x) ≤ λ(x).

**Conditional payoff.** Suppose every pair-join corner on a staircase used in §3 contains a colour q ∉ K(y) lying below
both rows. Then D1 holds for that pair and §3's Case B goes through. This is the design-rule use of "Tb at atom rows at
three-row pair columns" (§295), now located: the value row is the colour shared by the pair-join corner and the two
rows.

**Placement.** S1 ⟸ P2 for pairs (x, y) above a common colour q ∉ K(y). P2 needs Tb at q. That is consistent with the
run 5 sharpness result (dropping Tc gives models).

**Testability.** P2 is a theorem on paper. The open part is its **reach**: does every break of §3 lie on a staircase
whose rows share a colour outside K(y)?
- Test form (free replay first): on the stored colour-rows + TbA models, for each value-⊥ break at corner A = c ⊔ c',
  check whether rows x, y lie above c' (or c) with c' ∉ K(y), and rerun the staircase with value row c'.
- Not done this round; owed.

**Counterexample anatomy.** A break corner A whose colours are both outside the common lower set of x and y, i.e. x and
y share no colour. The smallest case: x, y colour rows, which share only ⊥. So P2 cannot treat colour-row pairs
directly. It applies to pair-join rows y = m ⊇ q with x = q.

**Mode.** Set-aside reversal: the value row q instead of ⊥, which `pairStair` always allowed.

**Limit.** It does not reach colour-row pairs (x ⊓ y = ⊥).

**Decisive step.** Route every §3 break onto a staircase of rows above a common colour. Use (x, m) or (m, m') with
m, m' ∈ R*, not (x, y) colour rows.

### P3: one universal colour (D2 as its own lemma)

**Candidate lemma (conjectural).** **UC.** In PairSelf's world ∧ NoFix, no colour c₀ lies below λ(z) for every z ∈ R*.

**Payoff.** Proved on paper:
- UC with S3 closes Case A when e(a) is a single colour;
- UC with D1 closes Case A completely when e(a) is a single colour;
- by S4, UC reduces to the pair-join cycle D2.

**Placement.** PairSelf ⟹ UC (vacuously). UC ⟸ D2 with S4.

**Testability.** Vacuous in PairSelf's world if PairSelf holds. **Relaxation:** drop `D_p` and keep "c₀ universal over
R*". Then the statement to test is "some pair-join row above c₀ self-lands". Test it on the stored colour-rows + TbA
models first (free), then by one exact run.

**Counterexample anatomy.** A μ-cycle of length ≥ 2 among the pair-joins above c₀, with a cell F(c₀, B) = φ(B) = d on
the boundary of consecutive members. The smallest case needs two pair-joins c₀ ⊔ d₁ and c₀ ⊔ d₂ in Z, so ≥ 3 colours
and a Z-atom c₀ under two height-2 Z-elements; H ≥ 5.

**Mode.** Ladder audit: it isolates the only use of TopRow's absorption on this branch.

**Limit.** It addresses only the single-colour shadow case.

### P4: reduction to thin by a deformation (priority 2 of the commission; assessed, not proposed as lead)

The natural deformation removes a pair-join m from Z by raising φ(m) to a colour a ≤ m. That means F′(x, y) =
F(x, y) ⊔ a·[y ≥ m] for all x. It keeps the colours, Tb, monotonicity and Z ∖ {m}, but:
- (i) a(⊥) = ⊥ can fail at some high z ≥ m with z ≤ φ(z) ⊔ a;
- (ii) raised descents can stop landing (Ta at rows of Z′);
- (iii) NoFix can fail.

No control of (i)–(iii) is known, so it is `needs direct proof` at best. The thin theorem gives it a target: a deformation
need only reach thinness, not two colours.

---

## 5. Already failed (do not repeat)

- Every located route of the frontier §4 (walks from ⊥, extremal indices, FixBelowD, TopLand_*, JointStuck forms).
- R3 / P3 (colour rows only, rows of Z ∖ 𝒜 set to ⊤) at |𝒜| ≥ 3: refuted, and the refutations are all non-thin.
- §299 UNSAT worlds as rungs: restatements via `nrmHom`.
- PC* (pair-closure of landings: C(m) ∩ K(y) ≠ ∅ ⟹ C(m) ⊆ K(y) for y ∈ R*). It fails in 725 instances on the stored
  colour-rows + TbA models, and in only 157 of them does m self-land. It also fails on stored W0 models: SCL breaks
  between R* rows occur in 18 of the 83 non-thin unbounded W0 models (`probes/w0_census.py`). So PC* is not a usable
  intermediate. Use D1 and D2 instead.

## 6. Probe scripts and report lines

**Tester.** `probes/rowset_probe.py` is the briefer's own encoding, written from the statements and not derived from
`cgall_probe.py`.
- Rows of height ≤ 2 are variables. Rows of height ≥ 3 are the constant ⊤.
- Always imposed: a(⊥) = ⊥, ZT, n1, h(⊤) ≥ 3, exact colours, at least K colours, NoFix at landing colour rows.
- Per-class flags: L (lands), G (ColourGain), T (Tb), D (lands and λ(x) ≰ x). Classes: b = ⊥, c = colour rows,
  q = all atom rows of Z, p = pair-join rows, z = all Z rows.
- Shape flags: `thin`, `nonthin`, `unb`.
- Output: it prints the quantifier and the SAT meaning, one progress line per lattice with the result of each world,
  and replays every SAT model from the definitions (assertion). Several worlds run per lattice (`'W1|W2'`).
- Models are dumped to `runs/<tag>_w<i>.json`.

**Free analyses** (stored models only, no search):
- `look.py`: describe models.
- `thin.py`: colour-thinness census (0 thin of 291 stored NoFix models).
- `scl_check.py`: SCL break claim, 0 violations on 41,103 pairs.
- `w0_census.py`: 361 W0 models. 83 are unbounded non-thin with |𝒜| ≥ 3; 84 are thin (81 with |𝒜| = 2, 3 with |𝒜| = 3).
- `pc_check.py`, `break_anatomy.py`.

**Run budget.** 5 exact runs were used, each under `timeout 1500`, at most 2 in parallel.

```
Thin (lead of §0) | bank lattices (exact): 43 lattices of brief297/cex/ColourGraph_R3.json + s299 | EXISTS F; SAT = thin NoFix model
  room: |L| 15–42, H 4–10 | anatomy: |𝒜| ≥ 3 (2 is Lean), no pair-join
  thin branch: 0/43 SAT | mutant P3 (same world without thin): 43/43 SAT -> consistent with the Lean proof (run 1;
  the mutant dump was lost to a file-name bug fixed before run 2; those lattices' P3 models are banked already)
Thin | tall 10 4 2 20, tall 14 4 2 20 (maxn 40), tall 10 7 1 5 (maxn 50), tall 12/13 4 1 8, tall 10 6 1 8 (maxn 45)
  room: H 10 (13 lattices), 12 (2), 13 (3), 14 (1); width 5–13; |L| 22–49; |𝒜| ≥ 3
  0/19 SAT | mutant P3 19/19 SAT (runs/run2_thin_room_w1.json) -> proved (Lean), probes agree
PairRows (Lc Gc Tc Gp Tp, non-thin) | closure 6 12 1 40, tall 8 4 1 12, tall 10 4 2 20 (maxn 40) | EXISTS F
  room: H 4–10, width 4–12, |L| 15–38, |𝒜| 3–4
  0/60 SAT; Lz Gc Gp Tq Tp 0/60 | mutant §299 colrows+TbA (non-thin): 60/60 SAT (runs/run3_pair_w2.json) -> provisional
PairSelf (Lc Gc Tc Dp, non-thin), |𝒜| ≥ 4 (run 5) | closure 6 12 1 40, tall 8 4 1 12, tall 10 4 2 20, tall 10 6 1 8 (maxn 40–42)
  | EXISTS F; SAT = PairSelf fails
  room: H 4–10, width 5–13, |L| 15–42, |𝒜| ≥ 4 (one step above the anatomy's 3) | anatomy needs |𝒜| ≥ 3, one pair-join, H ≥ 5
  0/55 SAT | mutant (§299 colrows+TbA, non-thin): 48/55 SAT (runs/run5_pairself_K4_w2.json)
  | sharpness: Tb at colour rows dropped (Lc Gc Dp): 47/55 SAT (runs/run5_pairself_K4_w1.json, smallest |L| 15, H 5,
    colours 1–4, pair-joins 6, 8) -> provisional (the evidence rule is met on the 48 lattices where the mutant has models)
PairSelf (Lc Gc Tc Dp, non-thin), |𝒜| ≥ 3 (run 4) | tall 12 4 1 8, tall 13 4 1 8, tall 14 4 2 20 (maxn 45), tall 10 6 1 8
  (maxn 45), tall 10 7 1 5 (maxn 50), tall 10 4 2 20 (maxn 40), closure 6 12 1 40 | EXISTS F; SAT = PairSelf fails
  room: H 4–14 (10 lattices at H 12–14, widths 6–9, |L| 33–45), width up to 13, |L| 15–49 | anatomy: |𝒜| 3, H ≥ 5
  0/63 SAT | mutant (§299 colrows+TbA, non-thin): 63/63 SAT (runs/run4_pairself_w1.json) -> provisional
  Pushed beyond the anatomy in H (to 14), width (to 13) and |𝒜| (to ≥ 4, run 5). Exact N is not controlled, so N is
  owed: stage `provisional`, one dimension short of `pushed`.
```

## 7. Pushes owed

- PairSelf:
  - exact N (the tester does not control N; add the E-flags of `orbit_probe.py` or filter by N in the replay);
  - H 14 at width ≥ 6 (`tall 14 6`, memory permitting);
  - |𝒜| ≥ 5;
  - a second encoding (the worker's, e.g. `cgall_probe.py` extended with a pair-join class and a `nonthin` clause).
- Thin: none (Lean). The worker re-compiles.
- SelfPair (D2′ test form): one exact run in the world without `D_p` (`Lc Gc Tc Lp unb nonthin`). Add the
  hypothesis "c₀ universal over R* and λ(c₀) = m ∈ 𝒫" and the negated conclusion "λ(m) ≠ m". Expected UNSAT. The
  mutant drops "c₀ universal".
- BreakCornerSelf (D1 test form): an exact run in the colour-rows + TbA world. It needs a staircase-break encoding:
  r3_probe's `break` mode is a local approximation and is not enough.

## 8. Hard constraints and design rules (as now understood)

- Sharpness:
  - thin ⟹ CertAtom with colour rows only and no Tb;
  - non-thin needs Tb at the colour rows (run 5) and the pair-join rows' landing (run 3 mutant);
  - ColourGain at the colour rows alone, even with Tb at every atom and landing at every Z-row, is SAT on 60/60 non-thin
    lattices.
- Tb at the pair-join rows is needed only in the descent form λ(m) ≰ m (runs 4–5: 0/118). Tb at non-colour atoms and
  landing at non-R* rows of Z are not needed (run 3 world 1; run 4).

## 9. Formalization order

1. Install `ThinColour.lean` (worker re-compiles; standard axioms).
2. Ladder edits per §2.
3. (Done in the scratch file.) `colourStair` is the general SCL with NoPairBreak at the corners as its hypothesis
   `hnb`. D1 must deliver `hnb` for (x colour, y ∈ R*).
4. P2's value-row-q version of the same.
5. S3 and S4 as lemmas.
6. Then D1, D2 and D3 as they are proved. No `sorry`, no new axioms.

## 10. Expected report

One verdict for each of: §0 Thin (`proves`); P1 PairSelf (`provisional`, `new conjecture` once pushed, or `refuted`
with a banked model); P2 (`conditional lemma`, with reach measured); P3 UC (`vacuous here` with the relaxation result,
or `conditional lemma`); P4 (`needs direct proof`).

## 11. Frontier corrections

1. **Ladder, stale lines.** Remove these per the snapshot rule:
   - "(superseded by the line above:) CertAtom(|𝒜| = 2) ⟸ TwoColourCG … new conjecture, pushed";
   - "CertAtom(|𝒜| = 2) ⟸ ShadowLemma … new conjecture, pushed";
   - "ShadowLemma ⟸ NoBreak [paper §297.3 …]".

   ShadowLemma is the Lean theorem `twoColour_selfShadow`, and all three are subsumed by `certAtom_of_thin` (this brief).
2. **"(history) |𝒜| = 2 status (§297)"** is a history block. Delete it.
3. **"OPEN CASE (§295)"** still names "smallest open subcase |𝒜| = 2 (P4)". That case is closed. Merge the block into
   the open target, which is now non-thin.
4. **The Lemma K description is too narrow.** "A descent above a ∨ b with φ(a ∨ b) = b lands at a ∨ b" holds for
   **every** row landing above a, from ⊤ (`land_capture`). Add it to the ladder as the capture law GK0.
5. **The §299 design rule needs its branch.** "A proof for |𝒜| ≥ 3 must use Tb at atom rows and the landing/ColourGain
   of height-2 rows" holds on the non-thin branch only. On the thin branch, colour rows with no Tb suffice (Lean and
   runs 1–2). On the non-thin branch, the height-2 rows needed are the pair-join rows (run 3 world 1; runs 4–5 in
   descent form).
6. **The R3 world is narrower than "three rows".** Every other row is the constant ⊤, so rows of Z ∖ 𝒜 do not land.
   All 42 P3 models are non-thin, and so are all 291 stored NoFix models of every relaxed world. The divide at
   |𝒜| ≥ 3 is thinness.
7. **Room vector.** Add |𝒜| (stored NoFix models reach 3–5; the probes here reach |𝒜| ≥ 4), the number of
   pair-joins, and the thin/non-thin branch.
8. **Corpora.** `experiments/amalgamation/holding/cgall_*.json` is the main stored NoFix corpus: 249 models of the §299
   worlds; with ColourGraph_R3 (42) it makes 291. The frontier does not list it.
9. **Census.**
   - The 167 unbounded W0 models split as follows: 84 thin (81 with |𝒜| = 2, 3 with |𝒜| = 3) and 83 non-thin
     (73 with |𝒜| = 3, 10 with |𝒜| ≥ 4).
   - SCL breaks between R* rows occur in 18 of the 83 non-thin models. Those models all have a fixed atom, so breaks
     are not excluded without NoFix.
10. **Buckets.**
    - Established: add `certAtom_of_thin`, `colourStair`, `thinStair`, `land_capture`, `shadow_start`,
      `phi_low_colour`, `join_of_two_atoms` once installed.
    - Open: "CertAtom at N ≥ 2, 𝒜 unbounded, |𝒜| ≥ 3, some pair-join in Z".
11. **Design rule §7.** "Tb at atom rows is used at three-row pair columns" is not used at all on the thin branch. On
    the non-thin branch its natural place is P2: value row = a colour shared by the rows, at pair-join corners.
12. **Process (moving checkout).** At 22:14 UTC, during the briefer's runs, `experiments/amalgamation/cgall_probe.py` in
    the checkout was modified (uncommitted; HEAD still 07c9506): `pairself` and `pairselfM` modes were added. The
    briefer did not write it; the briefer's only repository actions were reads. No result here depends on that file. If
    the worker is now encoding PairSelf there, that is the second encoding §7 asks for. Its mutant `pairselfM` ("λ(m) ≤
    m allowed") matches this brief's relaxation.
