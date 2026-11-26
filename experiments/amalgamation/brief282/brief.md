# Brief, run 14 (frontier-only, no seed): the top layer of Z

## Repository, pinned commit

`/home/user/mordor` at **f6d0586** (`git log -1`: "§34.3z²⁸¹: width is a room-to-fail dimension; BotOrbit, StrictDep, Orbit4
refuted at height 12 …"). Log `docs/rounds/26-v3.7.md`, §34.3z²⁷⁶–²⁸¹ (lines 18074–18537). Lean `lean/Mordor/LateParent.lean`,
section `Landing` (lines 5449–5733). The checkout was not modified; all scripts and outputs of this brief are in
`/tmp/claude-0/-home-user/3b6fdd2c-c95c-5c07-b47c-6ae28c687a4c/scratchpad/amr_run14/brief/`.

## Failure signature (computed from the frontier and checked at source)

Every refuted rung **names which row certifies**: either one row reached by a deterministic walk anchored at ⊥ (the
⊥-descent, the trap breakpoint w, the μ-orbit of ⊥, the first exit of d's in-step chain — BreakCert, OrbitDom, JoinCert,
Orbit3, BotOrbit, StrictDep, Orbit4, ChainT1, ChainDom′), or every row of a family (ExitDom, QEany, ExitGood, MuLoop,
M:TopCellAll and, this round, TopAbsorb, GoodFix, MaxIdx2). In one sentence: **each refuted route predicts the certifying
row (by a walk from ⊥ or by a rule every row must obey) instead of proving that the set of certifying rows is nonempty.**
What survives at height 10–12 and width 4–5 is existential over a set of rows and names none of them: GoodAtom1, Cert1,
TopCert and TopCell, which the ladder audit below shows is not a located certificate at all but GoodAtom1 restricted to
the atoms lying below the top layer of Z.

## Mission

Prove that **some atom below the top layer of Z is good** by an existence argument over the whole layer (contradiction,
counting or an extremal principle on the layer), never by following a row or an orbit from ⊥ and never by a universal
transport statement.

## Frontier

### Definitions (as in source)

- F : L → L → L monotone in both arguments, L finite (complete, `NoChain α (H+1)`); h = `height H`; a(x) = gfp F(x,·).
  R_0 = ↓⊥, R_{k+1} = ↓(R_k ∪ a(R_k) ∪ b⁻¹(R_k)) (`Rk`).
- `IsGood F p`: p ≤ a(p), or the row-p descent from ⊤ meets p. `DL F r p`: ∀ y, y ≤ F(r, p ⊔ y) → y ≤ p.
- **World W0 ∧ n1** (level 1): a(⊥) = ⊥, R_2 tight (∀ z ∈ R_2, h z ≤ 2), ⊤ ∉ R_2, R_1 not tight. Then R_1 = Z := {y : F(⊥, y)
  = ⊥}. With h(⊤) ≥ 3 this is equivalent to a(⊥) = ⊥, (T) and n1, where (T): no row x ∈ Z has a cell F(x,y) ≤ x or
  y ≤ F(x,y) at a column y of height ≥ 3 (x = ⊥ included, which forces every element of Z to have height ≤ 2).
- λ(x) = first element of height ≤ 2 on row x's descent from ⊤ (the landing). x **exits** iff λ(x) ∉ Z; then λ(x) has
  height 2 and c(x) := F(⊥, λ(x)) is an atom of Z (`exit_atom`). μ(x) = λ(x) if λ(x) ∈ Z, else c(x); μ(⊥) = d, the last
  nonzero element of the ⊥-descent.
- **M2 := {m ∈ Z : h(m) = 2}**, the top layer of Z (nonempty by n1). Every element of M2 is maximal in Z (Z has no
  element of height 3), and two distinct elements of M2 have their join outside Z.
- Branches (as in run-13 A's `w0lean.py`): exit-a / in-a (h(d) = 2, d exits / in-steps), exit-b / in-b (d a bad atom), g
  (d a good atom; GoodAtom1 trivial).

### Established results used (all checked in source)

- `goodAtom1_iff_ownCell1`: GoodAtom1 ⟺ some atom q ∈ R_1 has a height-2 element p on its own row's descent with
  q ≤ F(q, p). `ownCell_of_good` is its forward half.
- `good_of_dominating_desc`: p of height 2 on row x's descent, atom q ∈ R_1, q ≤ x, q ≤ F(q, p) ⟹ q good.
- `upTrap_land`: row x reaches p (height 2) at index k, atom q ≤ x with q ≤ F(q, p), Tb at row q, q ≤ m, h(a(m)) ≤ 2 ⟹
  p is row m's landing. `tb_of_tight` gives Tb for rows of R_1; `aIter_mem` (ParentAncestry.lean) gives a(m) ∈ R_2.
- `land_not_le` (λ(x) ≰ x), `land_bot_lt`, `exit_atom`, `land_unique` (λ is the only height-2 element of a Z-row's descent).
- `goodAtom_of_inCert`: e ∈ R_1 exits and c(e) ≤ e ⟹ c(e) is a good atom of R_1.
- `exitFixed_of_dom`, `cert_of_exitFixed`, `goodAtom_of_exitFixed` (Cert1 ⟺ CertAtom, a paper composition of these).
- `goodAtom_of_greatestZ` (TopZ), `breakExists`, `overshadowed_of_bad_botEnd`, `base_good_of_DL`, `dl_of_le_row`.

### Exact open target

GoodAtom1 (`LateParent.GoodAtom1`): in W0 ∧ n1, some atom of R_1 is good. It gives BackGood1 at k = 1
(`backGood1_one_of_goodAtom1`). Ladder at level 1 after this brief:

```
GoodAtom1 [O]  ⟸  (d good) ∨ NMGood [O, lead]  ⟺  TopCell [O]          (paper, this brief: Lemma T)
GoodAtom1      ⟸  Cert1 [O] ⟺ CertAtom                                (goodAtom1_of_cert1; exitFixed_of_dom + cert_of_exitFixed)
NMGood         ⟸  TopCert [O]                                         (goodAtom_of_inCert: c(m) < m)
Cert1          ⟸  TopCert                                             (by definition: m is a Cert1 witness)
NMGood         ⟹  TopCert  when the good atom below M2 is μ-fixed     (paper, Lemma D; in general OPEN: GoodFix is refuted)
TopCert        ⟸  LocalTop at some m ∈ M2 ⟸ TopZ [P goodAtom_of_greatestZ]   (paper, Programme 3)
```
TopCert is the strongest live rung: it implies both Cert1 and TopCell. TopCell does **not** sit below Cert1 (frontier
correction 2).

## Reuse

All in `lean/Mordor/LateParent.lean` unless noted: `ownCell_of_good`, `good_of_dominating_desc`, `upTrap_land`,
`upTrap_stay`, `tb_of_tight`, `land_not_le`, `land_unique`, `exit_atom`, `goodAtom_of_inCert`, `goodAtom_of_exitFixed`,
`exitFixed_of_dom`, `rowIter_succ_le`, `iter_antitone_of_le`, `eq_of_le_of_height_ge`, `goodAtom_of_greatestZ`;
`aIter_mem` (ParentAncestry.lean), `Rk_down` (Orbit.lean), `mem_succ_of_cell` (OrbitHeight.lean), `height_strictMono`
(GapPotential.lean), `le_a`, `row_a` (Derived.lean).

## Lead programme: NMGood — a non-maximal atom of Z is good

**Candidate lemma (conjectural).** Let F be monotone on a finite lattice with a(⊥) = ⊥, R_2 tight, ⊤ ∉ R_2, R_1 not
tight and h(⊤) ≥ 3, and suppose d is not a good atom. Then there are m ∈ R_1 with h(m) = 2 and an atom q < m such that
q is good.

**Conditional payoff (proof).** q ∈ R_1 by `Rk_down`, h(q) = 1, q good: that is GoodAtom1's conclusion. If d is a good
atom, GoodAtom1 holds with q = d. So GoodAtom1 ⟸ NMGood.

**Ladder audit that places it (Lemma T, paper, Lean-ready).** For m ∈ R_1 with h(m) = 2:

> TopCell at m (q := m ⊓ λ(m) is an atom and q ≤ F(q, λ(m)))  ⟺  some atom q < m is good.

(⟹) λ(m) ≥ q, λ(m) ≠ q (since λ(m) ≰ m by `land_not_le` and q ≤ m), h(λ(m)) ≤ 2, so h(λ(m)) = 2;
`good_of_dominating_desc` with x = m. (⟸) `ownCell_of_good` gives p of height 2 on row q's descent with q ≤ F(q, p);
`upTrap_land` (x = q, Tb from `tb_of_tight`, h(a(m)) ≤ 2 from `aIter_mem`) makes p the landing of row m; p ≰ m
(`land_not_le`), so m ⊓ p < p has height ≤ 1, and q ≤ F(q, p) ≤ p (`rowIter_succ_le`) gives m ⊓ p = q.
Hence **TopCell ⟺ (d is a good atom) ∨ NMGood**. TopCell is not a located certificate: it is the target restricted to the
atoms below M2, and it survived for that reason.

**Two companions (paper, Lean-ready).**
- **Lemma U (at most one good atom below any row of Z).** If m ∈ R_1 and q ≠ q′ are good atoms below m, then `upTrap_land`
  makes both landings equal to λ(m) = p, q ⊔ q′ ≤ m ⊓ p < p, and h(q ⊔ q′) ≥ 2 > h(m ⊓ p): contradiction. So every row of
  Z sees at most one good atom. The existential in NMGood cannot be strengthened to "every m ∈ M2" (M:TopCellAll fails
  on every branch, below).
- **Lemma D (fixed good atoms make their parents certify).** If q is good, μ(q) = q and q < m ∈ R_1, then λ(m) = λ(q) = p
  (`upTrap_land`; q = F(⊥, p) ≤ F(q, p)), so m exits with c(m) = q ≤ m. Hence NMGood ⟺ TopCert when the good atom below M2
  is μ-fixed. GoodFix (every good atom is μ-fixed) is refuted at height 12 (below), so NMGood ⟹ TopCert stays open;
  on every probed lattice and branch the three columns TopCell, NMGood, TopCert agree.

**Placement.** (d good) ∨ NMGood ⟺ TopCell ⟹ GoodAtom1. TopCert ⟹ NMGood (`goodAtom_of_inCert`; c(m) < m). TopZ ⟹
TopCert (the greatest element of Z is the only element of M2 and exits with c ≤ m, as in `goodAtom_of_greatestZ`). NMGood
is not known to imply Cert1 except through Lemma D.

**Testability class.** Finitely refutable (an existential over atoms below M2 for a fixed F; the negation is a universal
statement over a finite lattice and has finite counterexamples).

**Hypothesis world.** W0 ∧ n1 off branch g. It has models on every branch off g at height 10, width 4 (19, 8, 12 and 12
of 20 lattices), height 11 width 5 (8 of 8 on each branch) and height 12 width 4 (8, 5, 6, 6 of 8). On g the statement
is not asserted: on 19/20 g-lattices of `tall 10 4 2 20` (7/8 at h12, 8/8 at h11) some F on g has no good atom below M2,
so the good atom d is then maximal in Z.

**Mode.** Ladder audit (Lemma T) for the normal form; signature inversion for the stance (an existential over the top
layer, own-row cell, no walk).

**Limit.** It does not say which atom is good, and Lemma U plus the refutation of TopAbsorb show that no universal
transport inside the layer will say it. It is a restatement of TopCell, so as a candidate it adds no new instance; what it
adds is the right statement to prove and the three lemmas T, U, D.

**Decisive open step, named: TopExit = TopCert.** Off g, show that some m ∈ M2 exits with c(m) ≤ m (then NMGood by
`goodAtom_of_inCert`). It holds with power at height 12 width 4 and height 11 width 5 (one encoding). It splits into
- **ExitM2**: some m ∈ M2 exits (holds with power at height 11 width 5; no failure at height 10 width 4), and
- **choice of the exit**: among the exiting rows of M2, one is dominated by its own exit atom. The universal form of this
  step (TopAbsorb: every exit atom of M2 is absorbed by an exiting M2-row above it) is **refuted** at height 10 (|L| = 27).
  So the proof must pick the exit without a universal rule. The cheapest extremal choice (MaxIdx2, the latest landing of
  M2) is refuted at height 12, so landing index is not the order; what remains is a counting or contradiction argument
  over the pairs (m, c(m)), m ∈ M2 exiting, which must use the cell (M:TopCellAll and M:AllDomM2 fail on every branch).

## Other programmes

### Programme 2: TopCert — some top-layer row exits to an atom below it (the lead's decisive step, as its own programme)

- **Candidate (conjectural).** W0 ∧ n1, h(⊤) ≥ 3, d not a good atom ⟹ some m ∈ Z with h(m) = 2 has λ(m) ∉ Z and
  F(⊥, λ(m)) ≤ m. (Run-13 A's TopCert; on file at height 6 only, and absent from the frontier's ladder.)
- **Payoff (proof).** `goodAtom_of_inCert` with e = m: c(m) is a good atom, and c(m) < m, so NMGood, hence TopCell and
  GoodAtom1; m is also a Cert1 witness, so Cert1.
- **Placement.** TopZ ⟹ (LocalTop at some m ∈ M2) ⟹ TopCert ⟹ Cert1 ∧ NMGood. It is the strongest live rung on the
  ladder.
- **Testability.** Finitely refutable. **World:** off g; models on every off-g branch at height 11 and 12. **Mode:**
  ladder audit (a rung on file at height 6, re-placed above both Cert1 and TopCell). **Limit:** it reads the cell on row
  ⊥ (c(m) = F(⊥, λ(m))), so it is strictly stronger than NMGood on any F whose only good atoms below M2 are not
  μ-fixed. Non-fixed good atoms exist (GoodFix fails); whether one can be the only good atom below M2 was not probed.
- **Decisive open step:** ExitM2 ⟹ TopCert. ExitM2 holds with power (height 11, width 5). The universal version
  TopAbsorb is refuted, so the step must choose the exit; the cheapest extremal choice, MaxIdx2, is refuted too.

### Programme 3: LocalTop — the anchor-free existence theorem TopZ with its hypothesis made local (ladder audit; needs direct proof)

- **Theorem (paper, Lean-ready; a two-line generalization of `goodAtom_of_greatestZ`).** If m ∈ R_1 with landing index i
  satisfies **LocalTop(m)**: ∀ y, F(⊥, y) = ⊥ → y ≤ λ(m) → y ≤ m, then λ(m) ∉ Z (else λ(m) ≤ m, contradicting
  `land_not_le`), c(m) = F(⊥, λ(m)) is an atom of Z below λ(m) (`exit_atom`, `land_bot_lt`), so c(m) ≤ m and c(m) is good
  (`goodAtom_of_inCert`). TopZ's hypothesis (every y ∈ Z is ≤ m) is the special case.
- **Normal form (paper).** LocalTop(m) ⟺ m exits, c(m) ≤ m, and c(m) is the only atom of Z below λ(m) (λ(m) has height
  2 and is not in Z, so Z ∩ ↓λ(m) = {⊥} ∪ {atoms of Z below λ(m)}).
- **Candidate existential (conjectural): ∃ m ∈ Z*, LocalTop(m).** It implies TopCert (when m ∈ M2) or Cert1.
- **Testability.** Finitely refutable but **silent**: not probed (budget). Expected to fail on wide lattices, where a
  landing of height 2 has two atoms in Z. **Mode:** ladder audit of TopZ. **Limit:** a located certificate with an extra
  uniqueness condition. **Open step:** none if it fails; if it holds, why the certifying landing has a single Z-atom.
- Worth formalizing for the theorem alone: it is the only anchor-free existence argument in the library, and its
  hypothesis is now a statement about one landing instead of all of Z.

## Probe scripts

All exact: for each lattice and branch, a SAT query over **all** monotone F in W0 ∧ n1 (rows of low elements one-hot and
monotone in both arguments, a(⊥) = ⊥, (T) at every row of Z, n1; rows of high elements irrelevant), built on run-13
control A's class `W` (`amr_run13/ctlA/w0lean.py`, independent of `muorbit_sat.py`). Each column means **SAT = the named
statement fails for some F on that lattice and branch**; `vac` = the branch has a model. Every SAT model is decoded,
replayed with `rstages.stages` and re-checked in Python from the definitions (`Rep` + `check`) before it is counted; the
testers print their quantifier in the first line. Run from the brief directory; outputs and minimal models are written
there only.

- `diag.py` (run 1, a diagnostic of stored models, **not a search, not evidence**): structure of the stored models
  cx281 (h12), cx278_breakcert (h8), cx279_orbit3 (h10), cx280_orbit3_models (6 models, h8–h9). Output `run1_diag.txt`.
- `toplayer.py` (runs 2, 3): TopCell, NMGood, ExitM2, TopAbsorb; mutants M:ExitDom, M:AllDomM2, M:TopCellAll.
- `toplayer2.py` (run 4): TopCell, NMGood, TopCert, GoodFix, OneGood, MaxIdx2; mutants M:TopCellAll, M:GoodA,
  M:OneExitAtom, M:MinIdx2.
- `toplayer3.py` (run 5): NMGood, TopCert, ExitM2; mutants M:TopCellAll, M:AllDomM2, M:AllExitM2.
- Encodings in words. NMGood: no atom q with q ≤ m for some m ∈ M2 has `good[q]` (descent of row q meets q, or a(q) ≥ q,
  as exact one-hot iterates). TopCell: no m ∈ M2 lands at a height-2 p with q = m ⊓ p an atom and F(q, p) ≥ q. TopCert: no
  m ∈ M2 lands at p ∉ Z with F(⊥, p) an atom below m. ExitM2: every m ∈ M2 lands in Z. TopAbsorb (negated): some exiting
  m ∈ M2 with exit atom c such that no m′ ∈ M2 above c exits to c. GoodFix (negated): some good atom q of Z with ¬(q exits
  to q). OneGood (negated): two good atoms of Z. MaxIdx2 (negated): no m ∈ M2 whose landing index is maximal among M2 is a
  TopCert. Each mutant is the named sibling with the quantifier or the restriction changed (docstrings).

Room-to-fail parameter in every line: corpus height and width (M random sets), as fixed by §34.3z²⁸¹ (counts only at
height ≥ 10 with M ≥ 4, or on the stored h12 lattice plus such a corpus).

### Run 1 — `diag.py` on stored models (diagnostic, samples only, not evidence)

Stored lattices and F: cx281 (h12, |L| = 59), cx278_breakcert (h8, 33), cx279_orbit3 (h10, 31), the six models of
cx280_orbit3_models (h8–h9, 30–46). In all ten: exactly one good atom; it is non-maximal in Z, μ-fixed, and every M2-row
above it exits to it with c ≤ m (TopCert there); all exits of Z-rows share one landing in these ten (contradicted in
general by the L1(d) refutation of §34.3z²⁷⁰, |L| = 21, so not proposed). In cx281 the good atom 4 lies below M2-rows 10, 11, 13, which land at
14 and exit to 4; the ⊥-orbit 2 → 5 → 2 never meets it.

### Run 2 — `toplayer.py file cx281_botorbit_cycle_h12_n59.json`

Stopped by the briefer after about 35 min CPU on the single lattice, before any line was printed: **no result**. The same
lattice is lattice 5 of `tall 12 4 1 8` (set family checked equal), covered by run 4.

### Run 3 — `toplayer.py tall 10 4 2 20` (exact; 20 lattices, all height 10, |L| 22–50, width M = 4; 1200 s)

`statement | tall 10 4 2 20 (exact) | ∀F per lattice and branch; SAT = the statement fails for some F`

| statement | branch | hypothesis models | candidate failures | mutant failures | verdict |
|---|---|---|---|---|---|
| TopCell | exit-a / in-a / exit-b / in-b | 19 / 8 / 12 / 12 | 0 / 0 / 0 / 0 | M:TopCellAll 15 / 8 / 11 / 11 | **holds with power** on each |
| TopCell | g | 20 | 19 | 19 | not asserted on g (antecedent) |
| NMGood | same as TopCell, column-identical on every lattice and branch | | 0 / 0 / 0 / 0 (g 19) | M:TopCellAll as above | **holds with power** off g |
| ExitM2 | off g | 19 / 8 / 12 / 12 | 0 / 0 / 0 / 0 (g 19) | no paired mutant in this run | silent |
| TopAbsorb | exit-a / in-a / exit-b / in-b | 19 / 8 / 12 / 12 | **9 / 6 / 9 / 9** (g 19) | M:AllDomM2 15 / 8 / 11 / 11; M:ExitDom 9 / 7 / 9 / 9 | **refuted**, smallest |L| = 27 |

### Run 4 — `toplayer2.py tall 12 4 1 8` (exact; 8 lattices, all height 12, |L| 27–59, width M = 4; lattice 5 is the cx281 lattice; 3299 s)

| statement | branch exit-a / in-a / exit-b / in-b | hypothesis models | candidate failures | mutant failures | verdict |
|---|---|---|---|---|---|
| TopCell | | 8 / 5 / 6 / 6 | 0 / 0 / 0 / 0 (g 7 of 8) | M:TopCellAll 6 / 5 / 5 / 5 | **holds with power** on each |
| NMGood | | 8 / 5 / 6 / 6 | 0 / 0 / 0 / 0 (g 7) | M:TopCellAll 6 / 5 / 5 / 5 | **holds with power** on each |
| TopCert | | 8 / 5 / 6 / 6 | 0 / 0 / 0 / 0 (g 7) | M:TopCellAll 6 / 5 / 5 / 5 (TopCert at m ⟹ TopCell at m, so "every m is TopCert" fails wherever it does) | **holds with power** on each |
| GoodFix | | 8 / 5 / 6 / 6 | **6 / 4 / 5 / 5** (g 6) | M:GoodA 8 / 5 / 6 / 6 | **refuted**, smallest |L| = 32 (exit-a) |
| OneGood | | 8 / 5 / 6 / 6 | **6 / 4 / 5 / 5** (g 6) | M:OneExitAtom 7 / 5 / 6 / 5 | **refuted**, smallest |L| = 32 |
| MaxIdx2 | | 8 / 5 / 6 / 6 | **6 / 5 / 5 / 5** (g 7) | M:MinIdx2 6 / 5 / 5 / 5 | **refuted**, smallest |L| = 27 |

TopCell, NMGood and TopCert are column-identical on every lattice and branch. On the cx281 lattice (all F) all three hold
off g.

### Run 5 — `toplayer3.py tall 11 5 1 8` (exact; 8 lattices, all height 11, |L| 30–57, width M = 5; 2121 s)

| statement | branch exit-a / in-a / exit-b / in-b | hypothesis models | candidate failures | mutant failures | verdict |
|---|---|---|---|---|---|
| NMGood (lead) | | 8 / 8 / 8 / 8 | 0 / 0 / 0 / 0 (g 8) | M:TopCellAll 8 / 8 / 8 / 8 | **holds with power** on each |
| TopCert | | 8 / 8 / 8 / 8 | 0 / 0 / 0 / 0 (g 8) | M:AllDomM2 8 / 8 / 8 / 8 | **holds with power** on each |
| ExitM2 | | 8 / 8 / 8 / 8 | 0 / 0 / 0 / 0 (g 8) | M:AllExitM2 8 / 8 / 8 / 8 | **holds with power** on each |

**Summary.** The lead NMGood holds with power on every off-g branch at height 10 (width 4), height 11 (width 5) and height
12 (width 4, including the cycle lattice), in one encoding (the w0lean `W` class). The worker's second encoding should be
`muorbit_sat.py` tcase 17 (TopCell) on `tall 12 4 1 8` and `tall 11 5 1 8`. Exact runs used: 5 (run 1 a diagnostic of
stored models, run 2 stopped without result).

Stored SAT models (replayed): `m_tall_10_4_2_20_*.json`, `m2_tall_12_4_1_8_*.json`, `m3_tall_11_5_1_8_*.json` in the
brief directory; e.g. `m_tall_10_4_2_20_TopAbsorb_exit-a_min27.json`, `m2_tall_12_4_1_8_GoodFix_exit-a_min32.json`,
`m2_tall_12_4_1_8_OneGood_exit-a_min32.json`, `m2_tall_12_4_1_8_MaxIdx2_exit-a_min27.json`. Which kind of good atom
(Lemma C (i) or (iii)) breaks GoodFix was not inspected (budget); the worker should replay the GoodFix models.


## Already failed (do not repeat)

- **TopAbsorb** (this brief): every exiting m ∈ M2 has an exiting m′ ∈ M2 with c(m′) = c(m) ≤ m′. Refuted at height 10,
  width 4 (`tall 10 4 2 20`): fails on 9 / 6 / 9 / 9 lattices of exit-a / in-a / exit-b / in-b, smallest |L| = 27
  (model `m_tall_10_4_2_20_TopAbsorb_exit-a_min27.json`, replayed). Moving the anchor of ExitDom from ⊥ to the top layer
  does not save universal transport.
- **GoodFix** (this brief): every good atom of Z is μ-fixed. Refuted at height 12 width 4 (6 / 4 / 5 / 5 lattices off g,
  |L| = 32). So GoodAtom1 ⟺ Cert1 does not follow this way, and NMGood ⟹ TopCert stays open.
- **OneGood** (this brief): at most one good atom in Z. Refuted at height 12 (|L| = 32). Only the local form holds
  (Lemma U: at most one good atom below each row of Z).
- **MaxIdx2** (this brief): a latest-landing row of M2 certifies. Refuted at height 12 (|L| = 27); with run-13's MaxIdx this
  closes the landing-index extremal route.
- ⊥-anchored located certificates: BreakCert, OrbitDom, JoinCert (h8, |L| = 33); Orbit3 (h8–h11, also N = 4 at width);
  BotOrbit, StrictDep, Orbit4 (h12, |L| = 59: the ⊥-orbit cycles 2 → 5 → 2); ChainT1, ChainDom, ChainDom′, ExactDrop,
  DropProp (h5–h10). Reason: a walk from ⊥ can cycle or skip levels once height and width give it room.
- Anchor-free universal forms: ExitDom, QEany (|L| = 12), ExitCert/ExitCoLand/ExitGood (|L| = 15), MuLoop (|L| = 31),
  AtomOrb/MaxIdx/MaxAll (|L| = 31), LateCert. Reason: the certificate is one row, not a property of every row.
- Earlier: BotUp/BotTrack/RowDrop/LamNZ (h6), DomOrbit, ExitBelow (h7), PredBelow, LandBelow, InStepUp (h6), and the
  pre-level-1 families listed in the frontier file.

## Hard constraints

- Room to fail = height × width × N (§34.3z²⁸¹): a probe counts only at height ≥ 10 with width ≥ 4, or on the stored
  height-12 lattice plus such a corpus. Located statements held through height 7 and failed at 8; narrow corpora hid
  Orbit3 and Orbit4 failures that appeared only at width 4–5.
- Sharpness boundary: every probed mutant without R_2 tightness, or with (T) only at row ⊥, fails Cert1/TopCell-type
  statements (frontier, §278–§281); in this brief the cell cannot be dropped (M:TopCellAll fails on every branch).
- Design rules on file: use the orbit only as data, not as the certificate; carry the index bound from R_0; termination
  measures must use F; no local or bounded-lookahead progress lemma; qualitative claims about R(F) are theorems on finite
  lattices (only stage forms are testable). At level 1 every statement here is a stage form.
- Process rule: the worker does not touch the checkout while briefers run.

## Formalization order (Lean, no `sorry`, no new axioms; smallest first, all in section `Landing`)

1. `le_land_of_ownCell`: q ≤ F(q, p) with p = (F q)^[i] ⊤ gives q ≤ p (`rowIter_succ_le`).
2. **`good_atom_unique_below`** (Lemma U): m ∈ R_1, q, q′ atoms, q ≤ m, q′ ≤ m, both good, h(⊤) > 2 ⟹ q = q′.
   Uses `ownCell_of_good`, `upTrap_land`, `tb_of_tight`, `aIter_mem`, `land_not_le`, `height_strictMono`.
3. **`topCell_iff_goodBelow`** (Lemma T): for m ∈ R_1 with h(m) = 2 and landing index i (minimal index with height ≤ 2),
   (m ⊓ λ(m) has height 1 ∧ m ⊓ λ(m) ≤ F(m ⊓ λ(m), λ(m))) ⟺ ∃ q, h(q) = 1 ∧ q ≤ m ∧ IsGood F q.
4. `certAt_of_fixed_below` (Lemma D): q good, μ(q) = q, q ≤ m ∈ R_1 ⟹ m exits with exit atom q (a Cert1 witness).
5. `good_atom_cases` (Lemma C): the trichotomy of a good atom (F(q, λ(q)) = λ(q), or = q with λ(q) ∉ Z and μ(q) = q, or
   = q with λ(q) ∈ Z).
6. `goodAtom_of_localTop` (Programme 3): `goodAtom_of_greatestZ` with `hmax` replaced by the local hypothesis.
7. Define `NMGood F H` and `TopCert F H`; prove `goodAtom1_of_nmGood` (with the d-good case), `nmGood_of_topCert`,
   `cert1_of_topCert`, and from 3 the equivalence TopCell ⟺ (d good) ∨ NMGood.

## Expected report

One verdict per programme (taxonomy of the pipeline, section 6), each with its ladder update:
- Lead NMGood: expected `normal form` (Lemmas T, U, D in Lean), plus the worker's independent re-run of NMGood/TopCell at
  height 12 width 4 and height 11 width 5; then direct rounds on TopExit (ExitM2 with a mutant, and the choice of exit).
- Programme 2 TopCert: `new conjecture` holding with power at heights 11–12 (one encoding) and the ladder update
  TopCert ⟹ Cert1 ∧ NMGood; then a direct round on ExitM2 ⟹ TopCert.
- Programme 3 LocalTop: `conditional lemma` (the theorem, in Lean) and `refuted` or `new conjecture` for its existential
  after one probe.
- TopAbsorb, GoodFix, OneGood, MaxIdx2: `refuted` (this brief; re-check one model each with `replay278.py`-style replay).

## Frontier corrections

1. **TopCell is not a located certificate.** TopCell ⟺ (d is a good atom) ∨ NMGood (Lemma T, paper from `ownCell_of_good`,
   `upTrap_land`, `land_not_le`, `good_of_dominating_desc`). The frontier (§276 table, §278 "TopCell looks at the top of
   Z", §281 "global, top of Z") files it as a location; it is the target restricted to atoms below M2.
2. **Misplaced rung.** The ladder lists TopCell under "Below Cert1". Its payoff is GoodAtom1 directly
   (`good_of_dominating_desc`, own-row cell); TopCell ⟹ Cert1 is not known (it would need the cell on row ⊥). TopCell sits
   beside Cert1, not below it.
3. **Missing rung.** Run-13 A's TopCert (some m ∈ M2 exits with c(m) ≤ m) is not on the ladder. It implies both Cert1 and
   TopCell and holds with power at height 12 width 4 and height 11 width 5 (one encoding, this brief): it is the strongest
   live rung.
4. **New facts (paper, Lean-ready):** Lemma U (at most one good atom below any row of Z), Lemma D (a μ-fixed good atom
   below m makes m a Cert1 witness exiting to it), Lemma C (good-atom trichotomy), LocalTop ⟹ GoodAtom1.
5. **Failure signature incomplete.** §281's "every refuted rung is anchored at ⊥" misses the anchor-free universal forms
   (ExitDom, QEany, ExitGood, MuLoop, AtomOrb) and now TopAbsorb (top-anchored, universal): the shared feature is naming
   which row certifies, by a walk or for every row of a family.
6. **Stale room to fail.** The "Corpora and room to fail" section still states height 6 with height-6 corpora; the header
   states height 8; §281 makes it height × width × N. Only the last is current.
7. **Stale main ladder.** "Implication ladder (main; rewritten at dd0cd5a)" rung 3 still lists BotUp [O] "holds with power"
   and rung 5 BotTrack as the open step; both were refuted at height 6 in §34.3z²⁶⁸.
8. **Cert1 ⟺ CertAtom is a paper composition**, not one Lean theorem: Cert1 ⟹ CertAtom needs `exit_atom` (to turn
   q ≤ F(⊥, p) into F(⊥, p) = q) and `exitFixed_of_dom`; the converse is `cert_of_exitFixed` with x = q.
9. **Unverified list:** "TopCell on wide corpora: never run" is now answered — exact at height 10 width 4, height 12 width 4
   (including the cycle lattice) and height 11 width 5 (NMGood), one encoding. It needs the worker's second encoding.
10. **CURRENT STATE wording:** "Equivalently (h(⊤) ≥ 3): a(⊥) = ⊥ and (T)" should read "a(⊥) = ⊥, (T) and n1".
11. **Branch g at width:** on g, NMGood/TopCell/TopCert fail on 19/20 (h10), 7/8 (h12), 8/8 (h11) lattices: some F on g
    has no good atom below M2 (d, good, is then maximal in Z). The antecedent "d is not a good atom" is necessary.
12. **Four new refutations for the Refuted list:** GoodFix and OneGood (h12, |L| = 32), MaxIdx2 (h12, |L| = 27), TopAbsorb
    (h10, |L| = 27). ExitDom (on file, |L| = 12) also fails at height 10 width 4 (9 / 7 / 9 / 9 lattices), as a mutant.
