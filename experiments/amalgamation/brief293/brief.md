# Brief, run 18 — outside briefer (adjoint-math-research v1.0)

**Repository** /home/user/mordor at **b694349** (read-only: nothing in the checkout was written, built or changed; the
only git command run was `git log --oneline -1`). Checked at source: `lean/Mordor/Normalize.lean` (all of it:
`CertAtom`, `mem_one_iff`, `w0_of_T`, `succSet`, `nrm`, `nrmHom`, `nrm_desc`, `goodTop_of_certAtom`,
`goodTop_iff_certAtom`); `lean/Mordor/LateParent.lean` section `Landing` (lines 5455–6010: `land_not_le`,
`land_bot_lt`, `exit_atom`, `land_unique`, `trap_of_tb`, `domCoLand`, `tb_of_tight`, `exitFixed_of_dom`,
`upTrap_stay`, `upTrap_land`, `certAt_of_fixed_below`, `goodCell_dichotomy`, `ta_iff_lands`, `selfLow`, `GoodTop`,
`certAtom_of_goodTop`); log `docs/rounds/26-v3.7.md` §34.3z²⁸⁹–²⁹²; `experiments/amalgamation/brief291/brief.md` (in
full), `brief289/brief.md` (skimmed), `orbit_probe.py` (in full), `bank.py`, `bank/`, `direct292/`, `holding/`.
Everything this brief produced is in this directory: scripts, outputs (`*_out.txt`), run directories `run1/`–`run5/`,
saved models (`run*/`, `cex/`, `smoke/`).

**Mission (negation of the failure signature).** *Propagate a colour, do not predict a certificate.* Track one invariant
along the whole boundary of the region where two descents still meet high — the value of the atom's row there — and
let it carry the landing of one row to the landing of the other; the certificate then appears where the invariant
forces it, not where a walk or an extremal index points.

---

## 0. Summary

1. **New theorem (paper, complete, Lean-ready; checked free on 1 323 row pairs of 201 stored W0² models): the
   CornerColour / LandEq lemma.** For an atom q of Z and a row x ∈ Z above q, walk the boundary of the staircase
   {(j,k) : u_j(q) ⊓ u_k(x) high}. At every boundary point the value of row q is a low element ≰ q (Tb at a two-row meet
   column); consecutive values lie below one common low element; the first is ≤ λ(x), the last ≤ λ(q). Hence **if no
   boundary value is an atom, λ(x) = λ(q)** (§4.1).
2. **CertAtom (and TwoRowTb) holds in branch b/g with N = 1** (φ(⊤) = d an atom): every row of Z above d lands at λ(d),
   so λ(d) ∉ Z (else it self-lands) and φ(λ(d)) = d. Complete proof from on-file lemmas, uses only Tb at d at
   *staircase-boundary* columns (§4.2). This branch holds the smallest refuting models of Desc1 (|L| 10), Row1 (16) and
   LastEither (25); in 17 of the 20 stored B1 NoFix models the violated instance is exactly a boundary point the proof
   uses (the other 3 drop Tb at d altogether). Also proved: branch a with N = 1 when d has one atom below it, and the
   uniform-fibre case UF′ (§4.3); together 82 of the 191 stored W0 models (samples).
3. **Ladder audit.** (A1) the DMax "low meet column" case is vacuous: CertAtom(W0) ⟺ CertAtom(W0^meet) is proved.
   (A2) **TbFibre**: Tb at an atom q can only fail at a column w with φ(w) = q — the §292 anatomy "the violated value is
   always F(q, u⊓v) = q" is forced, not found. (A3) **TwoRowTb is ahead of CertAtom only on irreparable W0² models**
   (F♯ ∉ W0); all 10 stored W0²∖W0 models are repairable; run 1 searches the slice (§2, §8).
4. **Lead: StairTb**, CertAtom with Tb at atom rows only at staircase-boundary columns — a world strictly larger than
   W0² (fewer instances), a theorem on B1, conjecture elsewhere. Run 3: see §8. Decisive open step named: **connectors**
   (a boundary point whose value is an atom q′ ≠ q, then q′ = φ there).
5. P2 **Repair** (is TwoRowTb the target?), P3 **A1 connectors** (branch a, N = 1: the open half of N = 1; run 2: TwoRowTb
   0/33 at exact N = 1, Row1 mutant 26/33, 17 of them in branch a).
6. Frontier corrections: 14 (§13).

## 1. Frontier (restated; checked at source)

- L finite (`NoChain α (H+1)`), F monotone in both arguments, h = `height H`, φ = F(⊥,·), a(x) = gfp F(x,·).
  "High" = height ≥ 3, "low" = height ≤ 2. Row descent u_j(x) = (F x)^j ⊤ (a decreasing chain), λ(x) its first low
  element at index i(x), r_x = u_{i(x)−1}(x), succ_x(v) = F(x, v) for v on desc(x).
- **W0 ∧ n1**: a(⊥) = ⊥, R_2 tight, ⊤ ∉ R_2, R_1 not tight; then Z = R_1 = φ⁻¹(⊥) (`mem_one_iff`), and with ZT, n1,
  h(⊤) ≥ 3 it is (T) at every row of Z (`w0_of_T`): Ta(x) no high y with y ≤ F(x,y) (⟺ x lands, `ta_iff_lands`);
  Tb(x) no high y with F(x,y) ≤ x.
- **Open target CertAtom** (`CertAtom`, Normalize.lean): some atom q of Z with λ(q) ∉ Z and φ(λ(q)) = q (μ-fixed).
  ⟺ GoodTop (`goodTop_iff_certAtom`) ⟺ Cert1 (paper).
- **W0²** (§291): a(⊥) = ⊥, ZT, n1, h(⊤) ≥ 3, every row of Z lands, λ(m) ≰ m on M2, Tb at an atom q only at high
  u ⊓ v (u ∈ desc(q), v ∈ desc(x), x ∈ Z, q ≤ x). TwoRowTb = CertAtom in W0²; W0 ⊆ W0².
- d = last nonzero t_j of the ⊥-descent, N its index. Branch b/g (d an atom) with N = 1 is written **B1**; branch a
  (h(d) = 2) with N = 1 is **A1**.

## 2. Ladder audit

### A1. DMax: the "meet column is low" case is vacuous (paper, one line)
For a high y and an atom q, put w̄ = ⋀_{x′ ∈ Z, x′ ≥ q} σ_{x′}(y) (σ_{x′}(y) = least element of desc(x′) above y; it
exists, desc(x′) is a finite chain containing ⊤). Then **y ≤ w̄**, so w̄ is high whenever y is, and σ_{x′}(w̄) = σ_{x′}(y).
F♯(q, y) ≥ F(q, w̄) (q ≤ x′, w̄ ≤ σ_{x′}(y)), so Tb of F at the meet column w̄ gives Tb of F♯ at y. The worker's unchecked
case never arises. Consequences, proved: W0 ⊆ W0^meet ⊆ W0²; ♯ maps W0^meet into W0 with the same descents;
**CertAtom(W0) ⟺ CertAtom(W0^meet)**; W0² is closed under ♯ (F ≤ F♯ on rows of Z, Tb is up-closed in F, the other
W0² clauses depend on descents only).

### A2. TbFibre (paper, Lean-ready, two lines)
q an atom of Z, w high: F(q, w) ≤ q ⟹ F(q, w) = q and φ(w) = q.
*Proof.* F(q,w) ≥ φ(w) ≠ ⊥ (w ∉ Z by ZT); a nonzero element below the atom q is q; φ(w) ≤ q and ≠ ⊥. ∎
So Tb at q has content only on the fibre Φ_q = {w high : φ(w) = q}; atoms outside φ(Hi) have vacuous Tb. In B1,
φ(y) ≤ φ(⊤) = d for all y, so Tb at atom rows is Tb at d's row alone (agrees with §288 "uniqueness uses Tb only at d's
row"). The §292 anatomy "the violated instance is always F(q, u ⊓ v) = q" is A2, not an observation.
Corollary (trivial, recorded): every μ-fixed atom q lies below t_1 = φ(⊤) (q = φ(λ(q)) ∈ φ(L)); at N = 1 every
μ-fixed atom is ≤ d (census: 70/70 stored A1 models, 26/26 B1). FixBelowD's refutations are at N = 2.

### A3. Where TwoRowTb has content (audit of the pushed rung)
TwoRowTb exceeds CertAtom only on models F ∈ W0² with F♯ ∉ W0 (**irreparable**): if F♯ ∈ W0 then F♯ has F's
descents, so CertAtom for F♯ gives a fixed atom of F. Free check (`irrep_stored.py`): the repository holds 10 stored
W0²∖W0 models (bad1_*, single_claim_*, colasc_*, seeded_*; |L| 7–32, H 4–6) and **all 10 are repairable**. So no
stored model shows TwoRowTb saying more than CertAtom, and the §291 pushes of TwoRowTb are pushes of CertAtom on every
lattice where the irreparable slice is empty. Run 1 searches that slice exactly (§8); P2 states the question.
Note: TwoRowTb is not shown to be a restatement — a 3-row meet violation cannot be repaired by ♯ (♯ is the largest map
with the given descents), so a reduction W0² → W0 would have to move descents.

### A4. Placement of rungs on file, re-derived
- `goodTop_iff_certAtom`: checked in source; GoodTop is a restatement. ✓
- CertAtom ⟸ TwoRowTb (W0 ⊆ W0²): ✓. New: **TwoRowTb ⟸ StairTb** (Stair ⊇ W0², §4.4).
- "Cert1 ⟺ CertAtom [paper]": ✓ (`exitFixed_of_dom`, `cert_of_exitFixed`).
- G1/G2 ⟺ ExitZ/ExitToFix (via nrmHom): ✓. In B1 the split is irrelevant (the proof never asks whether a row exits).

## 3. Reuse (real names; `LateParent.lean` unless noted)
`land_not_le`, `land_bot_lt`, `exit_atom`, `land_unique`, `trap_of_tb`, `domCoLand`, `exitFixed_of_dom`, `tb_of_tight`,
`upTrap_stay`, `upTrap_land`, `certAt_of_fixed_below`, `ta_iff_lands`, `iter_antitone_of_le`, `iter_row_mono`,
`rowDesc_reaches_a`, `a_le_rowDesc`, `rowIter_succ_le`, `eq_of_le_of_height_ge`, `height_strictMono`,
`height_bot_eq_zero`; `CertAtom`, `mem_one_iff`, `w0_of_T` (Normalize.lean).

---

## 4. LEAD — Staircase colouring; StairTb

### 4.1 CornerColour / LandEq (paper, complete; Unverified until formalized)
Setting: q an atom of Z, x ∈ Z, q ≤ x, both rows land (i(q), i(x) finite). Put G(j,k) = u_j(q) ⊓ u_k(x), antitone in j
and in k. For l < i(q) let κ(l) = least k with G(l,k) low (κ(l) ≤ i(x) since G(l, i(x)) ≤ λ(x); κ(l) ≥ 1 since
G(l,0) = u_l(q) is high). κ is non-increasing; κ(0) = i(x) (G(0,k) = u_k(x)).
Boundary point l: B_l = G(l, κ(l)−1) (high), with G(l, κ(l)) low. **Boundary value** e_l = F(q, B_l).
Hypothesis used: **Tb at q at every boundary point** (Stair instances): e_l ≰ q.

1. e_l ≤ G(l+1, κ(l)). *Proof:* F(q, B_l) ≤ F(q, u_l(q)) ⊓ F(q, u_{κ(l)−1}(x)) ≤ u_{l+1}(q) ⊓ F(x, u_{κ(l)−1}(x))
   (q ≤ x) = u_{l+1}(q) ⊓ u_{κ(l)}(x).
2. A_l := G(l, κ(l)) is low, A_l ≥ G(l+1, κ(l)) ≥ e_l (step 1, antitone in j).
3. A_{l+1} = G(l+1, κ(l+1)) ≥ G(l+1, κ(l)) ≥ e_l (κ(l+1) ≤ κ(l)), for l+1 < i(q); and e_{i(q)−1} ≤ G(i(q), κ) ≤
   u_{i(q)}(q) = λ(q). So **the zigzag λ(x) = A_0 ≥ e_0 ≤ A_1 ≥ e_1 ≤ … ≥ e_{i(q)−1} ≤ λ(q)** runs through low elements,
   every e_l nonzero (≥ φ(B_l) ≠ ⊥, ZT) and ≰ q.
4. If e_l has height 2 then A_l = A_{l+1} = e_l (low elements above a height-2 element equal it); at the last point
   e = λ(q).
5. **LandEq.** If every boundary value has height 2, then λ(x) = A_0 = e_0 = … = e_{i(q)−1} = λ(q), of height 2. ∎
   A boundary value of height 1 is an atom q′ ≠ q with q′ = e_l ≥ φ(B_l) ≠ ⊥, hence q′ = φ(B_l) = F(q, B_l): a
   **connector**. If φ(B_l) ≥ q (B_l in φ⁻¹(↑q)), then e_l ≥ q, e_l ≠ q, so e_l has height 2 — no connector.
Free check (`corners.py`, `corners2.py`, `pairstats.py`, outputs beside them): the claims hold on all 1 323 pairs (q, x)
of the 201 stored models that lie in W0² (191 W0, 10 W0²∖W0): no boundary value is ≤ q; 845 pairs have no connector and
all 845 land together; 478 have a connector, 298 of them land differently (every differently-landing pair has one).

### 4.2 Theorem B1 (paper, complete): CertAtom holds in W0², hence in W0, when N = 1 and d is an atom
Hypotheses: a(⊥) = ⊥, ZT, h(⊤) ≥ 3, every row of Z lands, λ(m) ≰ m on M2, Tb at d at the boundary points of the
(d, x)-staircases (x ∈ Z above d), φ(⊤) = d an atom, φ(d) = ⊥.
1. *Fibre.* For high w: φ(w) ≤ φ(⊤) = d and φ(w) ≠ ⊥ (ZT), so φ(w) = d. [d ∈ Z: φ(d) = φ²(⊤) = ⊥.]
2. *No connectors.* Every boundary point B is high, so φ(B) = d ≥ d; by 4.1 step 5's last sentence every boundary value
   has height 2.
3. *LandEq* for each x ∈ Z above d (x = d included): λ(x) = λ(d) =: p, h(p) = 2, and p ≥ e > d (step 2, e ≥ φ(B) = d).
4. *p ∉ Z.* Else p ∈ Z, p ≥ d, so (3 with x := p) λ(p) = p ≤ p, against λ(m) ≰ m (in W0: `land_not_le`).
5. *Fixed.* φ(p) ≠ ⊥ (p ∉ Z), φ(p) ≤ φ(⊤) = d, so φ(p) = d: d is μ-fixed (λ(d) = p ∉ Z, F(⊥, λ(d)) = d). ∎
Hypothesis use per step (tested on the bank, `b1_corner_viol.py`): Tb at d at boundary points (steps 2–3) is what every
B1 NoFix model of a relaxed world violates — 17 of the 20 stored B1 NoFix models (Desc1 10 and 35, Row1, LastEither,
LastLast, s291 nofix models, …) fail it at a boundary point of the (d, λ(d))-staircase, the other 3 (brief289 role runs
noTb1, noTbD) drop Tb at d entirely; λ(m) ≰ m (step 4) is what the W0♭ witness models drop (nrmHom, §291); ZT (step 1)
is the fibre. Nothing else is used: no exit/no-exit split, no Ta beyond landing, no Tb at height-2 rows, no rows outside
↑d. In Lean (W0 form): Tb from `tb_of_tight`, step 4 from `land_not_le`, the zigzag by induction on l downward with the
invariant A_l = λ(d) (base l = i(d)−1: e ≤ λ(d); step: A_l ≥ e_l = A_{l+1}).

### 4.3 Further proved cases (paper, complete)
- **UF′ (uniform fibre).** If an atom q of Z has q ≤ φ(w) for every high w and φ(r_q) ∈ Z, then q is μ-fixed.
  Steps 2–4 of 4.2 verbatim (φ(B) ≥ q); then φ(r_q) ≥ q and φ(r_q) ≤ F(q, r_q) = p, so φ(r_q) ∈ {q, p}, and
  φ(r_q) ∈ Z, p ∉ Z give φ(r_q) = q, φ(p) ≤ q, φ(p) = q.
- **A1-thin.** Branch a, N = 1, exactly one atom q_0 below d: φ(Hi) ⊆ {q_0, d} ⊆ ↑q_0, and φ(r_{q_0}) ∈ {q_0, d} ⊆ Z, so
  UF′ applies.
- **FixSink.** If q is μ-fixed (W0², `upTrap_land` uses Tb only at two-row meets), every row of Z above q lands at
  p = λ(q); every grid point with j ≤ i(q), k ≤ i(x) is ≥ p, so φ(B) ≥ φ(p) = q at every boundary point: a fixed atom
  has no connectors. (Census, samples: at all 191 stored fixed atoms every staircase corner has φ(B) ≥ q; no non-fixed
  atom has both that and φ(r_q) = q.)
- **A1 location (paper).** In A1 a μ-fixed atom q*, if it exists, is φ(r_d): q* ≤ φ(⊤) = d (A2), so d lands at
  p = λ(q*) (`upTrap_land`), and q* = φ(p) ≤ φ(r_d) ≤ p ⊓ d, an atom (p ∉ Z, d ∈ Z). In B1 it is d. The location is
  forced, not predicted.
Coverage (samples only, `beta_census.py`): UF′ applies to 82 of 191 stored W0 models (B1 26/26, A1 45/70, N ≥ 2 11/95).

### 4.4 Candidate lemma (conjectural) — StairTb
**Stair world:** a(⊥) = ⊥, ZT, n1, h(⊤) ≥ 3, every row of Z lands, λ(m) ≰ m for m ∈ M2, and for every atom q of Z only
the instances F(q, u ⊓ v) ≰ q with u ∈ desc(q), v ∈ desc(x), x ∈ Z, q ≤ x, **u ⊓ v high and u ⊓ succ_x(v) low**.
**StairTb:** in the Stair world some atom of Z is μ-fixed.
- **Conditional payoff (complete).** Stair ⊇ W0² ⊇ W0 (each Stair column is a W0² column), so StairTb ⟹ TwoRowTb ⟹
  CertAtom ⟹ GoodAtom1 (`goodAtom1_of_cert1`) and GoodTop (`goodTop_iff_certAtom`).
- **Placement.** Strictly above TwoRowTb as a statement (larger world). Incomparable with Row1 (Stair keeps only r_x
  among single descent elements) and with LastEither (Stair lacks most single elements, has every boundary point).
  Proved on B1 (4.2) and UF′.
- **Testability.** Finitely refutable (`stair_probe.py`). **Hypothesis world**: Stair ∧ NoFix. Not vacuous by
  construction: it contains W0² ∧ NoFix; relaxed relatives (Row1, LastEither) have models. Bank replay
  (`replay_stair.py`): 201 stored models lie in Stair, every one has a fixed atom; 0 failures.
- **Counterexample anatomy.** Off B1 a counterexample needs a pair (q, x) with λ(x) ≠ λ(q) whose zigzag passes a
  connector (an atom q′ = φ(B) = F(q, B) at a boundary point) — so φ must take two atom values on high elements (N ≥ 2,
  or N = 1 in branch a with ≥ 2 atoms below d), at least three rows of Z above q or two atoms below a common row, and a
  boundary of length ≥ 2. Room: H (anatomy of the B1 relatives: H 8–10), width, N, number of atoms in φ(Hi) (new
  dimension, `beta_census.py`), boundary length i(q).
- **Mode.** Signature inversion (an invariant propagated along the staircase boundary instead of a predicted row) +
  ladder audit (A2 localises Tb to fibres). **Limit.** The colour argument needs every boundary value of height 2; a
  connector breaks the chain, and the chain alone does not say where it lands next.
- **Decisive open step — ConnectorClose.** In Stair ∧ NoFix: show that a connector at a boundary point B of (q, x)
  (F(q, B) = φ(B) = q′ ≠ q, an atom) produces a boundary Tb violation for q′ or a pair (q′, x′) whose zigzag has
  strictly fewer connectors (a well-founded measure: e.g. the number of connectors summed over pairs, or the boundary
  length). Two facts already hold at a connector: the three grid points G(l+1, κ(l)−1), G(l, κ(l)), G(l+1, κ(l)) are low
  and ≥ q′, and Tb at q′ at B (available in W0, not in Stair) gives F(q′, B) > q′. The relaxed B1/A1 models all choose the
  other escape: 17/17 Row1 A1 NoFix models of run 2 fail Tb at a boundary point of q_0 = φ(r_d) and have no connector
  (`a1_q0.py`).

## 5. Other programmes

### P2 — Repair: is TwoRowTb the target in other words?
- **Candidate (conjectural normal form).** Every F ∈ W0² is repairable: F♯ ∈ W0.
- **Payoff (complete).** Repair ⟹ (TwoRowTb ⟺ CertAtom): given F ∈ W0² ∧ NoFix, F♯ ∈ W0 has the same descents (A1),
  so it is a W0 ∧ NoFix model. TwoRowTb would then be a **restatement** (as GoodTop was), and its pushes CertAtom's.
- **Proved part (paper, complete): Repair holds at every connector-free atom.** If every row x ∈ Z above q lands at one
  height-2 p > q (e.g. LandEq with no connector), then for every high w each succ_{x′}(σ_{x′}(w)) sits at an index
  ≤ i(x′) of a decreasing chain ending at p, so F♯(q, w) = ⋀ succ_{x′}(σ_{x′}(w)) ≥ p > q: W0's Tb at q holds. So an
  irreparable model needs an atom with rows above it landing at different points, i.e. (4.1) a connector.
- **Placement.** A ladder-audit rung beside TwoRowTb; independent of its truth.
- **Testability.** Finitely refutable: SAT = an irreparable W0² model (`irrep_probe.py irrep`). Not vacuous: W0 ⊆ W0².
  Control (`irrep_probe.py … D1`, the refuted relative Desc1 world): irreparable models on 2/2 bank lattices (smoke).
- **Anatomy.** An atom q, ≥ 2 rows of M2 above q, a ≥ 3-row σ-meet column w in Φ_q (A2) with ⋀_{x′} s_{x′}(w) = q while
  every two-row column (with q's row) keeps a value > q. **Mode:** ladder audit. **Limit:** says nothing about existence.
  **Decisive step:** if Repair fails, its smallest model is the first lattice where TwoRowTb has room beyond CertAtom; if
  it holds, a paper proof (a three-row meet violation forces a two-row one in DMax form) would reclassify TwoRowTb.

### P3 — A1 connectors (branch a, N = 1: the open half of N = 1)
- **Candidate (conjectural).** CertAtom (equivalently TwoRowTb, StairTb) holds when N = 1 and h(d) = 2.
- **Payoff.** It closes N = 1 with 4.2. In A1, any exit of d is dominated (φ(λ(d)) ≤ φ(⊤) = d), so NoFix forces
  λ(d) = m ∈ M2 with m ⊓ d = q_0 = φ(r_d) (an atom), and then (4.1) some (q_0, x)-staircase has a connector q′, an atom
  below d other than q_0 (A2: connectors lie in φ(Hi) ⊆ ↓d). Proved when d has one atom (A1-thin, 4.3).
- **Testability / world.** Finitely refutable; Stair ∧ A1 ∧ NoFix empty on run 2's corpora for W0² (0/33). Relaxation
  with models: Row1 at N = 1 (17 A1 models in run 2), and the sharper relaxation the worker should build: Row1 + Stair
  instances at q_0 only — its NoFix models, if any, must carry a q_0-connector and are the anatomy of ConnectorClose.
- **Anatomy.** ≥ 2 atoms below d, a connector q′ < d. **Mode.** Signature inversion applied to the largest W0 class
  (70/191 stored). **Limit.** A1 only. **Decisive step:** ConnectorClose with q, q′ both below d and x = d available
  above both (d ≥ every atom of φ(Hi)).

## 6. Probe scripts (this directory; PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation)
- `irrep_probe.py` — exact SAT, one-hot rows of height ≤ 2 (same scheme as `orbit_probe.py`, written from the
  definitions). World W0² (λ(m) ≰ m, landing, Tb at atoms at two-row meets via descent-membership literals D). Mode
  `irrep`: SAT = exists F ∈ W0² and an atom q and high w with ⋀_{x′∈Z, x′≥q} succ_{x′}(σ_{x′}(w)) ≤ q (encoded as: for
  every minimal e ∉ ↓q some row x′ ≥ q has succ_{x′}(σ_{x′}(w)) ≱ e; σ through "u_j ≥ w ∧ u_{j+1} ≱ w"). `irrepnf` adds
  NoFix. Flag `D1` = control world Desc1. Replay: decoded F re-checked from the definitions (`corners.w0sq`), F♯ built
  and tested ∉ W0 (`dmaxviol.sharp`, `world.W`); assertion on mismatch; all SAT models saved.
- `stair_probe.py` — same scheme; Tb at atom rows only at Stair columns (clause over u1 ∈ desc(q), u2 ∈ desc(x),
  u3 = F(x,u2) with u1 ⊓ u2 high, u1 ⊓ u3 low); mode `nofix` (SAT = Stair ∧ NoFix); flag E1. Replay `stair_world` from
  the definitions + NoFix.
- `orbit_probe.py` (repository, unchanged) for the mutants Row1 and LastEither and for Meet2 (= W0²) at E1.
- Free analyses (no search, from the definitions): `corners.py`, `corners2.py`, `b1_corner_viol.py`, `boundary_viol.py`,
  `a1_q0.py`, `dmaxviol.py`, `violdetail.py`, `irrep_stored.py`, `replay_stair.py`, `census_fix.py`, `beta_census.py`,
  `clean_census.py`, `unclean_fixed.py`, `sink_census.py`, `gate_census.py`, `save_cex.py`, `inspect.py`.

## 7. Report lines
```
StairTb (LEAD) | stair_probe.py nofix (exact) | exists F in Stair: SAT = no atom of Z is mu-fixed
  run 3: tall 8 4 1 12 (12) + tall 10 4 2 20 maxn 40 (17) + tall 12 4 1 8 maxn 40 (4): H 8/10/12, |L| 16-35, width 4-9
     candidate SAT 0/33 | mutant LastEither (refuted relative, bank s292_lasteither_h10) SAT 10/33
     mutant models by branch: atom N1 5, a N1 3, a N2 2
  run 5: exact N = 2 and 3 on tall 12 4 1 8 maxn 40 (4 lattices each, H 12, |L| 27-34, width 6-8); exact N = 1, 2 on
     tall 10 6 1 8 maxn 40 (1 lattice, |L| 35, width 8)
     candidate SAT 0/10 | mutant LastEither SAT 6/10: atom N2 3, atom N3 2, atom N1 1
  bank replay (free): 201 stored models in Stair, 0 failures
  room reached: H 12, width 9, N 1-3 (exact) | anatomy needs: a connector pair (two atom values of phi on high elements),
     boundary length >= 2; smallest coordinates unknown off B1
  branch atom, N = 1 (B1): THEOREM (4.2); run agrees (0 failures; mutant 6 models)
  branch a, N = 1:  mutant models 3 | candidate failures 0 -> provisional
  branch a, N = 2:  mutant models 2 | candidate failures 0 -> provisional
  branch atom, N = 2, 3: mutant models 5 (run 5) | candidate failures 0 -> provisional
  branch a, N >= 3; branch g as such: silent (no mutant model)
          -> provisional at H <= 12, width <= 9, N <= 3; one encoding (this briefer's); width M 6-7 with |L| > 40, H 13-14 owed
TwoRowTb at exact N = 1 | orbit_probe.py nofix 0 Meet2 E1 (exact; the worker's encoding) | SAT = no mu-fixed atom in W0^2
  run 2: tall 8 4 1 12 + tall 10 4 2 20 maxn 40 + tall 12 4 1 8 maxn 40: 33 lattices, H 8/10/12, |L| 16-35, width 4-9
     candidate SAT 0/33 | mutant Row1 E1 (refuted relative, bank s292_row1_h8 lies in B1) SAT 26/33: a 17, atom 9
  branch atom (B1): theorem; branch a (A1): mutant models 17 | candidate failures 0 -> provisional (A1, P3)
  free follow-up: all 26 Row1 models fail Tb at a staircase-boundary point (boundary_viol.py); the 17 A1 models fail it
     at a boundary point of q_0 = phi(r_d) and have no connector (a1_q0.py)
Repair (P2) | irrep_probe.py irrep (exact) | exists F in W0^2 with F# not in W0: SAT = Repair fails (TwoRowTb has room)
  run 1: closure 5 11 4 30: 26 lattices (H 4-5, |L| 9-20) UNSAT; stopped by the briefer (encoding speed)
  run 4: tall 8 4 1 12 maxn 30: 8 lattices (H 8, |L| 16-29, width 4-8) UNSAT, then the cap (exit 124); tall 10 and
     closure 6 not reached
  control (smoke, D1 = Desc1 world, irrepnf): SAT 2/2 bank lattices (s292_row1_h8, brief291 desc1 min10)
  stored models (free): 10 W0^2 \ W0 models, all repairable
          -> no irreparable model found; silent as evidence for Repair (no refuted relative in the W0^2 family is known to
             have irreparable models except Desc1-type worlds, which are not W0^2); a search with room is owed
```

## 8. Runs (budget 5 exact runs, ≤ 1500 s each, ≤ 2 in parallel)

| run | job (cwd `runK/`, script `runK.sh`) | wall |
|---|---|---|
| 1 | `irrep_probe.py irrep maxn 40` on closure 5 11 4 30 + tall 8 4 1 12 + tall 10 4 2 20 | stopped by the briefer at ≈ 640 s (encoding too slow; 26 closure lattices done) |
| 2 | `orbit_probe.py nofix 0 Meet2 E1` and `… Row1 E1` on tall 8 4 1 12, tall 10 4 2 20 maxn 40, tall 12 4 1 8 maxn 40 | ≈ 240 s |
| 3 | `stair_probe.py nofix` and mutant `orbit_probe.py nofix 0 LastEither` on the same three corpora (all N) | ≈ 390 s |
| 4 | `irrep_probe.py irrep fast maxn 30` on tall 8 4 1 12 + tall 10 4 2 20 + closure 6 12 1 40 | 1500 s (cap; 8 of the 12 tall 8 lattices with |L| <= 30 done, one took 835 s) |
| 5 | `stair_probe.py nofix E2/E3` + mutant LastEither E2/E3 on tall 12 4 1 8 maxn 40; E2/E1 on tall 10 6 1 8 maxn 40 | ≈ 260 s |

Runs 1 and 2, then 3 and 4, then 4 and 5 ran in parallel (never more than two jobs).

## 9. Pushes owed
- **StairTb**: second, independent encoding (worker); H 13–14 (`tall 13 4 1 8`, `tall 14 4 2 20`), width M 6–7 with
  |L| > 40 (`tall 10 6 1 8`, `tall 10 7 1 5` — run 5 reached only the |L| 35 lattice of the M 6 corpus), exact N 4–6, and
  branch a with N ≥ 3 (silent: no mutant model yet). Each push paired with LastEither under the same flags.
- **TwoRowTb in A1 (P3)**: the same pushes at E1 with the branch read off the model lines (flag `Ba` is ignored in nofix).
- **Repair (P2)**: an encoding fast enough for |L| 30–45 at H 8–12 (suggestion: solve per (q, w) with assumptions, or
  build F♯ in the encoding and assert one W0 Tb clause fails), then the same corpora as StairTb.
- **Formalization** of A2, LandEq, Theorem B1, UF′ (§12) — they are complete on paper and need no search.

## 10. Already failed — do not repeat
All of frontier §4, plus (this brief, free refutations on stored W0 models, saved in `cex/`):
- **CleanExists** (some atom q with φ(r_q) = q and φ(B) ≥ q at every staircase corner): fails on 22 stored W0 models
  (smallest |L| 5); the fixed atom there has φ(r_q) = λ(q). The colour argument must allow φ(r_q) = λ(q).
- **SinkExitFix** (a non-fixed sink — every row above q lands at λ(q) ∉ Z — exits to a fixed atom): fails on 4 stored W0
  models (37/41; smallest |L| 15).
- **GateRank** for ρ ∈ {#φ⁻¹(↑q) ∩ Hi, #Φ_q, dep, i(q)}: along stored gates (atom colours at corners) ρ is not
  increasing (55–99 refuting models each). A ranking for ConnectorClose must be something else.
- Located predictions of the fixed atom (maximal preimage count: 22 of 191 fixed atoms are not maximal).

## 11. Hard constraints
- Sharpness on file (branch g for top-layer statements; R_2 tightness) unchanged. In B1 the branch g/b distinction is
  irrelevant (4.2 does not use badness of d).
- Tb at atom rows is used only on fibres (A2), and in B1 only at staircase-boundary points (4.2). Desc1 (own descent) is
  refuted; Stair keeps the boundary points of every pair (q, x).
- Every proof must handle connectors: λ(x) ≠ λ(q) for some q ≤ x occurs in 287 stored W0 pairs (all with a connector).

## 12. Formalization order (no sorry, no new axioms)
1. `tbFibre` (A2) and the corollary "μ-fixed ⟹ q ≤ F ⊥ ⊤".
2. The zigzag lemma for one pair (4.1 steps 1–5) with Tb at q at the boundary points as hypothesis (W0 instance:
   `tb_of_tight`). Suggested shape: for l < i(q), κ(l) via `Nat.find`; invariant by downward induction on l.
3. `certAtom_of_N1` (4.2) in W0 form: hypotheses of `CertAtom` plus `F ⊥ (F ⊥ ⊤) = ⊥` and `height H (F ⊥ ⊤) = 1`.
4. UF′ and A1-thin. 5. The Stair-world version (B1 needs no other Tb instance) and FixSink.
6. Then P2 (paper or refutation) and ConnectorClose.

## 13. Frontier corrections
1. **§2 W0² bullet / §292 anatomy**: "the violated instance is always F(q, u ⊓ v) = q" is forced by TbFibre (A2) for any
   Tb violation at an atom row; delete it as a finding and record A2 (Tb at q lives on Φ_q = {high w : φ(w) = q}).
2. **§2 normal forms, DMax**: the unchecked case "the meet column w is low" is vacuous (A1: w̄ ≥ y). Mark the design rule
   proved on paper; add W0 ⊆ W0^meet ⊆ W0² ⊆ Stair, ♯ : W0^meet → W0, and "W0² is closed under ♯".
3. **§2 ladder**: add CornerColour/LandEq, Theorem B1 (CertAtom, TwoRowTb and StairTb on N = 1 with d an atom), UF′,
   A1-thin, FixSink, A1 location (all paper, complete, Unverified until formalized); add StairTb [prov] above TwoRowTb.
4. **§2 MeetViolation**: on B1 it is answered — the violated column is a staircase-boundary point of a (d, x)-pair, x ∈ Z
   above d with λ(x) ≠ λ(d) (17/20 stored B1 NoFix models; the other 3 drop Tb at d). Its two "open cases" (ExitZ; exit
   atoms outside their rows) are irrelevant on B1. Restate the open part as "off B1 ∪ UF′", decisive step ConnectorClose.
5. **§2 TwoRowTb "pushed"**: its content beyond CertAtom lives only on irreparable W0² models (A3); the 10 stored W0²∖W0
   models are repairable and runs 1/4 found none on 26 lattices at H 4-5 and 8 at H 8, |L| <= 29 (§8). Until one is found, TwoRowTb's pushes are CertAtom's pushes on those
   lattices; Repair holds at every connector-free atom (P2, paper).
6. **§4 failure signature / §8 set-aside "every ⊥-anchored location is refuted"**: qualify — at N = 1 the μ-fixed atom is
   forced: d in B1 (theorem), φ(r_d) in A1 (paper, if it exists). The refuted ⊥-anchored routes are at N ≥ 2 or predict
   beyond what TbFibre forces.
7. **§2/§9 FixBelowD**: every μ-fixed atom lies below t_1 = φ(⊤) (A2 corollary); so FixBelowD holds at N = 1; its
   refutations (s288_*) are N = 2.
8. **§10 corpora / tester rules**: in `orbit_probe.py` the flags `Ba`/`Bb` are read into `BR` but used only in the
   topcert/nmgood/exitm2/twofix family; in modes `nofix`, `noexit`, `exitnofix`, `goodtop`, `Mgoodtop` they parse to
   nothing (a run "nofix … Bb" is unrestricted in branch). Branch must be read off the printed "model: branch" lines.
9. **§6 room vector**: add (i) the number of atoms in φ(Hi) (= 1 exactly on B1, where the target is a theorem), (ii) the
   number of connectors of a pair and the boundary length i(q), (iii) N per branch: branch atom with N ≥ 2 had no mutant
   model in run 3 (silent there) — see run 5.
10. **§7 design rules**: add "Tb at atom rows is used only on fibres Φ_q (A2); on B1 only at staircase-boundary points
    (4.2); λ(m) ≰ m is used once, to exclude a common landing inside Z".
11. **§9 vacuity map**: Stair ∧ NoFix: no model (runs 3, 5); LastEither ∧ NoFix has models in branch a (N 1, 2) and in B1;
    the irreparable slice W0² ∧ (F♯ ∉ W0): no model on runs 1/4 (§8); the Desc1 control has irreparable models (smoke).
12. **§10 speeds**: `orbit_probe.py nofix 0 Meet2 E1` and `Row1 E1` on tall 8 4 1 12 + tall 10 4 2 20 maxn 40 +
    tall 12 4 1 8 maxn 40 (33 lattices, |L| 16–35) take about 4 minutes together (run 2): exact N = 1 makes Meet2 fast.
    The irreparable-slice encoding is slow (19–75 s per lattice at |L| 19–21 even with the TbFibre restriction).
13. **§4 refuted routes**: add CleanExists (22 stored W0 models, smallest |L| 5), SinkExitFix (4, |L| ≥ 15), GateRank
    for #φ⁻¹(↑q), #Φ_q, dep, i(q) (55–99 models each) — files `cex/*.json` in this brief's directory (copies of stored
    models, sources recorded per entry).
14. **§3 buckets**: Unverified (one encoding, this briefer): StairTb (runs 3, 5), Repair (runs 1, 4), TwoRowTb at E1 per
    branch (run 2 uses the worker's `orbit_probe.py`, so it is a second run of the worker's encoding, not an independent
    one). Paper: A1, A2, LandEq, B1, UF′, A1-thin, FixSink, A1 location, Repair-at-connector-free.
