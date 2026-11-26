# Brief, run 16 — outside briefer (adjoint-math-research v1.0)

**Repository** /home/user/mordor at **b2ab19e** (read-only; nothing in the checkout was written, built or changed).
Sources checked: `lean/Mordor/LateParent.lean` section `Landing` (lines 5453–5903) plus `IsGood`, `not_good_of_ahead`,
`ownCell_of_good`, `goodAtom1_iff_ownCell1`, `Cert1`, `goodAtom1_of_cert1`, `DescChain`, `descChain_of_good`,
`good_of_descChain`, `BackGood1`; log `docs/rounds/26-v3.7.md` §34.3z²⁸⁵–²⁸⁸; `experiments/amalgamation/{bank.py,
orbit_probe.py, tight_probe.py, cert1_sat.py, bank/}`. All probe scripts, outputs and models are in this directory.

**Mission (negation of the failure signature).** Stop locating the certificate. Work in a world where the fixed set is
*allowed to be empty*, and show that emptiness forces a global, unnamed violation that the real world forbids by a
lemma already in Lean. Concretely: in W0 with Tb dropped at the height-2 rows, "no μ-fixed atom" must make *some*
top-layer element good — and `not_good_of_ahead` says no top-layer element is good in W0.

---

## 1. Frontier (restated; everything below checked at source)

- L finite (`NoChain α (H+1)`), F monotone in both arguments, a(x) = gfp F(x,·), b(y) = lfp F(·,y), h = `height H`.
  φ := F(⊥,·). Z = R_1 = {y : φ(y) = ⊥}. M2 = {m ∈ Z : h(m) = 2}. Atoms of Z: A.
- **World W0 ∧ n1** (= the hypotheses of `GoodAtom1`/`Cert1`): a(⊥) = ⊥; R_2 tight; ⊤ ∉ R_2; R_1 not tight. With
  h(⊤) ≥ 3 this is: a(⊥) = ⊥, ZT (Z has heights ≤ 2), n1 (M2 ≠ ∅), and (T) at every row x ∈ Z:
  **Ta(x)**: no y with h(y) ≥ 3 and y ≤ F(x,y) (⟺ row x lands, `ta_iff_lands`);
  **Tb(x)**: no y with h(y) ≥ 3 and F(x,y) ≤ x (`tb_of_tight`).
- Row descent u_j(x) = F(x,·)^j(⊤); landing λ(x) = first element of height ≤ 2; i(x) its index. Exit: λ(x) ∉ Z;
  then c(x) = φ(λ(x)) is an atom of Z and h(λ(x)) = 2 (`exit_atom`). μ(x) = λ(x) if λ(x) ∈ Z, else c(x).
  **μ-fixed atom** q: λ(q) ∉ Z and φ(λ(q)) = q. ⊥-descent t_j, d = last nonzero t_j, N its index.
- **Open target CertAtom**: in W0 ∧ n1 some atom of Z is μ-fixed (⟺ Cert1, paper; ⟹ GoodAtom1 by `goodAtom1_of_cert1`).
- `IsGood F p` := p ≤ a(p) ∨ ∃ i, u_i(p) = p. `not_good_of_ahead` (j = 1): with R_2 tight, x ∈ R_1, h(x) ≥ 2, x ≠ ⊤ ⟹
  ¬IsGood x. So **in W0 no element of M2 is good** (Lean).

## 2. Ladder audit (re-derived from the cited lemmas)

| # | rung / claim on file | re-derivation | finding |
|---|---|---|---|
| A1 | GoodAtom1 ⟺ OwnCell1; Cert1 ⟹ GoodAtom1; TopExit = TopCert = FixBelow ⟹ Cert1; NMGood ⟹ ExitM2; TopCert ⟹ NMGood; TopZ ⟹ GoodAtom1 | checked against `goodAtom1_iff_ownCell1`, `goodAtom1_of_cert1`, `fixedBelow_of_exitDom`, `certAt_of_fixed_below`, `goodUp`, `goodAtom_of_inCert`, `goodAtom_of_greatestZ` | placements correct |
| A2 | **AtMost1Fix** and **FixMax** (pushed new conjectures) | both are universal statements over the fixed set | **They hold vacuously on every model where CertAtom fails.** Neither is below the target, so no proof of either reduces CertAtom. They are corollary-side rungs: they say what the certificate looks like *when it exists*. The §288 direct round (a proof attempt on AtMost1Fix) was therefore orthogonal to the open target. |
| A3 | "OneFix ∧ FixMax ⟹ TopExit off g" | CertAtom gives a fixed q; FixMax gives m ∈ M2 with q ≤ m; `certAt_of_fixed_below` makes m exit to q ≤ m | **AtMost1Fix is not used**: the correct rung is *CertAtom ∧ FixMax ⟹ TopExit (off g)*. |
| A4 | decisive step "count-to-existence: prove AtMost1Fix, then existence from a global invariant" | role data below (run 1) vs §286 | AtMost1Fix holds without Tb at the height-2 rows (§286, h5); **CertAtom fails without Tb at the height-2 rows on 82 of 82 lattices** (run 1). Any invariant that yields existence must use the height-2 rows; a proof of AtMost1Fix cannot contain it. Drop AtMost1Fix from the decisive step. |
| A5 | **normal form for the real level-1 need** (new, paper, Unverified) | see Lemma N1 below | **GoodAtom1 ⟺ CertAtom ∨ StallExit**, StallExit := some atom q ∈ Z with q < a(q) (then a(q) = λ(q) ∉ Z and q exits). CertAtom is strictly stronger on paper than what BackGood1(1) needs; on every corpus run here both hold, and their roles coincide (run 2, `nogood` = `nofix` column by column). |
| A6 | TopExit / TopCert as "placed form" | TopExit ⟺ (some μ-fixed atom lies below M2) | not the target in other words: it is CertAtom ∧ (a fixed atom below M2); off g with FixMax the two coincide (A3). Correctly placed above Cert1. |

**Lemma N1 (paper, Unverified; uses only Lean lemmas).** In W0 ∧ n1 with h(⊤) ≥ 3: GoodAtom1 ⟺ ∃ atom q ∈ Z with
[φ(λ(q)) = q] ∨ [q < a(q)].
*Proof.* (⟸) `goodAtom_of_exitFixed`; or q < a(q) gives IsGood q (left disjunct). (⟹) Let q be a good atom of R_1.
`goodUp` with m := q gives p, h(p) = 2, q ≤ F(q,p), F(⊥,p) ≠ ⊥ and j with u_j(q) = p, earlier elements high; so p = λ(q).
F(q,p) ≤ p (`rowIter_succ_le`). `goodCell_dichotomy`: either F(q,p) = q ∧ φ(p) = q — q is μ-fixed; or F(q,p) = p — then
p ≤ a(q) (`le_a`) and a(q) ≤ u_j(q) = p (`a_le_rowDesc`), so a(q) = p > q. ∎

## 3. Failure signature (recomputed)

On file (§285): every refuted route predicts which row certifies, or where the certificate sits. Still true of every
entry in §4 of the frontier, including §288's FixBelowD (a comparison element) and LandBelowD.
**Widened (this brief):** *the last two rounds argued about the certificate set only on worlds where it is non-empty.*
AtMost1Fix and FixMax (A2) are statements the empty fixed set satisfies; work on them cannot meet existence. Both halves
of the signature share one assumption: **the fixed atom is reasoned about as an object that is there.** Inversion:
argue from the world in which it is absent, and derive a contradiction that names no row.

Sharpness boundary (unchanged): branch g for top-layer statements; dropping R_2 tightness. **Refined by run 1–3**: the
existence half fails as soon as *any one* class of (T) is dropped (table §4), and survives exactly one weakening found
so far — Tb at the height-2 rows replaced by its descent form (DescTb2).

## 4. Role of the hypotheses in EXISTENCE (runs 1–3; new; small heights, suggestive only)

Exact SAT over all monotone F rows (one-hot, rows of low x), each model replayed from the definitions.
Corpus for each column: `closure 5 11 4 30 + closure 6 12 1 40 + tall 8 4 1 12` (82 lattices, heights 4–8, |L| 9–37).
Entry = lattices on which the relaxed world has a model with the stated failure (branch of that model: a / atom).

| relaxation of (T) at rows of Z \\ {⊥} | CertAtom fails (`nofix`) | GoodAtom1 fails (`nogood`) | ExitZ fails (`noexit`) | ExitToFix fails (`exitnofix`) |
|---|---|---|---|---|
| none (W0, control) | 0/82 | 0/82 | 0/82 | 0/82 |
| Tb dropped at height-2 rows (`noTb2`) | 82/82 | 82/82 | 82/82 | 81/82 |
| **Tb at height-2 rows → descent form λ(m) ≰ m (`desc2`)** | **0/82** | **0/82** | **0/82** | **0/82** |
| Tb dropped at atom rows (`noTb1`) | 82/82 | 82/82 | 82/82 | 82/82 |
| Tb at atom rows → descent form (`desc1`) | 79/82 | — | 79/82 | 79/82 |
| Tb → descent form at every row (`desc12`) | 79/82 | — | — | — |
| Tb dropped at d's row only (`noTbD`; d of either height) | 82/82 | 82/82 | 82/82 | 82/82 |
| Tb at d's row → descent form (`descD`) | 79/82 (all branch atom) | 79/82 | 79/82 (atom) | 79/82 (atom) |
| height-2 Tb kept only at d (`onlyD2`) | 82/82 (a: 10) | 82/82 | — | — |
| atom-row Tb kept only at d (`onlyD1`) | 79/82 (a: 77, atom: 2) | 79/82 | — | — |
| Tb kept only at d (`onlyD`) | 82/82 | 82/82 | — | — |
| Ta dropped at height-2 rows (`noTa2`) | 82/82 | 82/82 | 82/82 | 81/82 |
| Ta dropped at atom rows (`noTa1`) | 82/82 | — | — | — |

Reading (design rules, suggestive below room):
1. Existence uses **Ta at the height-2 rows** (they must land), **full Tb at the atom rows** (descent form is not
   enough: desc1 fails), **Tb at d's row** in both branches, and at the height-2 rows **only the descent form**.
2. By Lemma SelfLow (§6) the descent form at the height-2 rows is, given Tb at the atoms, exactly "no element of M2 is
   good" — the conclusion of `not_good_of_ahead`. So the height-2 rows enter existence **only through
   `not_good_of_ahead`** (equivalently `land_not_le` at m).
3. The decomposition CertAtom = ExitZ ∧ ExitToFix does **not** separate hypotheses: both halves fail under the same
   relaxations (run 3). Verdict on that split: `collapses` (no leverage), do not pursue.
4. GoodAtom1 and CertAtom have identical role columns: weakening the target to GoodAtom1 buys no hypothesis.
5. Contrast with §286: AtMost1Fix does not need Tb at the height-2 rows; existence does (A4).

Anatomy of the stored relaxed models that keep Tb at the atom rows (the 8 distinct W0♭ ∧ NoFix models of
`witness_stats_out.txt`, from runs 1–4): in every one the violation the real world forbids is a **top-layer element
landing on itself** (λ(m) = m, m good); in the models that drop Tb at atom rows the violation sits at an atom row instead: e.g. `run1/certrole_nofix_noTb2_min9.json`
(|L| 9, H 4, branch a): every row of Z lands at d = 5, including row 5 itself (a(5) = 5). In
`run2/certrole2_nofix_onlyD2_min9.json` (branch b) the self-landing element is 5 ≠ λ(⊥), on its own descent without
stalling. This is the observation the lead turns into a statement.

## 5. Reuse (real names, `LateParent.lean`)

`not_good_of_ahead` (line 4508), `upTrap_land`, `upTrap_stay`, `trap_of_tb`, `domCoLand`, `tb_of_tight`,
`land_not_le`, `land_unique`, `exit_atom`, `exitFixed_of_dom`, `cert_of_exitFixed`, `goodAtom_of_exitFixed`,
`goodUp`, `goodCell_dichotomy`, `ownCell_of_good`, `ta_iff_lands`, `good_of_dominating_desc`, `DescChain`,
`descChain_of_good`, `good_of_descChain`, `mem_succ_of_cell`, `le_a`, `a_le_rowDesc`, `rowIter_succ_le`,
`rowDesc_reaches_a`, `aIter_mem`, `Rk_down`.

---

## 6. LEAD programme — GoodTop: no fixed atom forces a good top-layer element (contradiction mode, transfer)

**World W0♭** := W0 ∧ n1 with Tb dropped at the height-2 rows of Z: a(⊥) = ⊥, ZT, n1, h(⊤) ≥ 3, Ta at every row of Z,
Tb at every atom row of Z. (W0 ⊆ W0♭.)

**Candidate lemma (conjectural) GoodTop.** In W0♭: if no atom of Z is μ-fixed, then some m ∈ M2 is good
(equivalently λ(m) = m: row m lands on itself).

**Small lemmas (paper, Unverified; for the worker to formalize first):**
- **SelfLow.** In W0♭, for m ∈ M2: λ(m) ≤ m ⟹ λ(m) = m.
  *Proof.* i(m) ≥ 1 (h(⊤) ≥ 3); let r = u_{i−1}(m), high, λ(m) = F(m,r). If λ(m) < m then h(λ(m)) ≤ 1. If λ(m) = ⊥:
  φ(r) ≤ F(m,r) = ⊥, so r ∈ Z with h(r) ≥ 3, against ZT. If λ(m) = q an atom: F(q,r) ≤ F(m,r) = q (monotone in the row,
  q ≤ m), a lower cell at the atom row q at a high column, against Tb(q). ∎ So in W0♭, DescTb2 ⟺ "no element of M2 is good".
- **GoodTopEq.** In W0♭, for m ∈ M2: IsGood m ⟺ λ(m) = m. (⟸: m on its own descent. ⟹: if m ∈ desc(m), the elements
  before it are > m, so λ(m) = m by heights; if m ≤ a(m), a(m) ≤ λ(m) has height ≤ 2 (Ta), so λ(m) ≥ m, hence = m.)
- **ZCellTop.** In W0♭, an atom q with z ∈ M2 on row q's descent and q ≤ F(q,z) (OwnZCell) makes row z land at z:
  `upTrap_land` with x := q, p := z, m := z (Tb at q, a(z) of height ≤ 2). So OwnZCell ⟹ GoodTop's conclusion.

**Conditional payoff (complete).** GoodTop ⟹ CertAtom. *Proof.* Assume W0 ∧ n1 and no μ-fixed atom. W0 ⊆ W0♭, so
GoodTop gives m ∈ M2 = Z ∩ {h = 2} with IsGood m. m ∈ R_1, h(m) = 2 ≥ 1 + 1, m ≠ ⊤ (⊤ ∉ R_2). `not_good_of_ahead`
(j := 1, using R_2 tight) gives ¬IsGood m. Contradiction. ∎ The same argument with "some nonzero element of Z is good"
(GoodZ, a consequence of GoodTop) gives **GoodAtom1 directly** (= BackGood1(1)'s open case), since M2 is excluded.

**Placement.** GoodTop (in W0♭) ⟺ [CertAtom ∨ GoodTop-conclusion] in W0♭ ⟹ CertAtom in W0 ⟹ GoodAtom1.
GoodTop ⟺ CertAtom in the DescTb2 world (by SelfLow), so it is **a strengthening of the target to a strictly larger
world**, and it is strictly stronger than its refuted relative OwnZCell (ZCellTop). Corollary GoodZ (some nonzero
element of Z is good, in W0♭) sits between GoodTop and GoodAtom1 and is BackGood1(1) with height-2 Tb dropped.

**Testability.** Finitely refutable in W0♭. Its hypothesis NoFix is *vacuous in W0* (that is the point: contradiction
mode); **relaxation named: drop Tb at the height-2 rows (W0♭)**, where NoFix has models on 82 of 82 lattices (run 1,
`noTb2`; branch a on 61, atom on 21). The negated hypothesis, CertAtom, stays the ladder's target.

**Hypothesis world.** NoFix ∧ W0♭: the target's counterexample branch, opened by one dropped hypothesis class. Both
branches (a and atom) have models there (run 1).

**Counterexample anatomy.** A W0♭ model with no μ-fixed atom in which every top-layer row lands on something other than
itself: by SelfLow the height-2 Tb violations must then sit at non-landing columns only (some F(m,y) ≤ m with y high and
y not the last high element of row m's descent), and no atom-row Tb may break. Smallest coordinates unknown; the
smallest W0♭ ∧ NoFix models have |L| = 9, H = 4 (so room starts at H 5); probe one step above in every dimension the
corpora reach: H 10 and 12; width (largest antichain) up to 12 at H 10 (M = 4), 11 at H 12, 19 at H 10 with M = 6
(`corpus_widths.txt`); N uncontrolled (see pushes owed).

**Mode.** Signature inversion (the set of good top-layer elements is shown non-empty; no member named — in 5 of the
8 stored W0♭ ∧ NoFix models the witness is not λ(⊥), in 4 it does not stall) + transfer lemma (a
level-1 failure moves goodness to the ahead layer, where Lean already forbids it).

**Limit.** It does not prove existence: the existence argument is moved, intact, into W0♭. What it gives: (i) the
height-2 rows may be treated as "rows that land and are not good" — every other use of Tb at m is provably unnecessary
if GoodTop holds; (ii) the end of the proof is fixed in advance (`not_good_of_ahead`), so a proof attempt is a search
for a *goodness-producing* mechanism at M2, of which the programme has two in Lean: DescChain at level 1
(`good_of_descChain`; its Z-version is OwnZCell, refuted below) and the stall m ≤ a(m).

**Decisive open step (named).** *GoodnessTransfer*: in W0♭ ∧ NoFix, produce m ∈ M2 with m ≤ a(m) or m ∈ desc(m). Data
(`witness_stats.py`, 8 distinct stored W0♭ ∧ NoFix models, samples only): the witness stalls (a(m) = m, m ≤ F(m,m)) in
4 and lies on its own descent without stalling in 4; it equals λ(⊥) in 3. So neither "the diagonal post-fixed point"
nor "the ⊥-landing" names it; a proof must produce the set, e.g. by showing that the family {u_j(m) : m ∈ M2} cannot
avoid every m once the exits all miss their atoms. Suggested first attack (an idea, no computation behind it): case on whether d's row
is the witness. Branch a: GoodTop fails at d iff u_N(d) ≠ d, and then a height-2 version of `breakExists` applies —

**BreakA (paper, Unverified).** Branch a (d = t_N ∈ M2), W0♭. If λ(d) ≠ d, let r be the last element ≥ d on row d's
descent and s = F(d,r) (so s ≱ d); let j be least with r ⊓ t_j = d and w = r ⊓ t_{j−1}. Then w > d, h(w) ≥ 3,
q := φ(w) is an atom below d, and q ≤ s. *Proof.* u_N(d) ≥ t_N = d and u_N(d) ≠ d (else λ(d) = d, the earlier u_j(d) ≥ t_j
being high), so r exists, r > d, and r ≠ d gives j ≥ 1, w ≥ d, w ≠ d. φ(w) ≤ φ(r) ⊓ φ(t_{j−1}) ≤ s ⊓ t_j ≤ r ⊓ t_j = d,
and s ⊓ t_j ≤ s ⊓ d < d. φ(w) = ⊥ would put w ∈ Z at height ≥ 3 (ZT). ∎

So in branch a a failed witness at d hands over an atom q < d carrying the cell q ≤ φ(w) at a high column w ≥ d; the
open question is how that cell is pushed to some m ∈ M2 (for instance one above q) until a row lands on itself. Branch
atom (d an atom): no analogue is offered here; run 2's `onlyD2_min9` (branch b) has its witness at an m ≠ λ(⊥) that lies
on its own descent.

**Probe (run 5, reserved lead run).** See §8. **Result: the lead holds on 78 of 78 lattices (H 4–12, |L| 9–66, width 3–19); the calibrated mutant
(OwnZCell, refuted in run 4) fails on 78 of 78, in branch a on 54 and branch atom on 24.** Status: `provisional` in height
and width (one encoding); silent in N (not controlled). Whole run 1475 s of the 1500 s cap; no lattice stopped.

## 7. Other programmes

### P2 — Exits are absorbed: every exit's μ-orbit ends at a fixed atom (ExitReach)
- **Candidate (conjectural).** In W0 ∧ n1, if x ∈ Z exits, the μ-orbit of c(x) reaches a μ-fixed atom. Weaker form
  ExitCycle: every μ-cycle containing an exit step has length 1.
- **Payoff (complete).** ExitZ ∧ ExitReach ⟹ CertAtom (take any exit; its orbit ends at a fixed atom). ExitReach also
  explains BotOrbit's refutation: in s281 the ⊥-orbit 0 → 2 → 5 → 2 never exits (bank replay `bank_cycles.py`).
- **Placement.** Not below CertAtom by itself (needs ExitZ, open, and ExitZ fails under the same relaxations as
  CertAtom, run 3). ExitReach is implied by "every exit atom is fixed or lands in Z and reaches a fixed atom".
- **Testability.** Finitely refutable in W0 (hypothesis "some row exits" has models wherever CertAtom holds).
- **Anatomy.** An exit into a non-exit μ-cycle of length ≥ 2. The only banked non-exit cycles are in s281 (|L| 59, H 12,
  width 11) and s276_atomorb (|L| 31, H 6, width 10, M2-cycle 8 ↔ 9): room needs H ≥ 12 or width ≥ 10.
- **Evidence.** Bank replay only: 21 of 21 non-certifying exits reach the fixed atom; every μ-cycle with an exit is a
  fixed point (30 of 30 W0 models). **Silent** (no search run; budget spent on the lead).
- **Mode.** Set-aside reversal (frontier §8, "the anchor"): the walk starts at an *exit*, not at ⊥. The recorded
  objection is that ⊥-anchored walks cycle (s281); that cycle never exits, so it does not refute ExitReach — but the
  general objection (walks cycle once height and width give room) still applies, which is why this is not the lead. Limit: a
  walk statement; it names the certificate as the orbit's end. **Decisive step:** ExitCycle (no exit on a 2-cycle).

### P3 — The real level-1 target: GoodAtom1 = CertAtom ∨ StallExit (normal form, A5)
- **Candidate.** Lemma N1 (paper above). In contradiction mode for GoodAtom1 one may assume every atom bad, a stronger
  hypothesis than NoFix: in addition no atom stalls (q ≮ a(q)).
- **Payoff (complete).** N1 is itself the payoff: any proof of "NoFix ∧ ¬StallExit ⟹ ⊥" gives BackGood1(1)'s open case.
- **Placement.** GoodAtom1 ⟸ CertAtom (strict on paper). With the lead: GoodZ (in W0♭) ⟹ GoodAtom1 directly.
- **Testability.** `nogood` = `nofix` on every relaxation column of run 2 (82 lattices): the weaker target uses the same
  hypotheses. Expect `normal form` for N1 and no leverage beyond it; formalize N1 because it is three existing lemmas.

### P4 — Counting (pigeonhole) over exit columns (short; bank only, silent)
- **Candidate.** NC1: an exit column p whose atom c = φ(p) lies below none of the rows landing at p is the landing of
  exactly one row of Z. Surplus: #exiting rows > #exit columns.
- **Payoff (complete).** NC1 ∧ Surplus ⟹ some exit column has two landing rows ⟹ (NC1) it is certifying ⟹ Cert1 ⟹
  CertAtom (`exitFixed_of_dom`). Bank: NC1 holds on 5 of 5 non-certifying columns (30 W0 models). No proof idea for
  either half; listed so the worker can test it cheaply in the second encoding. Limit: Surplus is as hard as existence.

## 8. Probe scripts (all in this directory; corpora via `tight_probe.lattices`; one-hot F as in `orbit_probe.py`)

Common encoding (`certrole.py`, written from the definitions): rows F(x,·) for x of height ≤ 2, one-hot, monotone in
both arguments along covers; a(⊥) = ⊥ (no y ≠ ⊥ with y ≤ F(⊥,y)); ZT; n1; exact descents for j ≤ h(⊤)+1; λ = first
element of height ≤ 2; d from the exact ⊥-descent; (T) at rows of Z per relaxation; every SAT model is decoded (rows of
high x = constant ⊤) and replayed in Python from the definitions (assertion). Every mode prints its quantifier and SAT
meaning; per-lattice progress is printed. Smoke runs (2 and 3 lattices) are in `smoke/`. `amalg/` and `separation/`
are unmodified copies of `experiments/amalgamation/*.py` (+ `bank/`) and `experiments/separation/*.py` at b2ab19e, so
the probes import `tight_probe`, `rstages`, `bank` without writing into the checkout; run each script with this
directory's subfolder (e.g. `run5/`) as cwd.

| run | script / command | encodes | output |
|---|---|---|---|
| 1 | `certrole.py nofix full,noTb2,noTb1,noTbD,noTb,desc1,desc12,noTa2,noTa1 closure 5 11 4 30 + closure 6 12 1 40 + tall 8 4 1 12` | SAT = in the relaxed world no atom of Z is μ-fixed | `run1/run1_nofix_roles.txt`, min models `run1/*.json` |
| 2 | `certrole2.py nofix,nogood full,noTb2,noTb1,noTbD,desc2,descD,onlyD2,onlyD1,onlyD,noTa2 (same corpus)` | + SAT = no atom has an own-row cell (GoodAtom1 fails) | `run2/run2_roles.txt`, `run2/*.json` |
| 3 | `certrole3.py noexit,exitnofix full,noTb2,desc2,noTb1,desc1,noTbD,descD,noTa2 (same corpus)` | SAT = no row of Z exits / some row exits and no atom is fixed | `run3/run3_split.txt`, `run3/*.json` |
| 4 | `lead_probe.py lead,mutA,mutB,vac noTb2 closure 5 11 4 3` | first lead candidate OwnZCell: SAT = NoFix ∧ ¬OwnZCell in W0♭ | `run4/lead_lead_noTb2_min12.json` (refutes OwnZCell; console output `run4/run4_console.txt`) |
| 5 | `lead2_probe.py lead,weak,mutZ noTb2 closure 5 11 4 30 + tall 8 4 1 12 + tall 10 4 2 20 + tall 12 4 1 8 + tall 10 6 1 8` | lead: SAT = NoFix ∧ no m ∈ M2 with λ(m) = m (W0♭); weak: SAT = NoFix ∧ no m with λ(m) ≤ m (solved only when lead is SAT; equal to lead by SelfLow); mutZ: SAT = NoFix ∧ ¬OwnZCell (calibrated mutant, the refuted relative) | `run5/run5_lead.txt` |

**Budget.** Five exact runs (1–5 above), each under `timeout 1500`, at most two in parallel (runs 2 and 3 overlapped;
run 5 overlapped the end of run 3), plus one 2-lattice set-up smoke of `certrole.py` (`smoke/`, 0 s). Wall times:
run 1 227 s, run 2 ≈ 730 s, run 3 ≈ 750 s, run 4 < 1 s, run 5 1475 s (all 78 lattices finished). Corpus coordinates
(no search): `corpus_widths.txt`; model coordinates: `coords_of_models.txt`.

Free replays (no search): `replay_all.py` (statistics of every banked model), `bank_cycles.py` (μ-cycles, exit
columns), `bank_noncert.py` (non-certifying exits and their orbits), `replay_lead.py` (lead and mutant on every banked
model and every stored model in W0♭), `inspect_model.py`, `inspect_relaxed.py`. Bank: CertAtom, GoodAtom1 and atmost1fix.py 30/30
(`bank_replay_out.txt`); the bank has no W0♭ ∧ NoFix model (its 30 W0 models all have a fixed atom; none of its 12 relaxed models
is a W0♭ ∧ NoFix model); over the 15 stored files of runs 1–4 that lie in W0♭ ∧ NoFix (8 distinct models) the lead holds on all
15 and OwnZCell fails on 7 (`replay_lead_out.txt`).

**Report lines**

```
GoodTop (lead) | closure 5 11 4 30 + tall 8 4 1 12 + tall 10 4 2 20 + tall 12 4 1 8 + tall 10 6 1 8 (exact, 78 lattices)
  | exists F in W0b (W0, Tb dropped at height-2 rows): SAT = NoFix and no m in M2 with lambda(m) = m (lead fails)
  room reached: H 4,5,8,10,12; width 3-9 / 4-8 / 5-12 / 6-11 / 8-19; |L| 9-66; N not controlled; constants none
  | anatomy needs: unknown; smallest W0b & NoFix model is |L| 9, H 4 -> one step above reached in H and width
  per corpus: closure5 30/30 UNSAT, tall8 12/12, tall10 20/20, tall12 8/8, tall10-M6 8/8
  branch a: hypothesis models >= 54 lattices (mutant models) | lead failures 0 | mutant (OwnZCell, run 4) failures 54
  branch atom: hypothesis models >= 24 lattices              | lead failures 0 | mutant failures 24
          -> provisional (H, width); silent in N; push owed (independent encoding, H 13-14, M 7, exact N)
LowLand / DescTb2 world (weak) | same run | SAT = NoFix and no m in M2 with lambda(m) <= m
  -> equal to the lead by SelfLow (solved only if lead SAT; lead never SAT) : 0/78 failures
OwnZCell (first lead candidate) | closure 5 11 4 3 (exact, run 4) | SAT = NoFix and not OwnZCell in W0b
  room: H 5, |L| 12-14 | anatomy: two atoms swapping at a Z-landing | failures 3/3 (a 2, atom 1)
          -> refuted (|L| 12, H 5, width 4, N 2, branch a; run4/lead_lead_noTb2_min12.json)
CertAtom under each single relaxation (role, runs 1-2) | closure5 + closure6 + tall8 (exact, 82 lattices, H 4-8)
  | SAT = CertAtom fails in the relaxed world | control W0: 0/82
  noTb2 82 | noTb1 82 | noTbD 82 | noTb 82 | desc1 79 | desc12 79 | descD 79 | onlyD2 82 | onlyD1 79 | onlyD 82 | noTa2 82 | noTa1 82
  desc2 0/82  -> design rules, suggestive (below room; no mutant needed: the W0 column is the control)
GoodAtom1 under the same relaxations (run 2) | same corpus | SAT = no atom has an own-row cell
  identical pattern to CertAtom column by column; desc2 0/82
ExitZ / ExitToFix (run 3) | same corpus | SAT = no row exits / an exit and no fixed atom
  noTb2 82/81 | noTb1 82/82 | desc1 79/79 | noTbD 82/82 | descD 79/79 | noTa2 82/81 | desc2 0/0 | W0 0/0
          -> the split collapses (no separation of hypotheses)
```

## 9. Pushes owed

- GoodTop is at most `provisional` (one encoding; this briefer's). Owed: an **independent encoding** (worker), then one
  step further in every dimension: H 13–14 (`tall 13 4 1 8`, `tall 14 4 2 20 maxn 45`), width M = 7 (`tall 10 7 1 5`),
  and **N**: the probe does not control N; add exact-N flags (E4–E6 as in `orbit_probe.py`) to the W0♭ encoding. Per
  branch: UNSAT lattices carry no branch; the hypothesis world's branches were measured only on the small corpus (run 1).
- desc2 (CertAtom in the DescTb2 world, = GoodTop by SelfLow): pushed only as far as run 5 reaches.
- P2, P4: silent (bank only); need exact runs at H ≥ 12 or width ≥ 10 for room.

## 10. Already failed — do not repeat

All of frontier §4 (⊥-anchored walks, extremal indices, comparison elements FixBelowD/LandBelowD, universal-over-family
statements, tightness-free descents, DescTb12, the Pous companion). New in this brief:
- **OwnZCell** (NoFix ⟹ some atom has an own cell at a height-2 element of Z, in W0♭): `refuted`, |L| 12, H 5, width 4
  (largest antichain {1,2,3,4}), branch a, N 2 (`run4/lead_lead_noTb2_min12.json`): atoms 3, 4 land at d = 7 and swap
  (F(3,7) = 4, F(4,7) = 3); the violation W0 forbids is row 7 landing on itself. So DescChain-at-level-1 into Z is not
  the only goodness producer.
- **ExitZ ∧ ExitToFix split**: `collapses` (both halves need every hypothesis class; run 3).
- **GoodAtom1 instead of CertAtom as the contradiction target**: no hypothesis leverage (run 2).
- AtMost1Fix / FixMax as a route to existence: vacuous on the target's counterexample world (A2).

## 11. Hard constraints

Sharpness: branch g for top-layer statements; dropping R_2 tightness. New: existence fails when any single class of (T)
is dropped (Ta at atoms, Ta at M2, Tb at atoms, Tb at M2, Tb at d's row), and when Tb at the atoms or at d's row is
weakened to descent form; it survives Tb at M2 weakened to descent form (0/82 failures in run 2; 0/78 in run 5, to H 12). Design rule: a proof
of CertAtom uses Tb at the height-2 rows only through `not_good_of_ahead`/`land_not_le`, and uses full Tb at the atom
rows (trap-type), including d's row.

## 12. Formalization order (no sorry, no new axioms)

1. A3 correction: `certAtom_fixMax_topExit` (CertAtom ∧ FixMax ⟹ TopExit, off g) from `certAt_of_fixed_below`.
2. Lemma N1 (GoodAtom1 ⟺ CertAtom ∨ StallExit) from `goodUp`, `goodCell_dichotomy`, `land_unique`, `le_a`, `a_le_rowDesc`.
3. SelfLow and GoodTopEq, stated with hypotheses ZT, Tb at atom rows, Ta at m (no R_2 tightness at m).
4. ZCellTop from `upTrap_land`.
5. The payoff: GoodTop (as a hypothesis on W0♭-shaped data) ⟹ CertAtom, via `not_good_of_ahead` (j = 1).
6. Then the open step, GoodnessTransfer.

## 13. Expected report

One verdict per programme in the §6 taxonomy: Lead (GoodTop): `provisional` → push owed / `refuted` (bank the model) /
`conditional lemma` (payoff, items 3–5 above, formalized) ; P2: `silent` → run or drop; P3: `normal form` (N1);
P4: `silent`. Each with its ladder update.

## 14. Frontier corrections

1. **§2 ladder, "OneFix ∧ FixMax ⟹ TopExit off g"**: AtMost1Fix is not used. Write *CertAtom ∧ FixMax ⟹ TopExit (off g)*
   [`certAt_of_fixed_below`] (A3).
2. **§2, AtMost1Fix and FixMax**: mark them as holding vacuously wherever CertAtom fails — corollary-side rungs, not
   sufficient conditions; no proof of either reduces the target (A2).
3. **§2, decisive open step "count-to-existence"**: stale. AtMost1Fix does not use Tb at the height-2 rows (§286);
   existence does (run 1: CertAtom fails on 82/82 without it). Replace with: existence itself, and if the lead is
   accepted, GoodnessTransfer (§6 of this brief) (A4).
4. **§2 / §3, missing normal form**: GoodAtom1 ⟺ CertAtom ∨ StallExit (Lemma N1, paper from `goodUp`,
   `goodCell_dichotomy`, `land_unique`, `le_a`, `a_le_rowDesc`). The frontier calls CertAtom "the open target"; it is a
   sufficient condition for the level-1 need GoodAtom1, strictly stronger on paper (A5).
5. **§1 branches**: "g (d a good atom; GoodAtom1 holds trivially there)" is right, but CertAtom is *not* trivial on g — by
   N1 a good d may be a StallExit atom that exits to another atom. Say so wherever CertAtom is read per branch.
6. **§2, "Cert1 ⟺ CertAtom [paper: exit_atom + exitFixed_of_dom + cert_of_exitFixed]"**: the direction Cert1 ⟹ CertAtom
   also needs `land_unique` (the height-2 descent element in Cert1 is the landing) before `exit_atom` applies.
7. **§7 hard constraints**: the role of the hypotheses in the *target itself* was missing (only TopExit's and
   AtMost1Fix's were on file). Add §4 of this brief: existence fails when any one of Ta(atoms), Ta(M2), Tb(atoms), Tb(M2),
   Tb(d's row) is dropped, and when Tb at the atoms or at d's row is weakened to descent form; it survives Tb at M2 in
   descent form (runs 1–3, 82 lattices, H 4–8; run 5: 78 lattices to H 12, width 19). "Every statement fails once R_2 tightness is dropped
   entirely" is much weaker than what holds.
8. **§2 / §3, DescTb2**: listed as provisional for TopExit only. Add: CertAtom and GoodAtom1 survive DescTb2 (run 2:
   0/82 failures; run 5: 0/78 to H 12), and by Lemma SelfLow DescTb2 is, given Tb at the atom rows, *equivalent* to
   "no element of M2 is good" — the conclusion of `not_good_of_ahead`. So DescTb2 is not a new hypothesis.
9. **§4 refuted routes**: add OwnZCell (in W0♭: NoFix ⟹ an atom has an own cell at a height-2 element of Z), refuted,
   |L| 12, H 5, width 4, N 2, branch a, `run4/lead_lead_noTb2_min12.json`. Bank it (world: relaxed, Tb dropped at
   height-2 rows). Add the ExitZ ∧ ExitToFix split as `collapses` (run 3).
10. **§8 set-aside choices**: record (i) the target choice CertAtom over GoodAtom1, with the reason now measured: the
    weaker target has the same hypothesis profile (run 2), so no reversal is indicated; (ii) the ExitZ/ExitToFix split
    (no separation of hypotheses).
11. **§9 vacuity map**: add that ¬CertAtom (NoFix) has no model in W0 on any corpus run, but has models on 82/82
    lattices (H 4–8) in each single-class relaxation of runs 1–2, and on 78/78 lattices of run 5's corpora in W0♭
    (mutant column: branch a on 54, atom on 24). Contradiction-mode statements about NoFix are testable there.
12. **§10 corpora/testers**: add this brief's `certrole*.py` / `lead2_probe.py` (one-hot rows, relaxation flags,
    per-lattice replay): 82 lattices × 20 (mode, relaxation) pairs in about 12 minutes; `lead2_probe.py` ran 78 lattices (H 4–12, |L| ≤ 66,
    width ≤ 19) × 3 modes in 1475 s.
