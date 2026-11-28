# Brief run 28: the k-colour twoSelf is a theorem (Lean); colour-row landings never form a triangle; PairLocal repaired by universality over C'(m)

**Repository:** /home/user/mordor at 9c1afac, read only. Nothing in the checkout was changed, no state-changing git
command was run, nothing was built there.
**Work dir:** `/tmp/claude-0/-home-user/3b6fdd2c-c95c-5c07-b47c-6ae28c687a4c/scratchpad/amr_run28/brief/`
(`brief.md`; `KSelf.lean`, `AxCheck_KSelf.lean`, `lean_build.txt`, `lean_kself_axioms.txt`; `probes/`; `runs/`
(`run1.sh`–`run5.sh`, `run*.out`, `r1`–`r5` with every SAT model as JSON, `smoke/`); `cex/`; the Lean scratch copy
`leanw/`).

**Mission.** Stop asking where the escape sits; ask what the whole family of colour-row landings looks like. The
statements that held this round are about a set taken together: every atom of C'(m) at once (kSelf, PairLocalS),
and every three colour-row landings at once (NoTriangle). The one-colour statement NSL was refuted, 13 models.

---

## 0. Results first

**Lean: `KSelf.lean`** (imports `Mordor.SelfLand`).
- It compiles in the scratch copy: `lake build Mordor.KSelf` gives 1289 jobs, OK.
- There is no `sorry`. `#print axioms` reports only propext, Classical.choice and Quot.sound for all six
  declarations (`lean_kself_axioms.txt`).

| name | statement |
|---|---|
| **`kSelf`** | Assume ZT (`hne`) and let p have height 2. Let y be a landing row. Let S be a nonempty set of atoms such that each q ∈ S has Tb, q ≤ y, and p on q's descent. Suppose S is **cross-closed**: every atom value φ(X) at a high column X with φ(X) ≤ p lies in S. Then λ(y) = p. `twoSelf` is the case S = {q₁, q₂} |
| **`kSelf_absurd`** (W0) | Let m ∈ Z have height 2. It is impossible that some atom q₀ ≤ m has m on its descent while every atom value φ(X) (X high) below m has m on its descent. In words: the colours of C'(m) cannot all land at m. This is twoSelf_absurd for any number of colours |
| `pairLocalS_of_nsl` (W0, conditional) | Suppose c₀ ≤ λ(c₀) = m ∈ Z, and c₀ lies below the landing of every t ∈ C'(m). Suppose also NSL at m: every such t ≠ c₀ with c₀ ≤ λ(t) has t ≤ λ(t). Then we have a contradiction (via `kSelf_absurd`) |
| **`certAtom_of_colourUniv`** (W0, conditional) | Assume PLS (hypothesis `hPLS`, W0 form). Then a colour below the landing of every **colour** row gives CertAtom. Before this, the hypothesis needed universality over R* (`certAtom_of_closed`) |
| `selfExit_not_exitColour` (W0) | Let an atom c ∈ Z satisfy c ≤ λ(c) = A ∉ Z with φ(A) ≠ c. Then c is the exit colour φ(λ(y)) of no landing row y |
| `exitColour_univ_of_meet` (W0) | Let a row x ∈ Z land at A ∉ Z, and let some atom lie below both A and the landing of a row y. Then φ(A) ≤ λ(y). Consequence: in Helly2/NoTriangle, the case where some colour row exits is closed |

**Proof of `kSelf`** (the Lean proof follows it):
1. Show by induction that p ≤ u_j(y) for every j up to the landing.
2. Suppose u_j(y) is high and above p, and u_{j+1}(y) is not above p.
3. `crossAtom` from q ∈ S gives an atom t₁ = φ(X₁) of p below u_{j+1}(y), and t₁ ∈ S by cross-closure.
4. `crossAtom` from t₁ gives an atom t₂ ≠ t₁ of p, also below u_{j+1}(y).
5. Two atoms of p join to p, so p ≤ u_{j+1}(y), a contradiction.

**Exact runs (5, the budget).** Every SAT model was replayed from the definitions, monotonicity included.

| statement (world W) | result | calibrated mutant |
|---|---|---|
| **PairLocalS**: c₀ ≤ λ(c₀) = m (a pair-join), c₀ ≤ λ(c) ∀ c ∈ C'(m) ⟹ λ(m) ≤ m | **0 SAT on 191 lattices** | PairLocal (refuted, bank s302): SAT on 85 of 191 |
| **NoTriangle**: no three colour rows whose landing colour sets pairwise meet with no common colour | **0 SAT on 55 lattices** | UnivCol-in-W (refuted on 81 stored W-models): SAT on 10/15 where co-run; Helly2 runs as below |
| **Helly2**: if the colour-row sets K(c) pairwise meet, they have a common colour | **0 SAT on 104 lattices** | UnivCol-in-W: SAT on 75 of 104 |
| NSL: one non-self colour t ∈ C'(m) with c₀ ≤ λ(t) forces λ(m) ≤ m | **REFUTED**: 13 saved models + 5 unsaved (run 2, capped) | — |

Room reached:

| dimension | reached |
|---|---|
| \|C(m)\| | 3, 4, 5 (new `planted` corpora) |
| height | 6–12 |
| width (largest antichain) | 4–18 |
| exact N | 3, 4, 5 |
| \|𝒜\| | 4–6 |

---

## 1. Frontier used (checked at source, 9c1afac)

**Definitions.**
- φ = F(⊥, ·) and Z = φ⁻¹(⊥).
- A **colour** is an atom of Z that is a value of φ; 𝒜 is the set of colours.
- C(z) is the set of colours below z. **C'(z)** is the set of atoms φ(X) ≤ z with X high (in Z these are colours). This
  is the set that `twoSelf`'s `hcol` and `crossAtom` speak about.
- λ(x) is the first element of height ≤ 2 on row x's descent u_j(x) = (F x)^[j] ⊤, and K(x) := C(λ(x)).
- A **pair-join** is an element of Z of height 2 above two colours.
- A colour c is **self** if c ≤ λ(c).
- **W** is PairSelf's world without D_p (= `cgall_probe.py pairselfM` = brief302 `world_pairselfM`):
  - a(⊥) = ⊥, ZT, n1, h(⊤) ≥ 3;
  - colours unbounded in Z, and some pair-join;
  - colour rows land, with ColourGain and Tb;
  - pair-join rows land;
  - NoFix.

  All other rows are free. D_p is λ(m) ≰ m at the pair-join rows. PairSelf says W ∧ D_p has no model.

**Read at source and used.**
- SelfLand.lean: `selfLand`, `selfPair`, `certAtom_of_closed`, `crossAtom` (no hypothesis q ≤ p), `twoSelf`,
  `twoSelf_absurd`, `certAtom_of_caseB` (hypothesis `hint`).
- ThinColour.lean: `land_capture`, `join_of_two_atoms`, `shadow_start` (its Z-branch calls `colourGain` at row y),
  `colourStair` (hypothesis `hnb` = D1), `certAtom_of_thin`.
- PairTrap.lean: `colourGain`. It holds at **any** landing row x, not only x ∈ Z.
- LateParent.lean `Landing`: `land_not_le`, `land_bot_lt`, `exit_atom`, `tb_of_tight`, `ta_iff_lands`,
  `land_index_pos`, `exitFixed_of_dom`. StairB1.lean: `exists_first_low`. Normalize.lean: `mem_one_iff`.
- Log §34.3z³⁰⁰–³⁰² (lines 19626–19830); brief302/brief.md in full; brief300/brief.md §3.

**Open target.** CertAtom in W0 on the non-thin branch: N ≥ 2, colours unbounded in Z, some pair-join.

---

## 2. Ladder audit

1. **The k-colour twoSelf is `kSelf`, and the right hypothesis is about C'(m), not about |C(m)|.**
   - `twoSelf`'s `hcol` already quantifies over φ-values at high columns.
   - In the PairLocal counterexample `bank/s302_pairlocal_h5` (m = 12): C(12) = {1, 2, 3} but C'(12) = {1, 3}.
     The refuting instances are (c₀, c₁) = (1, 2) and (2, 1). In both, what breaks the twoSelf argument is the atom
     3 ∈ C'(12), which does not land at 12 (λ(3) = 10).
     For (1, 2) the third atom c₁ = 2 is not even in C'(12).
   - So PairLocal₂ ("exactly two colours below m") restricts the wrong set. The case kSelf closes is "every atom of
     C'(m) lands at m", and it is now `kSelf_absurd` [P].
   - The frontier's open item "a k-colour twoSelf" is closed.
2. **Universality: R\* shrinks to the colour rows, conditionally on PLS.**
   - `certAtom_of_colourUniv` [P, hypothesis `hPLS`]. With `certAtom_of_closed` this places PLS: a colour universal
     over the colour rows gives CertAtom.
   - PLS is implied by NSL [P `pairLocalS_of_nsl`]. But NSL's located W-form is refuted (§5), so this implication is
     not the route.
3. **Composition (new skeleton; every arrow is Lean except the two marked paper):**
   ```
   hint  := any two colour rows' landings share a colour
   hint  ⟸ D1 at colour-row staircases          [P colourStair + shadow_start, ThinColour.lean]
   Case B (every colour row exits): hint ⟹ CertAtom          [P certAtom_of_caseB]
   Case A: hint ∧ Helly2 ⟹ some colour universal over the colour rows   [paper, definition]
           Helly2 ⟸ NoTriangle                               [paper, §3 below; 5 lines]
           universal over colour rows ∧ PLS ⟹ CertAtom       [P certAtom_of_colourUniv]
   ⟹  CertAtom ⟸ hint ∧ NoTriangle ∧ PLS      (non-thin branch, W0)
   ```
   - The only D1-type step left is `hint`, which is pairwise and has no corner location.
   - D3 (brief300's "transversal of size 2 inside a pair-join") is replaced by NoTriangle.
4. **NoTriangle and Helly2 are not the target in other words.**
   - They hold in W, a world without D_p, which has NoFix models. So they are direct statements about W, not
     contradiction-mode lemmas, and their proofs cannot use D_p.
   - Neither implies CertAtom on its own: hint fails in 81 of the 602 stored W-models.
5. **PLS is not a restatement.** It holds (exactly) in W, where the target's world has models. Its conclusion is
   located at m, which is the failure-signature risk (§7). Its W0 use is in contradiction mode.
6. **The relaxation rule for NSL.**
   - NSL's W0 form (contradiction mode) is the hypothesis of `pairLocalS_of_nsl`.
   - Its relaxation W refutes it: 13 saved models, all with λ(t) = c₀ (an atom landing) and λ(m) a self-landing
     pair-join.
   - So a proof of NSL in W0 would have to use something W lacks: Tb or ColourGain at the pair-join rows, or rows
     outside R\*. NSL should not be proposed as a step.
7. **`selfExit_not_exitColour`** [P] adds to the Case B structure. Exit colours are never self-exit colours, so in
   Case B the exit-colour map sends 𝒜 into the non-self colours and has no fixed point. No rung follows from this alone.

---

## 3. Lead programme P1: NoTriangle (colour-row Helly)

**Candidate lemma (conjectural, finitely refutable).** **NoTriangle.** In W, and hence in W0 ∧ NoFix, there are no
colours c₁, c₂, c₃ such that K(c₁), K(c₂), K(c₃) pairwise intersect while K(c₁) ∩ K(c₂) ∩ K(c₃) = ∅.

**Corollary (Helly2, paper).** If the sets K(c), over all colour rows c, pairwise intersect, they have a common colour.
- If two distinct height-2 elements both lay above two distinct atoms, both would equal the join of those atoms. So
  distinct landings share at most one colour.
- If all colour rows have the same landing, done.
- Otherwise take two distinct landings with K(a) ∩ K(b) = {x}.
- If x lies in every K, done.
- Otherwise some K(c) ∌ x. It meets K(a) and K(b) by pairwise intersection, and the three sets have no common colour
  (any common colour lies in K(a) ∩ K(b) = {x}). That is a triangle.

**Conditional payoff (proof).**
- In W0 ∧ NoFix, hint and NoTriangle give a colour c₀ universal over the colour rows (Helly2).
- If λ(c₀) ∉ Z: `certAtom_of_closed` (its hXc branch needs c₀ ≤ λ(s) only for the colour row s).
- If λ(c₀) ∈ Z: `certAtom_of_colourUniv` with PLS.
- In Case B, hint alone suffices (`certAtom_of_caseB`).
- So **CertAtom ⟸ hint ∧ NoTriangle ∧ PLS**, and hint ⟸ D1 at colour-row staircases.

**Placement.**
- NoTriangle ⟹ Helly2 [paper].
- hint ∧ Helly2 ⟹ "∃ colour universal over the colour rows". In the stored W-models, a universal colour exists in
  exactly the 521 of 602 models where hint holds (samples).
- Not implied by anything on file. It is not implied by CertAtom: in W0 it is vacuous, and in W it has content.

**Testability:** finitely refutable in W, which has models. Hypothesis world: W with three colour rows whose
landings pairwise meet. The stored W corpus has 752 pairwise-meeting colour-row triples and 0 triangles (samples).

**Counterexample anatomy.**
- Two cases are already closed:
  - If one of the three landings is an atom g, then K = {g} and g is common.
  - If one exits at A, then φ(A) is common (`exitColour_univ_of_meet` [P]).
- So a triangle needs three **distinct pair-joins in Z**, p₁ ⊇ {x, y}, p₂ ⊇ {x, z}, p₃ ⊇ {y, z}, with x, y, z distinct
  colours, landed on by three colour rows.
- Smallest coordinates: |𝒜| ≥ 3 and three height-2 elements of Z on an atom triangle. Such a triangle occurs in 33/40
  `closure 6 12 1 40` lattices, 11/15 `planted 6 6 21 15 5`, 7/12 `tall 8 4 1 12` and 8/15 `planted 8 4 2 15 3`.
- So the lattices have room. Whether F can realize the configuration is exactly the statement.

**Mode.** Signature inversion: a set shown to have a common point (Helly), in place of a named certifying colour.

**Limit.**
- NoTriangle does not supply hint; hint is still D1 at colour pairs.
- It does not remove PLS.

**Decisive open step: TriZ.** Exclude three colour rows landing at three distinct pair-joins p₁ = x ⊔ y,
p₂ = x ⊔ z, p₃ = y ⊔ z (W, or W0).
- Tools: `selfLand` (when cᵢ ≤ pᵢ, the basin {y ≥ cᵢ : cᵢ ∈ K(y)} lands at pᵢ), `crossAtom` at the rows of pᵢ,
  which dominate the rows x, y, z, and `kSelf`.
- The W-runs say even the colours x, y, z need not be the three rows. Start with the sub-case where c₁, c₂, c₃ are
  self (cᵢ ≤ pᵢ).

---

## 4. Programme P2: PairLocalS (PLS), the repaired PairLocal

**Candidate lemma (conjectural, finitely refutable).** **PLS.** In W, let c₀ be a colour with λ(c₀) = m a pair-join,
c₀ ≤ m. Suppose c₀ ≤ λ(c) for every c ∈ C'(m). Then λ(m) ≤ m.
- W0 form: no such c₀ exists (W0 has D_p by `land_not_le`).
- PLU, the same with "every colour c ≤ m", is weaker and was run beside it: also 0 SAT.

**Conditional payoff.** `certAtom_of_colourUniv` [P]: PLS ⟹ (a colour universal over the colour rows ⟹ CertAtom).
This is the payoff brief302 wanted from PairLocal.

**Placement.**
- Its hypothesis is stronger than PairLocal's, which needed c₀ ≤ λ(c₁) for one c₁. So PLS is weaker than the
  refuted PairLocal.
- The sub-case "every c ∈ C'(m) is self" is `kSelf_absurd` [P]: universality plus c ≤ λ(c) gives λ(c) = c₀ ⊔ c = m.
- PLS ⟸ NSL [P], but NSL is refuted in W.

**Paper facts for the open half** (W0 ∧ NoFix, PLS hypothesis, λ(m) ≠ m):
- Let j be the step where row m leaves ↑m.
- `crossAtom` from c₀, and from every self colour of m, gives the same t₁. It is the unique atom of m below
  u_{j+1}(m) and lies below φ(u_j(m)), and t₁ is non-self: c₀ ≤ λ(t₁) and t₁ ≰ λ(t₁).
- Domination of row t₁ by row m gives i(t₁) ≤ j. Otherwise u_{j+1}(m) ≥ u_{j+1}(t₁) ≥ λ(t₁) ≥ c₀, and then
  m ≤ u_{j+1}(m).
- λ(t₁) ∉ Z with exit colour ≠ c₀ is impossible: `land_capture` would make λ(c₀) = λ(t₁).
- Open leaf (the anatomy of all 13 NSL models): **λ(t₁) = c₀, an atom landing**, or λ(t₁) = c₀ ⊔ t′ with t′ ∉ m.
- Universality over the rest of C'(m) is necessary at this leaf: in every NSL model it fails at some other atom of
  C'(m).

**Anatomy and room.**
- A counterexample needs |C'(m)| ≥ 2 with a non-self atom of C'(m), so |C(m)| ≥ 3 is the dimension the earlier runs
  lacked.
- The standard corpora have no room there:
  - `tall 8/10/12/14 …`, `tall 10 6 1 8`: 0 lattices with three atoms under one height-2 element;
  - `closure 6 12 1 40`: 2/40;
  - `closure 5 11 4 30`: 1/30;
  - stored W corpus: 3 of 602 models with |C(m)| ≥ 3.
- New corpus **`planted H M SEED CNT k`** (`probes/my_lat.py`): every lattice has a height-2 element above exactly k
  atoms, and height exactly H (construction and assertion in the file).

**Status:** provisional, one encoding. It meets the evidence rule on every corpus listed in §6. **Mode:** ladder
audit plus set level. **Limit:** a located conclusion (the escape at m), so it carries the signature risk.

**Decisive open step: the atom leaf.** The case λ(t₁) = c₀, with universality of c₀ over C'(m) \ {t₁}, at the
leaving step of row m.

---

## 5. Programme P3: one colour is not enough (NSL refuted; sharp boundary for PLS)

- **NSL** (refuted). In W, let c₀ ≤ λ(c₀) = m be a pair-join, and let t ∈ C'(m) \ {c₀} satisfy c₀ ≤ λ(t) and
  t ≰ λ(t). NSL claims λ(m) ≤ m.
  - Counterexamples: 7/30, 1/15, 0/10, 2/6 in run 1; 2/20 (k4), 0/40, 1/12 (k4) and 5/11 (k4, capped, unsaved) in
    run 2.
  - Minimal model: `cex/nsl_min.json`, with |L| 19, H 6, width 5, N 2, branch a, |𝒜| 4, |C(m)| = |C'(m)| = 3. In it
    c₀ = 5, m = 11, t = 3, λ(3) = 5, λ(11) = 6, and the escape is λ(6) = 6. PLS's hypothesis fails at colour 2, since
    λ(2) = 6 ∌ 5.
  - All 13 saved models are in `cex/nsl_all.json`.
- **Sharpness.** Between PairLocal/NSL (one other colour; refuted) and PLS (all of C'(m); 0/191), the line is
  universality over the whole set C'(m).
  - In all 13 NSL models the escape is λ(m) itself: λ(λ(m)) = λ(m) (samples).
  - Do not turn this into a located conjecture. It is the signature.
- **`kSelf` placement:** proved, the general form of the self case.

---

## 6. Probe scripts and report lines

**Tester.** `probes/plu_probe.py` (the briefer's encoding, extending brief302's `plocal_probe.py` base world W).
- Rows of height ≤ 2 are one-hot variables, monotone in both arguments; higher rows are ⊤.
- cp(c) ⟺ c = φ(X) for a high X (exact).
- Modes: `plu`, `pls`, `ns`, `nsC`, `pl` (mutant), `kself` (theorem check), `helly`, `hellyM` (mutant), `tri`.
  Flags: `k<d>` (the instance pair-join has ≥ d colours), `kp3`, `E<k>` (exact N), `maxn`.
- The header prints the quantifier (EXISTS F per lattice) and the SAT meaning; one line per lattice; every SAT model
  is replayed from the definitions (monotonicity included) and dumped.
- Corpora: `probes/my_lat.py` (tight_probe corpora plus `planted`).
- Free analyses on stored models: `load_corpus.py` (2013 distinct stored models), `census.py` (602 W-models),
  `kself_replay.py`, `plu_replay.py`, `univ_census.py`, `helly_census.py`, `tri_census.py`, `nsl_anatomy.py`,
  `summarize.py`, `helly_room.py`, `show.py`.
- Run from a sub-directory of `runs/` with
  `PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation`.

**Bank replay (free).**
- kSelf: 0 violations in 2634 instances over 1983 stored ZT models. Theorem check; no instance had |C'(p)| ≥ 3.
- PLU / PLS: 0/780 W-instances violate λ(m) = m; PairLocal fails on 4 instances (the bank model and its relative).
- NSL: 0/274 stored instances (the stored corpus has no room; exact search refutes it).
- Helly2: 0/521; NoTriangle: 0 triangles in 752 triples.
- Calibration on stored lattices (`runs/smoke`, under 1 min CPU): on the lattice of `s302_pairlocal_h5`, `pl` SAT,
  `plu` UNSAT, `kself` UNSAT; on two planted H 6 lattices, `pl` SAT 1/2.

**Budget.** Five runs, each under `timeout 1500`, at most 2 in parallel.
- Run 2 hit the cap in its last corpus (11 of 12 lattices; its dump is lost and the counts come from `run2.out`).
- Run 4 hit the cap at the start of its width-M-8 corpus (0 lattices; the H 14 corpus was not reached).
- Run 5 was started, stopped after about a minute to add the `tri` room check, and restarted. Nothing from the first
  start is reported. It hit the cap at the start of `tall 10 7 1 5` (0 lattices; `tall 14` not reached).

```
PLS / PLU (P2) | runs 1,2,4,5, exact | EXISTS F in W; SAT = PLS (PLU) fails; mutant pl = PairLocal (refuted, bank s302)
  planted 6 5 1 30 3 k3  (H6, w4-9,  |C(m)|>=3): pls 0/30 plu 0/30 | mutant 17/30 | ns 7/30
  planted 8 4 2 15 3 k3  (H8, w4-8):              pls 0/15 plu 0/15 | mutant 8/15  | ns 1/15
  planted 10 4 3 10 3 k3 (H10, w5-10):            pls 0/10 plu 0/10 | mutant 6/10  | ns 0/10
  planted 12 4 4 6 3 k3  (H12, w5-10):            pls 0/6  plu 0/6  | mutant 5/6   | ns 2/6
  planted 6 5 4 20 4 k4  (|C(m)|>=4, w4-11):      pls 0/20 plu 0/20 | mutant 12/20 | ns 2/20
  closure 6 12 1 40 k3   (H4-6, w5-12):           pls 0/40 plu 0/40 | mutant 2/40  | ns 0/40
  planted 8 4 5 12 4 k4:                          pls 0/12 plu 0/12 | mutant 4/12  | ns 1/12
  planted 7 8 6 12 5 k4  (w7-18; 11/12, capped):  pls 0/11 plu 0/11 | mutant 11/11 | ns 5/11
  planted 6 6 21 15 5 k5 (|C(m)|>=5):             pls 0/15 plu 0/15 | mutant 5/15
  planted 8 4 22 12 3 k3 E3 (exact N 3):          pls 0/12 plu 0/12 | mutant 6/12
  planted 8 4 23 12 3 k3 E4 (exact N 4):          pls 0/12 plu 0/12 | mutant 4/12
  planted 10 4 31 8 3 k3 E5 (exact N 5, H10):     pls 0/8           | mutant 5/8
  room reached: H 4-12, width 4-18, exact N 3/4/5, |C(m)| 3/4/5, |A| 4-6 (mutant models), branches a and atom
  anatomy needs: |C(m)| >= 3 with a non-self atom of C'(m), H >= 5
  -> provisional (evidence rule met on every corpus above; one encoding)
NSL (P3) | runs 1,2 | SAT = NSL fails -> REFUTED (13 saved models, cex/nsl_all.json; min |L| 19 H 6 w 5 N 2)
Helly2 (P1 corollary) | runs 3,5 | EXISTS F in W; SAT = colour-row K's pairwise meet and have no common colour
  closure 6 12 1 40 (H4-6, w5-12): 0/40 | mutant hellyM (UnivCol-in-W, refuted on 81 stored W) 35/40
  tall 8 4 1 12 (H8, w4-8): 0/12 | 10/12      planted 8 4 2 15 3 (H8): 0/15 | 11/15
  tall 10 4 2 20 maxn 40 (H10, w5-9): 0/17 | 7/17      tall 12 4 1 8 maxn 45 (H12, w6-9): 0/5 | 2/5
  planted 6 6 21 15 5 (|C(m)| room 5, w6-10): 0/15 | 10/15
  room: H 4-12, width 4-12, |A| 3-5 in mutant models, up to 4 distinct colour-row landings in Z, N 2-4
  -> provisional
NoTriangle (P1, lead) | run 5 | EXISTS F in W; SAT = some three colour rows form a triangle
  planted 6 6 21 15 5: 0/15 (helly mutant hellyM 10/15 on the same lattices)   closure 6 12 1 40: 0/40
  lattice room for the anatomy (an atom triangle of height-2 joins): 11/15 and 33/40 lattices
  -> provisional (narrow: H <= 6 only; the push to H 8-14 and width is owed)
kSelf check (mode kself) | smoke only; theorem (Lean); not evidence
```

---

## 7. Pushes owed

- **NoTriangle (lead):**
  - a second, independent encoding;
  - heights 8, 10, 12, 13–14 (`tall 8 4 1 12`, `tall 10 4 2 20 maxn 40`, `tall 12 4 1 8 maxn 45`, `tall 13 4 1 8`,
    `tall 14 4 2 20 maxn 45`);
  - width M 6–7 (`tall 10 6 1 8`, `tall 10 7 1 5`; both are slow, more than 25 min a corpus);
  - exact N 3–5;
  - |𝒜| ≥ 5.
  - Also "NoTriangle over R\*" (with pair-join rows added to the family). If it holds, it removes PLS from the payoff
    via `certAtom_of_closed`.
- **Helly2:** width M 6–7, H 13–14, a second encoding.
- **PLS:** a second encoding (the worker's `cgall_probe.py`, from `plocal` with universality over C'(m)); H 13–14
  (`planted 14 4 25 4 3 k3`); exact N ≥ 6; width at H ≥ 10 (`planted 10 8 24 6 3 k3` did not finish one lattice
  in 15 min).
- **PairSelf:** |𝒜| ≥ 5 is still owed (brief300 §7, brief302 correction 10).
- **Lean:** none owed for `KSelf.lean`; the worker re-compiles.

## 8. Already failed (do not repeat)

| statement | reason |
|---|---|
| NSL (one non-self colour of C'(m) forces the escape at m) | 13 saved models, `cex/nsl_all.json`; all have λ(t) = c₀ |
| PairLocal | bank `s302_pairlocal_h5`; re-found by the mutant here on 85 of 191 lattices |
| "W ⟹ a colour universal over the colour rows" (UnivCol-in-W) | 81 stored W-models; mutant SAT on every Helly corpus |
| BreakCornerSelf, BD, EscapeLow, CrossExists, CrossPair, CaseBEmpty-in-W, ClosedColour-in-W | brief302 `cex/` |
| every located route of the frontier §4 | as on file |

## 9. Hard constraints and design rules

- **Room in |C(m)| needs a dedicated corpus.** No `tall` lattice on file has three atoms under one height-2 element.
  Any pair-join-local statement tested only on `tall` corpora is silent in |C(m)|.
- **The k-colour self argument needs cross-closure over C'(m)** (atom values at high columns), not a count of C(m).
  `crossAtom`'s atom is always a high-column value.
- **Set, not member.** Statements over all of C'(m) (PLS) or over all triples of colour rows (NoTriangle) hold. The
  same statements for one chosen colour (PairLocal, NSL) fail.
- **Exits are harmless for Helly.** One exiting landing that meets the others makes its exit colour common
  (`exitColour_univ_of_meet`).

## 10. Formalization order

1. Install `KSelf.lean` (re-compile; standard axioms).
2. Helly2 ⟸ NoTriangle as a Lean lemma over the colour-row landings. It is pure combinatorics using
   `join_of_two_atoms`, plus `exitColour_univ_of_meet` for the exit case.
3. The composition `certAtom_of_hint_noTriangle_pls`: hint, NoTriangle and PLS as hypotheses, via
   `certAtom_of_caseB` (Case B) and `certAtom_of_colourUniv` (Case A).
4. TriZ sub-case "c₁, c₂, c₃ self", if a proof is found.
5. No `sorry`, no new axioms.

## 11. Expected report

| programme | expected verdict |
|---|---|
| §0 `kSelf`, `kSelf_absurd` | `proves` (the k-colour twoSelf) |
| §0 `certAtom_of_colourUniv`, `pairLocalS_of_nsl` | `conditional lemma` |
| §0 `exitColour_univ_of_meet`, `selfExit_not_exitColour` | `proves` (lemmas) |
| P1 NoTriangle / Helly2 | `provisional`, then `new conjecture` once pushed, or `refuted` (banked) |
| P1 payoff chain | `normal form`: CertAtom ⟸ hint ∧ NoTriangle ∧ PLS |
| P2 PLS | `provisional`, or `refuted` |
| P3 NSL | `refuted` (banked); kSelf as above |

## 12. Frontier corrections

1. **"Open: a k-colour twoSelf"** is closed: `kSelf`, `kSelf_absurd` [P] (KSelf.lean, this brief).
2. **PairLocal₂'s restriction "exactly two colours below m" is the wrong set.**
   - `twoSelf_absurd` and `crossAtom` speak about C'(m), the atom values at high columns.
   - In `s302_pairlocal_h5`, C'(12) = {1, 3} ≠ C(12) = {1, 2, 3}. What defeats twoSelf there is 3 ∈ C'(12) with
     λ(3) ≠ 12, not the count of colours below m.
   - Replace PairLocal₂ by PLS (universality over C'(m)) or drop it.
   - The frontier's reading "three colours below m" as the cause should read "an atom of C'(m) that does not land at m".
3. **Room vector:** add |C(m)| and |C'(m)| (colours / high-column φ-atoms below one pair-join).
   - Largest values reached: 5 in this brief; the stored W corpus reaches 3 in 3/602 models.
   - `tall` corpora reach 2 at most. On `closure 6 12 1 40` only 2/40 lattices have room 3; on `closure 5 11 4 30`,
     1/30.
   - Also add "distinct colour-row landings in Z" (the anatomy of a triangle).
4. **Corpora section:** add `planted H M SEED CNT k` (`brief run 28 probes/my_lat.py`) and the tester `plu_probe.py`
   (modes `pls`/`plu`/`ns`/`pl`/`helly`/`hellyM`/`tri`/`kself`).
   - §10 also still omits `cgall_probe.py` modes `d2p`/`d2pM`/`plocal` with flag `two`.
5. **Stale ladder lines** (brief302 correction 7, not applied):
   - "(superseded by the line above:) … TwoColourCG …";
   - "CertAtom(|𝒜| = 2) ⟸ ShadowLemma …";
   - "ShadowLemma ⟸ NoBreak …";
   - the "(history) D2′ (§301)", "(history) OPEN (§298)" and "(history) |𝒜| = 2 status (§297)" blocks;
   - "OPEN CASE (§295) … smallest open subcase |𝒜| = 2 (P4)" (closed).

   A snapshot file should carry none of them.
6. **"PairSelf: new conjecture, pushed (§300)"** still overstates |𝒜|: it reaches 3–4 and |𝒜| ≥ 5 is owed (brief302
   correction 10, not applied).
7. **"PairLocal₂ provisional (0/40 on closure 6 12 1 40 where the mutant has 2/40)"**: the evidence corpus has room
   |C(m)| ≥ 3 on only 2 of its 40 lattices. Mark it silent outside those 2.
8. **Definitions §1** should define 𝒜, C(z), C'(z), K(y) and "self colour". 𝒜 is defined only inside the §295
   history text.
9. **Ladder additions:**
   - `kSelf` [P];
   - CertAtom ⟸ universal colour over colour rows ∧ PLS [P conditional];
   - Helly2 ⟸ NoTriangle [paper];
   - CertAtom ⟸ hint ∧ NoTriangle ∧ PLS [paper composition of Lean lemmas];
   - hint ⟸ D1 at colour-row staircases [P colourStair + shadow_start].

   D3 is superseded by NoTriangle (TriZ).
10. **Failure signature, widened.** Within a pair-join, single-member forms (one other colour, PairLocal; one non-self
    colour, NSL) fail, while the whole-set forms hold. Add NSL to the refuted routes with `cex/nsl_min.json` (bank it).
11. **Unverified from the worker's last round:** the PairLocal refutation was banked with "|C(m)| = 3" as its
    coordinate. The coordinate that matters is |C'(m)| = 2 together with a C'(m)-atom not landing at m. Re-record it
    in INDEX.md.
