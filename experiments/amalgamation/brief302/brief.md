# Brief run 27: SelfLand makes D2′ a theorem (Lean); the located forms of D1 fail; lead PairLocal

**Repository:** /home/user/mordor at 5470ecb, read only. Nothing in the checkout was changed; no git command that
changes state was run, and nothing was built there.
**Work dir:** `/tmp/claude-0/-home-user/3b6fdd2c-c95c-5c07-b47c-6ae28c687a4c/scratchpad/amr_run27/brief/`
(`brief.md`, `SelfLand.lean`, `AxCheck_SelfLand.lean`, `lean_build.txt`, `lean_selfland_axioms.txt`, `probes/`,
`runs/`, `cex/`, and the Lean scratch copy `leanw/`).

**Mission.** Stop predicting where the escape sits. Every route in this round that said *where* the relaxed world
escapes (at a corner, at a crossing pair, at a closed colour, in Case B) was refuted, by an exact run or by a stored
model. The one thing that
held is a statement about a whole **set** of rows: SelfLand. The landing map is constant on the basin
`{y ≥ q : q ≤ λ(y)}` of an atom that lies below its own landing.

---

## 0. Result first (verdict asked: `proves` for D2′ and for S4)

New Lean file `SelfLand.lean`, which imports `Mordor.ThinColour`.
- It compiles in the scratch copy: `lake build Mordor.SelfLand` gives 1288 jobs, OK.
- There is no `sorry`. `#print axioms` reports propext, Classical.choice and Quot.sound for all seven declarations
  (`lean_selfland_axioms.txt`).

| name | statement (W0 = a(⊥) = ⊥, R_2 tight, h(⊤) > 2) |
|---|---|
| **`selfLand`** | Only ZT (`hne`: high elements are outside Z) and Tb at the atom q are assumed. Let p = (F q)^[i] ⊤ have height 2 with q ≤ p. Then every row y ≥ q that lands with q ≤ λ(y) lands at p. No NoFix, no ColourGain, no a(⊥) = ⊥ |
| **`selfPair`** (D2′, strong form) | In W0, if c ∈ Z is an atom and c ≤ λ(c) = m ∈ Z, then c ≰ λ(m) |
| **`certAtom_of_closed`** (S4 closed) | In W0, let c ∈ Z be an atom with c ≤ λ(c). Suppose c ≤ λ(λ(c)) if λ(c) ∈ Z, and c ≤ λ(F(⊥, λ(c))) if λ(c) ∉ Z. Then some atom is μ-fixed |
| `crossAtom` | The trap of `trap_of_tb`, run without its hypothesis q ≤ F(q, p). Suppose a descent element r = (F y)^[K] ⊤ is high and lies above p, but the next element does not. Then some high X has F(q, X) = F(⊥, X), an atom below p, different from q and below (F y)^[K+1] ⊤ |
| **`twoSelf`** | Let q₁ ≠ q₂ be atoms with Tb whose rows reach the same height-2 element p ≥ q₁, q₂, and suppose every atom value F(⊥, X) (X high) below p is q₁ or q₂. Then every landing row y ≥ q₁, q₂ lands at p |
| `twoSelf_absurd` | In W0, two such colours landing at the same m ∈ Z is impossible |
| `certAtom_of_caseB` | In W0, suppose every colour row exits and any two colour rows' landings share a colour. Then some atom is μ-fixed. This is the thin proof's Case B with SCL replaced by its conclusion, so it isolates what D1 must supply in Case B |

**Paper proof of SelfLand** (the Lean proof follows it line by line).
1. Let u_j = (F y)^[j] ⊤. We show p ≤ u_j for every j ≤ i(y), by induction on j.
2. Suppose p ≤ r = u_j and not p ≤ s = u_{j+1} = F(y, r).
   - r is high, because j < i(y).
   - F(q, r) ≤ s ≤ r, because q ≤ y.
   - q ≤ s, because q ≤ λ(y) ≤ s.
3. **Trap**, run from row q's index i up to ⊤. We claim r ⊓ (F q)^[i−t] ⊤ = p for every t ≤ i.
   - At t = 0 this is r ⊓ p = p.
   - Step: let X = r ⊓ (F q)^[i−t−1] ⊤. Then X ≥ p, and F(q, X) ≤ F(q, r) ⊓ (F q)^[i−t] ⊤ ≤ r ⊓ (F q)^[i−t] ⊤ = p.
   - If X is high:
     - F(q, X) ≥ F(⊥, X) ≠ ⊥ by ZT.
     - F(q, X) ≠ p, because F(q, X) ≤ F(q, r) ≤ s and s does not lie above p.
     - So F(q, X) is an atom t′ < p, and t′ ≠ q by Tb.
     - Now q ≤ s and t′ ≤ s, so p = q ⊔ t′ ≤ s, a contradiction.
   - Hence X is low and X ≥ p, so X = p.
4. At t = i the claim reads r = p. But r is high and p has height 2. This contradiction finishes the induction, so
   p ≤ λ(y), hence λ(y) = p.

**Consequences.**
- **D2′ holds outright.** Take c₀ universal over R* with λ(c₀) = m a pair-join. Then c₀ ≤ λ(m) because m ∈ R*, and
  `selfPair` gives a contradiction. Neither the other colour c′, nor NoFix, nor ColourGain is used.
- §301's partial case split on λ(c′) (two open cases) is therefore unnecessary.
- **S4 is closed.** Universal over colour rows and pair-join rows ⟹ CertAtom (`certAtom_of_closed`; λ(c₀) ∈ Z is a
  pair-join by ColourGain).
- **The universal-colour branch of PairSelf's skeleton is closed in Lean.**

**Check against the stored models** (free; `probes/selfland_replay.py`): 0 violations of SelfLand in 2,996 instances
over the 1,809 distinct stored models with ZT. Any F is allowed there, with Tb required only at q.

**`twoSelf`** proves half of the lead's candidate (§3). Its proof applies `crossAtom` twice:
- the cross atom of q₁ is q₂ and the cross atom of q₂ is q₁;
- both lie below the first descent element s that leaves ↑p;
- so p = q₁ ⊔ q₂ ≤ s.

---

## 1. Frontier used (checked at source, 5470ecb)

**Definitions.** φ = F(⊥, ·) and Z = φ⁻¹(⊥).
- A colour is an atom of Z that is a value of φ; 𝒜 is the set of colours.
- λ(x) is the first element of height ≤ 2 on row x's descent from ⊤, and r_x is the element just before it.
- K(y) := C(λ(y)), the colours below λ(y).
- A pair-join is an element of Z above two colours.
- R* is the set of colour rows together with the pair-join rows.
- μ-fixed atom: an atom q with λ(q) ∉ Z and φ(λ(q)) = q.
- **W** is PairSelf's world without D_p (the worker's `pairselfM`):
  - a(⊥) = ⊥, ZT, n1, h(⊤) ≥ 3;
  - colours unbounded in Z, and some pair-join;
  - colour rows land, with ColourGain and Tb;
  - pair-join rows land;
  - NoFix.
- **PairSelf**: W ∧ D_p (λ(m) ≰ m at the pair-join rows) has no model.

**Used, read at source.**
- ThinColour.lean: `land_capture`, `join_of_two_atoms`, `phi_low_colour`, `shadow_start` (its Z-branch calls
  `colourGain` at the row y), `colourStair` (hypothesis `hnb`), `thinStair`, `certAtom_of_thin` (Case A / Case B blocks).
- PairTrap.lean: `pairStair`, `certAtom_of_topRow'`, `colourGain` (any landing row x, in W0 ∧ NoFix).
- TwoColour.lean: `desc_ge_of_postfixed`.
- LateParent.lean section `Landing`: `land_not_le`, `land_bot_lt`, `exit_atom`, `land_unique`, `trap_of_tb`,
  `domCoLand`, `tb_of_tight`, `exitFixed_of_dom`, `upTrap_land`, `ta_iff_lands`.
- StairB1.lean: `exists_first_low`. Normalize.lean: `mem_one_iff`, `CertAtom`.
- Log §34.3z²⁹⁸–³⁰¹ (`docs/rounds/26-v3.7.md`, lines 19528–19751) and `experiments/amalgamation/brief300/brief.md` §3.

**Exact open target.** CertAtom in W0 with N ≥ 2, 𝒜 unbounded in Z, and some pair-join (non-thin). Since an element of Z
lies above two colours and the colours are unbounded, |𝒜| ≥ 3 follows.

---

## 2. Ladder audit

1. **D2′ is a theorem** (`selfPair`). It is also stronger than stated: it needs universality at row m only, and no c′.
   Ladder: `CertAtom ⟸ universal colour over R*` [P `certAtom_of_closed`, `selfPair`].
2. **"∃ closed atom" is the target in other words** (W0):
   - ⟸ is `certAtom_of_closed`;
   - ⟹: a μ-fixed q is closed, since q ≤ λ(q) ∉ Z, its exit colour is q, and q ≤ λ(q).
   - **Normal form:** CertAtom ⟺ ∃ atom c ∈ Z with c ≤ λ(c) and c below the landing of μ(c).
   - Any future candidate "some colour is closed" is a **restatement**. "Some colour is universal over R*" is a strict
     sufficient rung above it.
3. **D1 does not follow from D2′, and it has no local form.** Two located versions of D1 are refuted; both
   counterexamples are banked.
   - **BreakCornerSelf** (brief300's D1 test form: a break at corner A forces λ(A) ≤ A) is refuted by 11 stored
     W-models (free replay). The smallest is |L| 29, H 6, width 10, N 2 (`cex/breakCornerSelf_min.json`).
   - **BD** (a break at A forces λ(A) ≤ A, or λ(u) = A for a colour u ≤ A) is refuted by an exact calibration run on 2
     stored lattices (`cex/bd_min.json`, |L| 29, H 8, width 7, N 2).
   - In both BD models the corner A is a pair-join whose own landing is **another** self-landing pair-join: λ(6) = 10
     and λ(10) = 10, or λ(10) = 13 and λ(13) = 13.
   - So D1 needs D_p at a row other than the corner, a row that cannot be named in advance.
4. **D3 does not follow from D2′ alone.** Its Case A2 tree (§4, P3) closes on some leaves by
   capture / `selfPair` / `twoSelf`, and needs PairLocal (the lead) on another.
5. **Composition check (asked).**
   - **(a) PairSelf ⟹ CertAtom is correct.**
     - W0 ∧ NoFix ∧ non-thin ∧ unbounded ⊆ PairSelf's world, by `ta_iff_lands`, `colourGain`, `tb_of_tight` and
       `land_not_le`.
     - With `certAtom_of_thin` and `certAtom_of_boundedAtoms` this covers every branch.
   - **(b) The skeleton S1–S4 + D1–D3 does not prove PairSelf in its own world.**
     - SCL's start is `shadow_start`, which calls `colourGain` at the row y (ThinColour.lean, the `hpZ` branch).
     - PairSelf's world has no ColourGain at the pair-join rows.
     - So the skeleton proves the W0 statement (CertAtom), where `colourGain` holds at every landing row. That is all the
       target needs.
   - **(c) In W0, after SelfLand, the skeleton needs:**
     - Case A1 (e(a) a single colour c₀): SCL from a to c₀, to λ(c₀) (a pair-join row, if in Z) or to the exit colour
       s (if not), i.e. D1 at 2 pairs;
     - Case A2: D1 at every pair (a, y) and D3;
     - Case B: D1 at the colour–colour pairs, which `certAtom_of_caseB` (Lean) turns into CertAtom.
6. **PairSelf is not the target in other words.** Its world drops landing and Tb at the rows of Z outside R*, and
   ColourGain at the pair-join rows. Its push in |𝒜| (≥ 5) is still owed (brief300 §7; the frontier lists |𝒜| 3–4).

---

## 3. Lead programme P1: PairLocal

**Candidate lemma (conjectural, finitely refutable).** **PairLocal.** In W, let c₀ ≠ c′ be colours and m = c₀ ⊔ c′ ∈ Z a
pair-join with λ(c₀) = m and c₀ ≤ λ(c′). Then λ(m) = m.

Equivalently, in PairSelf's world or in W0 ∧ NoFix: if λ(c₀) = m ∋ c₀ is a pair-join, then no other colour c′ ≤ m has
c₀ ≤ λ(c′).

**Conditional payoff (proof).** PairLocal ∧ SelfLand ⟹ "a colour universal over the **colour rows** gives CertAtom" (W0).
- Let c₀ be such a colour, so c₀ ≤ λ(c₀) =: p.
- If p ∉ Z: the exit colour s is a colour row, so c₀ ≤ λ(s). Then `certAtom_of_closed` applies.
- If p ∈ Z: ColourGain at c₀ gives a colour c′ ≤ p other than c₀, so p = c₀ ⊔ c′ is a pair-join. Also c₀ ≤ λ(c′),
  because c′ is a colour row. PairLocal gives λ(p) = p, against `land_not_le`.

So with PairLocal:
- **R\* shrinks to the colour rows** in S3/S4 and in the D3 leaves, and SCL is needed only between colour rows.
- The `shadow_start` gap of §2.5(b) disappears, because colour rows have ColourGain in PairSelf's world. So
  "D1 between colour rows ∧ D3 over colour rows ∧ PairLocal ⟹ PairSelf" is then a statement in PairSelf's own world.
- It also closes the D3 leaf "u₁ ≤ λ(u₁) = m₀, u₁ ∈ K(u₂)" (§4, P3).

**Placement.**
- PairLocal ⟸ `twoSelf` in the half λ(c′) = m (Lean).
- PairLocal ⟸ `land_capture` in the half "λ(c′) ∉ Z with exit colour ≠ c₀" (paper, below).
- It is not implied by D2′: D2′ assumes c₀ ≤ λ(m), PairLocal assumes c₀ ≤ λ(c′).
- **Its generalization CrossPair (b ≤ λ(a), a ≤ λ(b) ⟹ λ(a ⊔ b) = a ⊔ b) is refuted** in W (`cex/cp_min.json`).
  So PairLocal's hypothesis λ(c₀) = m is essential.

**Testability.** Finitely refutable in W, which has models. The mutant has models on every corpus.
- **Hypothesis world:** W with a pair-join that is the landing of one of its own colours.
- PairLocal instances (λ(c₀) = m ∋ c₀ and c₀ ≤ λ(c′)) occur in 425 of the 428 stored W-models (free count), and
  λ(m) = m in all of them.

**Counterexample anatomy.** Two colours below one pair-join m = λ(c₀), with the descent of row m leaving ↑m before
landing (`crossAtom` then gives the cross atom c′ below the leaving element).
- Smallest coordinates: |𝒜| = 3, H 5 (the mutant's smallest model is |L| 15, H 5).
- A third atom of m that is a value of φ is a room dimension: the `twoSelf` half needs C(m) = {c₀, c′}.

**Mode.** Ladder audit (it isolates the only use of universality at row m) plus set level (basin constancy).

**Limit.** It does not touch D1. It only moves the universality that D1/SCL must deliver from R* to the colour rows.

**Paper proof, what is done and what is open.** Let n = λ(c′) ≥ c₀ and suppose λ(m) ≠ m.
- **(done) n = m and C(m) = {c₀, c′}:** `twoSelf_absurd`.
- **(done) n ∉ Z with exit colour s ≠ c₀:**
  - n = c₀ ⊔ s, and `land_capture` at c₀ makes every landing above c₀ equal to n.
  - But λ(c₀) = m ∈ Z ≠ n.
- **(facts for the open half, all from `crossAtom` / `domCoLand`)** Let K* = the last j with u_j(m) ≥ m, and
  s = u_{K*+1}(m).
  - u_{K*}(m) is high, s ∋ c′, and c₀ ≰ s.
  - Hence c₀ ≰ λ(m) and i(c′) ≤ K*.
  - Row m does not land at n: λ(m) = n would give c₀ ≤ λ(m), which was just excluded. In case (i), `domCoLand`
    (x = m, q = c₀, using φ(n) = c₀) also gives this.
  - With K′ = the last j with u_j(m) ≥ n, we have K′ ≤ K*, and u_{K′+1}(m) carries an atom t′ ≠ c′ of n:
    - t′ = c₀ if K′ < K*;
    - t′ is the other atom of n if K′ = K*.
- **Decisive open step**, two sub-cases:
  - (i) n ∉ Z with exit colour c₀, so n = c₀ ⊔ t with t ≠ c′ and c′ ≰ n;
  - (ii) n ∈ Z, n ≠ m. This includes n = c₀ (an atom landing), where the c′-trap above does not apply because its
    target must have height 2.
  - These are the two cases §301 left open, now with c₀ ≤ λ(m) **not** assumed. With that assumption they are closed
    by `selfPair`.
  - Candidate tools: `crossAtom` with q = c′ and target n on row m (as above), Tb at m (W0), and SelfLand at c₀ applied
    to row n (n ≥ c₀ in case (ii)).

**Probes (exact; `probes/plocal_probe.py`, the briefer's encoding; SAT = PairLocal fails; mutant `plocalM` = d2pM of
§301, "λ(c₀) = m a pair-join ⟹ λ(m) = m", the nearest refuted relative):** see §5, runs 1, 4 and 5. Lead 0 SAT on every
lattice reached; the mutant is SAT on most.

---

## 4. Other programmes

### P2: Case B via BD-B (named open case: every colour row exits)

**Candidate lemma (conjectural).** **BD-B.** In W, suppose every colour row exits. Then every break of a colourStair
staircase between two colour rows sits at a corner A with λ(A) ≤ A.

**Conditional payoff (proof; Lean for the last step).**
- In W0, or in PairSelf's world, a break corner is a pair-join, so D_p forbids λ(A) ≤ A.
- BD-B then gives no breaks between colour rows in Case B.
- So `colourStair` (with `shadow_start` at colour rows) gives: any two colour rows' landings share a colour. That is
  the hypothesis `hint` of **`certAtom_of_caseB`** (Lean), which yields CertAtom.
- **So BD-B closes Case B of the open target.**

**Placement.**
- BD-B is D1 restricted to Case B and colour pairs, in a form testable in W.
- The unrestricted form, BD, is **refuted** (exact, `cex/bd_min.json`): its counterexamples are Case A models.
- CaseBEmpty-in-W ("W has no Case B model") is **refuted** by run 3 (SAT on 5 corpora, H 8–14).
- So the Case B world W ∧ CaseB has models, and BD-B is not vacuous there.

**Evidence (samples only).** The 9 Case B models of W produced by run 3 contain 36 colour–colour breaks, and every
corner self-lands: λ(A) = A in 36 of 36 (`probes/bdB_replay.py`). In every one of them the pair-join corner is the
model's only self-landing pair-join.

**Testability.** Finitely refutable in W ∧ CaseB, which has models. Mode `bdB` of `probes/bd_probe.py` is written and
parses but was **not run**, because the budget was spent. **One exact run is owed.** Its mutant is `bdM1`
(BreakCornerSelf without Case B), which is refuted on stored lattices.

**Counterexample anatomy.** A Case B model with a colour–colour break at a pair-join corner that does not self-land.

**Mode.** Set-aside reversal, applied to D1: Case B was proved given SCL, so the open part of SCL is localized to
Case B.

**Limit.** It closes Case B only. Case A still needs D1 there (and D3).

**Decisive step.** Prove BD-B. In Case B every colour row exits, so `land_capture` controls every colour below any
colour landing. The break corner A = c ⊔ a has c carried in K(y) and a = φ(B).

### P3: D1 and D3 in Case A: what is closed, what is global

- **D1 is global** (§2.3). Every located form tested this round fails in W:
  - BreakCornerSelf;
  - BD;
  - and, as escape statements, EscapeLow, CrossExists, ClosedColour-in-W and CaseBEmpty-in-W (§7).
- The escape in W is always *some* self-landing pair-join, at a place no statement so far predicts. Treat any further
  "the break / escape is at X" as the failure signature.
- **D3 (Case A2):** λ(a) = e(a) = m₀ ∈ Z with C(m₀) ⊇ {u₁, u₂}. D1 gives K(y) ∩ C(m₀) ≠ ∅ for every landing y.
  Leaves:
  - **(closed, capture)** if some uᵢ ≤ λ(uᵢ) ∉ Z, then capture forces λ(a) = λ(uᵢ) ∉ Z, against λ(a) = m₀ ∈ Z.
    So every self colour of m₀ lands in Z.
  - **(closed, `selfPair` + `twoSelf`)** u₁ ≤ λ(u₁) = m₀:
    - u₁ ∉ K(m₀), so u₂ ∈ K(m₀) by D1 at row m₀.
    - If also u₂ ≤ λ(u₂), then λ(u₂) ∈ Z (capture leaf). SelfLand at u₂ with y = m₀ gives λ(m₀) = λ(u₂).
    - If λ(u₂) = m₀, that is λ(m₀) = m₀, which is impossible (also `twoSelf_absurd`).
    - If λ(u₂) = P₂ ≠ m₀, the leaf stays open (a chain of pair-joins).
  - **(closed by the lead)** u₁ ≤ λ(u₁) = m₀ and u₂ ≰ λ(u₂). Then u₁ ∈ K(u₂), and PairLocal gives λ(m₀) = m₀.
  - **(open)** λ(u₁) = P₁ ≠ m₀ (a chain of pair-joins P₁, λ(P₁), …), and the crossing leaf u₂ ∈ K(u₁),
    u₁ ∈ K(u₂) with neither colour self. The crossing leaf is exactly where CrossPair fails in W (`cex/cp_min.json`).
- **Mode.** Ladder audit. **Limit.** No new conjecture is proposed here; this is the map of what remains.

---

## 5. Probe scripts and report lines

**Testers** (the briefer's own encodings, written from the statements; run from a sub-directory of `runs/` with
`PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation:<work dir>/probes`):
- **`probes/plocal_probe.py`.** Base world W:
  - rows of height ≤ 2 are variables, and higher rows are the constant ⊤;
  - colours are encoded exactly.
  - Modes: plocal / plocalM / plne / esc / escM / cx / cp / cpM / caseB / caseAall.
  - Flags: E<k> (exact N), maxn, min<K> (at least K colours).
  - It prints the quantifier and the SAT meaning per mode, one line per lattice, and replays every SAT model from the
    definitions (assertion). Models are dumped to `plocal_<modes>_<corpus>.json`.
- **`probes/bd_probe.py`.** W plus a staircase-break encoding:
  - choice variables for x, y, l, κ(l), κ(l+1) and the six descent elements;
  - meets via the lattice's meet table;
  - "carried at l, not carried at l+1".
  - Modes: bd / bdM1 / bdM2 / bdB.
- **Free analyses** (stored models only, no search; library `probes/mlib.py`, `wlib.py`):
  - `selfland_replay.py`;
  - `d2local*.py`, `sub_nm.py`, `pl_raw.py`, `pl_roles.py`;
  - `w0_pairlocal.py` (0 PairLocal instances in the 361 stored W0 models);
  - `closed.py`, `swap.py`, `cross.py`, `breaks.py`, `break_w0*.py`, `bdB_replay.py`;
  - `bank_cex.py` and `bank_exact.py` (bank writers).

**Run budget.** Five corpus runs (`runs/run1.sh` … `run5.sh`), each under `timeout 1500`, at most 2 in parallel.
- Runs 1 and 3 were stopped early by the briefer:
  - run 1 because its candidate PairLocal had been re-run in runs 4–5;
  - run 3 because its statement was already refuted on 4 corpora.
- Run 4 hit the cap in its last corpus. Run 5's `min4` corpus stopped on a tester bug after 15 of 40 lattices.
- Disclosure: three calibration runs on 1–2 stored lattices each (`runs/smoke/`, under 1 minute CPU in total) also
  produced the CrossExists, CrossPair and BD refutations.

```
PairLocal (lead) | run 1 (partial) closure 6 12 1 40: lattices 1-9 of 40, exact | EXISTS F in W; SAT = PairLocal fails
  room: |L| 15-37, H 5-6 | anatomy: |A| 3, H 5
  base: 0/9 SAT (plne 0/9) | mutant plocalM (d2pM, refuted relative): 9/9 SAT -> consistent
PairLocal | run 4 (hit the 1500 s cap in its last corpus) | EXISTS F in W; SAT = PairLocal fails
  tall 8 4 1 12 (H 8): 0/12, mutant 9/12 | tall 12 4 1 8 maxn 45 (H 12): 0/5, mutant 2/5
  tall 10 7 1 5 maxn 50 (width M 7, H 10): 0/2, mutant 2/2 | tall 14 4 2 20 maxn 45 (H 14): 0/6, mutant 3/6
  tall 10 6 1 8 maxn 45 (M 6): 1 lattice before the cap, 0/1, mutant 1/1
PairLocal | run 5 | exact N: tall 10 4 2 20 maxn 40 E3: 0/17, mutant 6/17 (N 3); E4: 0/17, mutant 6/17 (N 4);
  tall 12 4 1 8 maxn 45 E5: 0/5, mutant 2/5 (N 5)
  >= 4 colours, closure 6 12 1 40: lattices 1-15, 0/15, mutant 14/15 (|A| 4-5); the corpus then stopped on a tester
  bug (CardEnc bound above the number of atoms on lattice 16; fixed in the script afterwards, not re-run)
  room reached: H 5-14, M 4-7, exact N 3-5, |A| 3-5 | anatomy: |A| 3, H 5, one pair-join
  -> provisional (evidence rule met where the mutant has models; one encoding; owed: second encoding, N >= 6,
     M 6-7 at H >= 12, |A| >= 5 beyond one model, a third phi-value atom of m)
EscapeLow (P-, refuted) | run 2: closure 6 12 1 40, tall 8 4 1 12, tall 10 4 2 20 maxn 40 | SAT = EscapeLow fails
  0/40, 3/12, 3/17 SAT | mutant ClosedColour-in-W: 35/40, 10/12, 7/17 -> refuted (cex/esc_min.json, |L| 29, H 8, N 2)
CaseBEmpty-in-W (refuted) | run 3 (stopped in tall 14) | SAT = W has a model with every colour row exiting
  closure 0/40; tall 8: 3/12; tall 10: 3/17; tall 12: 1/5; tall 13: 2/5; tall 14: >= 1 | mutant CaseAallEmpty: 40/40, 11/12,
  9/17, 2/5, 3/5 -> refuted (cex/caseB_min.json); hence BD-B (P2) is not vacuous
CrossExists, CrossPair (refuted) | calibration, 2 stored lattices, exact: SAT on the |L| 29 H 8 lattice
  (cex/cx_min.json, cex/cp_min.json); mutant OneCross SAT on both
BD (refuted) | calibration, 2 stored lattices, exact: bd SAT 2/2, bdM1 2/2, bdM2 2/2 (cex/bd_min.json)
```

---

## 6. Pushes owed

- **PairLocal:**
  - a second encoding (the worker's, e.g. `cgall_probe.py` with a mode built from `d2p` that replaces universality by
    c₀ ≤ λ(c′) for one colour c′ ≤ m);
  - width M 6 (run 4 reached 1 lattice) and M 7 at H ≥ 12;
  - exact N ≥ 6;
  - |𝒜| ≥ 5 (run 5 reached it on one model);
  - and **a third atom of m that is a value of φ** (the half not covered by `twoSelf`).
- **BD-B:** one exact run (`bd_probe.py bdB,bdM1`) on `tall 8 4 1 12`, `tall 10 4 2 20 maxn 40`, `tall 12 4 1 8`
  (Case B models exist there), then the room corpora.
- **PairSelf:** |𝒜| ≥ 5 (owed since brief300).
- **Lean:** none owed for `SelfLand.lean` (the worker re-compiles).

## 7. Already failed (do not repeat; all banked under `cex/` with statement, coordinates, F and lattice)

| statement | reason / counterexample |
|---|---|
| BreakCornerSelf (D1 test form, brief300) | 11 stored W-models; min \|L\| 29, H 6, width 10, N 2 (`breakCornerSelf_min.json`) |
| BD (break ⟹ λ(A) ≤ A or a colour lands at A) | exact, `bd_min.json` (\|L\| 29, H 8, width 7, N 2): corner's landing is another self-landing pair-join |
| ClosedColour-in-W (W ⟹ a colour c ≤ λ(c) = m ∈ Z with c ≤ λ(m)) | 3 stored W-models, escapes are swaps λ(a) = b, λ(b) = a (`closedColourW_0..2.json`, min \|L\| 22, H 5) |
| EscapeLow (W ⟹ a self-landing pair-join m with a colour c ≤ m, λ(c) ≤ m) | run 2, 3/12 and 3/17 (`esc_min.json`) |
| CrossExists (W ⟹ colours a, b with a ⊔ b ∈ Z, b ∈ K(a), a ∈ K(b)) | exact (`cx_min.json`) |
| CrossPair (b ∈ K(a), a ∈ K(b), a ⊔ b ∈ Z ⟹ self-landing) | exact (`cp_min.json`); also false with Tb only at a, b on 5 stored models |
| CaseBEmpty-in-W | run 3 (`caseB_min.json`) |
| §301's case split for D2′ | moot: `selfPair` |
| The located routes of the frontier §4; R3/P3; PC*; the §299 UNSAT worlds as rungs | as on file |

## 8. Hard constraints and design rules (as now understood)

- **SelfLand uses Tb at one atom and ZT only.** The trap of `trap_of_tb` does not need q ≤ F(q, p) once the row y keeps
  q below its landing.
- **Universality is needed at most at one pair-join row.** S4 needs c₀ ≤ λ(z) only for z = c₀ and z = λ(c₀) (or the
  exit colour).
- **In W every escape is a self-landing pair-join, but its position is not predictable.** It may be:
  - the corner of a break;
  - a closed colour's landing;
  - a swap's join;
  - the landing of a break corner;
  - or neither colour's landing (EscapeLow's counterexample).
- Sharpness (stored, samples): PairLocal fails once Tb at c₀ is dropped (97 stored failures) or Tb at c′ is dropped
  (25).
  CrossPair fails with Tb at a, b only, so Tb at a third colour is used.

## 9. Formalization order

1. Install `SelfLand.lean` (re-compile; standard axioms).
2. Ladder edits per §2: D2′ and S4 become `P`; add the normal form "CertAtom ⟺ ∃ closed atom" as a restatement marker.
3. PairLocal's case "λ(c′) ∉ Z with exit colour ≠ c₀" (a `land_capture` corollary, a few lines).
4. The payoff "universal over colour rows ∧ PairLocal ⟹ CertAtom" as a lemma with PairLocal as a hypothesis.
5. BD-B ⟹ `hint` (from `colourStair`), giving Case B outright once BD-B is proved.
6. No `sorry`, no new axioms.

## 10. Expected report

- §0 SelfLand: `proves` (D2′, S4).
- P1 PairLocal: `provisional`, or `new conjecture` once pushed, or `refuted` (banked); the case λ(c′) = m is
  `proves` (`twoSelf_absurd`).
- P2 BD-B: `provisional` after its owed run, or `refuted`; `certAtom_of_caseB` is `conditional lemma`.
- P3: `normal form` (closed-atom equivalence) and a map of D3's leaves.

## 11. Frontier corrections

1. **D2′ is a theorem** (`selfPair`, `selfLand`; in a stronger form: no c′, no NoFix, no ColourGain). Remove
   "provisional, one exact encoding" and §301's two open cases from §2 and §3.
2. **S4 is closed in Lean** (`certAtom_of_closed`). Add `CertAtom ⟸ universal colour over R*` [P].
3. **Normal form.** CertAtom ⟺ ∃ closed atom (W0). Mark future "some colour is closed" candidates as restatements.
4. **BreakCornerSelf is refuted** by 11 stored W-models. brief300's "14/14 breaks have λ(A) ≤ A" was a sample. Of all
   30 breaks in the stored W corpus, 11 have λ(A) ≰ A.
5. **Composition gap.** PairSelf ⟹ CertAtom is right. But "PairSelf ⟸ D1 ∧ D2′ ∧ D3" holds only in W0 form, because
   `shadow_start` needs ColourGain at the row y and PairSelf's world has none at the pair-join rows. With PairLocal,
   colour rows suffice and the gap closes.
6. **Relaxed-world census.**
   - The stored corpus has 428 distinct models satisfying the W predicate, not 235/238.
   - 421 have a colour universal over R* and 425 a closed colour.
   - 3 have neither; they escape through swap pairs.
   - All 428 are Case A at the colour rows (417 with every colour row landing in Z), so **the stored corpus has no Case B
     model**, while exact search finds them (run 3). The corpus is biased; "all 238 are in Case A" says nothing about
     Case B.
7. **Stale ladder lines from brief300's corrections 1–3 are still in the snapshot:**
   - "(superseded by the line above:) … TwoColourCG …";
   - "CertAtom(|𝒜| = 2) ⟸ ShadowLemma …";
   - "ShadowLemma ⟸ NoBreak …";
   - the "(history) OPEN (§298)" and "(history) |𝒜| = 2 status (§297)" blocks;
   - "OPEN CASE (§295)" still names "smallest open subcase |𝒜| = 2 (P4)", which is closed.
8. **Room vector** still lacks |𝒜|, the number of pair-joins, thin/non-thin (brief300 correction 7) and now the
   Case A/B split at the colour rows. In run 3, Case B models of W appear on the `tall` corpora at H 8–14 and not on
   `closure 6 12 1 40` (H ≤ 6).
9. **Corpora/testers.** §10 does not list `cgall_probe.py` (modes pairself/pairselfM/d2p/d2pM) nor `holding/cgall_*`,
   the main stored W corpus.
10. **"PairSelf: new conjecture, pushed (§300)"** overstates the |𝒜| dimension. The runs reach |𝒜| 3–4, and |𝒜| ≥ 5
    was listed as owed by brief300 §7. Mark it pushed in H, width and N, with |𝒜| owed.
11. **Failure signature, widened.** In the relaxed world W the escape is always some self-landing pair-join. Every
    statement this round that named which one was refuted:
    - by a corner (BreakCornerSelf, BD);
    - by a colour (ClosedColour-in-W);
    - by a pair (CrossExists, CrossPair, EscapeLow);
    - by a case (CaseBEmpty-in-W).

    This is the frontier's located-certificate signature, transported to the relaxation.
12. **Design rule §7 ("Tb at atom rows is used at three-row pair columns")** has a sharper form now. The pair column of
    `crossAtom` is the meet r ⊓ (F q)^[j] ⊤ of a high element of row y's descent with row q's descent, where row q
    takes its cross atom. That is exactly where Tb at q is used in `selfLand` and `twoSelf`.
