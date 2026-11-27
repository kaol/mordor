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
   - Add this as a normal form (paper) with its census: 1500 restrictions of stored W0 models all have a T-fixed atom.
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
