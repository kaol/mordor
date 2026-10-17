import Mordor.NoRoom

/-!
# The Cut Lemma at edge-height ≤ 3

Hypothesis `Height3`: in every chain `⊥ < x < y < ⊤`, `x` is an atom and `y` a coatom (no chain of five elements;
this covers `D_ω` and `M_ω × C₂` of the log's open frontier, §23.5, §31.5, and every finite lattice of
edge-height ≤ 3). Then the Cut Lemma holds for every monotone `F` and every down-set, hence semi-CL and CL.

Proof (by contradiction, `c = F ⊥ ⊤ ∉ {⊥, ⊤}`):
* `c ∉ D`: `c' = F ⊥ c` lies strictly between `⊥` and `c`, so `c'` is an atom and `c` a coatom; `c' ∉ D` is
  impossible (`F ⊥ c'` would lie strictly inside `(⊥, c')`), so `c' ∈ D`; then `e = F c' c` is a coatom `≠ c`, and
  `F c' ⊤ ≥ e ⊔ c = ⊤` is a witness.
* `c ∈ D`: `c'' = F c ⊤` lies strictly between `c` and `⊤`, so `c` is an atom and `c''` a coatom; `c'' ∈ D` is
  impossible (`F c'' ⊤` would be `⊤`), so `c'' ∉ D`; then `f = F c c''` is an atom `≠ c`, and
  `F ⊥ c'' ≤ f ⊓ c = ⊥` is a witness.
The log's universal cut theory `C₃` timed out in z3 (§31.5); this case analysis settles it.
-/

namespace Mordor
variable {α : Type*} [CompleteLattice α]

def Height3 (α : Type*) [CompleteLattice α] : Prop :=
  ∀ x y : α, ⊥ < x → x < y → y < ⊤ → IsAtom x ∧ IsCoatom y

theorem coatom_sup_eq_top {e c : α} (he : IsCoatom e) (hc : IsCoatom c) (hne : e ≠ c) : e ⊔ c = ⊤ := by
  apply hc.2
  refine lt_of_le_of_ne le_sup_right fun h => ?_
  have hec : e ≤ c := h ▸ le_sup_left
  exact hc.1 (he.2 _ (lt_of_le_of_ne hec hne))

theorem atom_inf_eq_bot {f c : α} (hf : IsAtom f) (hc : IsAtom c) (hne : f ≠ c) : f ⊓ c = ⊥ := by
  apply hc.2
  refine lt_of_le_of_ne inf_le_right fun h => ?_
  have hcf : c ≤ f := h ▸ inf_le_left
  exact hc.1 (hf.2 _ (lt_of_le_of_ne hcf hne.symm))

/-- **The Cut Lemma at edge-height ≤ 3.** -/
theorem cut_height3 (h3 : Height3 α) (G : α →o α →o α) : CutCells G := by
  intro D hD ⟨d, hd⟩ ⟨u, hu⟩
  have hbot : ⊥ ∈ D := hD bot_le hd
  have htop : ⊤ ∉ D := fun h => hu (hD le_top h)
  by_contra hno
  push_neg at hno
  -- hno : ∀ x ∈ D, ∀ y, y ∉ D → ¬ G x y ≤ x ∧ ¬ y ≤ G x y
  obtain ⟨hc0, hc1⟩ := hno ⊥ hbot ⊤ htop
  have hc0' : ⊥ < G ⊥ ⊤ := bot_lt_iff_ne_bot.mpr fun h => hc0 h.le
  have hc1' : G ⊥ ⊤ < ⊤ := lt_top_iff_ne_top.mpr fun h => hc1 h.ge
  set c := G ⊥ ⊤ with hc
  by_cases hcD : c ∈ D
  · -- c ∈ D: c'' = G c ⊤ is a coatom outside D, f = G c c'' an atom ≠ c
    obtain ⟨hA, hB⟩ := hno c hcD ⊤ htop
    have hge : c ≤ G c ⊤ := G.mono (bot_le : ⊥ ≤ c) ⊤
    have hlt1 : c < G c ⊤ := lt_of_le_of_ne hge fun h => hA h.symm.le
    have hlt2 : G c ⊤ < ⊤ := lt_top_iff_ne_top.mpr fun h => hB h.ge
    obtain ⟨hcat, hcco⟩ := h3 c (G c ⊤) hc0' hlt1 hlt2
    have hc''D : G c ⊤ ∉ D := by
      intro hin
      obtain ⟨hA', hB'⟩ := hno (G c ⊤) hin ⊤ htop
      have hge'' : G c ⊤ ≤ G (G c ⊤) ⊤ := G.mono hlt1.le ⊤
      rcases lt_or_eq_of_le hge'' with hlt | heq
      · exact hB' (hcco.2 _ hlt).ge
      · exact hA' heq.ge
    obtain ⟨hA'', hB''⟩ := hno c hcD (G c ⊤) hc''D
    have hfle : G c (G c ⊤) ≤ G c ⊤ := (G c).mono le_top
    have hflt : G c (G c ⊤) < G c ⊤ := lt_of_le_of_ne hfle fun h => hB'' h.ge
    have hf0 : ⊥ < G c (G c ⊤) := bot_lt_iff_ne_bot.mpr fun h => hA'' (h ▸ bot_le)
    obtain ⟨hfat, _⟩ := h3 _ _ hf0 hflt hlt2
    have hfne : G c (G c ⊤) ≠ c := fun h => hA'' h.le
    have hmeet : G ⊥ (G c ⊤) ≤ G c (G c ⊤) ⊓ c :=
      le_inf (G.mono (bot_le : ⊥ ≤ c) _) ((G ⊥).mono le_top)
    rw [atom_inf_eq_bot hfat hcat hfne] at hmeet
    exact (hno ⊥ hbot (G c ⊤) hc''D).1 hmeet
  · -- c ∉ D: c' = G ⊥ c is an atom inside D, e = G c' c a coatom ≠ c
    obtain ⟨hA, hB⟩ := hno ⊥ hbot c hcD
    have hle : G ⊥ c ≤ c := (G ⊥).mono le_top
    have hlt1 : G ⊥ c < c := lt_of_le_of_ne hle fun h => hB h.ge
    have hlt0 : ⊥ < G ⊥ c := bot_lt_iff_ne_bot.mpr fun h => hA h.le
    obtain ⟨hc'at, hcco⟩ := h3 (G ⊥ c) c hlt0 hlt1 hc1'
    have hc'D : G ⊥ c ∈ D := by
      by_contra hout
      obtain ⟨hA', hB'⟩ := hno ⊥ hbot (G ⊥ c) hout
      have hle' : G ⊥ (G ⊥ c) ≤ G ⊥ c := (G ⊥).mono hle
      rcases lt_or_eq_of_le hle' with hlt | heq
      · exact hA' (hc'at.2 _ hlt).le
      · exact hB' heq.ge
    obtain ⟨hA'', hB''⟩ := hno (G ⊥ c) hc'D c hcD
    have hege : G ⊥ c ≤ G (G ⊥ c) c := G.mono (bot_le : ⊥ ≤ G ⊥ c) c
    have helt : G ⊥ c < G (G ⊥ c) c := lt_of_le_of_ne hege fun h => hA'' h.symm.le
    have hetop : G (G ⊥ c) c < ⊤ := lt_top_iff_ne_top.mpr fun h => hB'' (h ▸ le_top)
    obtain ⟨_, heco⟩ := h3 _ _ hlt0 helt hetop
    have hene : G (G ⊥ c) c ≠ c := fun h => hB'' h.ge
    have hjoin : G (G ⊥ c) c ⊔ c ≤ G (G ⊥ c) ⊤ :=
      sup_le ((G _).mono le_top) (G.mono (bot_le : ⊥ ≤ G ⊥ c) ⊤)
    rw [coatom_sup_eq_top heco hcco hene] at hjoin
    exact (hno (G ⊥ c) hc'D ⊤ htop).2 hjoin

/-- **Semi-CL at edge-height ≤ 3**, infinite lattices included. -/
theorem semi_height3 (h3 : Height3 α) (G : α →o α →o α)
    (hsemi : ∀ x, b G (a G x) ≤ a G (b G x)) : m G = n G :=
  semi_of_cut (cutMaps_of_cells (cut_height3 h3 G)) hsemi

/-- **CL at edge-height ≤ 3.** -/
theorem cl_height3 (h3 : Height3 α) (G : α →o α →o α)
    (hc : ∀ x, a G (b G x) = b G (a G x)) : m G = n G :=
  semi_height3 h3 G fun x => (hc x).ge

end Mordor
