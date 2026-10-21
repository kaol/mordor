import Mordor.Plane

/-!
# The generalized collapse (log §34.3z⁵, item 7)

`β × K`, any complete lattices; `β` is the fibre that gets collapsed, `K` carries the layers. A monotone label
`lab : K → Λ` picks a floor set `A (lab k)` (growing with the label) and a ceiling set `B (lab k)` (shrinking with
the label). Lower a value to `(⌊z.1⌋_{A}, z.2)`, raise it to `(⌈z.1⌉_{B}, z.2)`, zones as in `Plane.zone_lo`, no
guides. If every stuck pair `z ≤ z'` (with `z.2 ≤ x.2` below and `y'.2 ≤ z'.2` above) has `z.1 ∈ A` or `z'.1 ∈ B`, the
result is monotone and witness-free on cells, keeps the second coordinates, and has first coordinates that are floors
in some `A` or ceilings in some `B`.

`Plane.collapse_lo`/`collapse_hi` and `Layers.cut_prod_layers` are instances (one label; `A` or `B` the corner sets).
On one layer this single move reproduces the whole plane theorem (`experiments/products/layered_collapse.py`).
-/

namespace Mordor.GenCollapse
open Finset Classical

variable {β K Λ : Type*} [CompleteLattice β] [CompleteLattice K] [Preorder Λ]

theorem gen_collapse {F : β × K → β × K → β × K} {D : Set (β × K)}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    (lab : K → Λ) (hlab : Monotone lab) (A B : Λ → Finset β)
    (hA : ∀ l l', l ≤ l' → A l ⊆ A l') (hB : ∀ l l', l ≤ l' → B l' ⊆ B l)
    (hpair : ∀ x y x' y', x ∈ D → y ∉ D → x' ∈ D → y' ∉ D → x ≤ x' → y ≤ y' →
      (F x y).2 ≤ x.2 → y'.2 ≤ (F x' y').2 →
      (F x y).1 ∈ A (lab (F x y).2) ∨ (F x' y').1 ∈ B (lab (F x' y').2)) :
    ∃ H : β × K → β × K → β × K,
      (∀ x x' y y', x ∈ D → x' ∈ D → y ∉ D → y' ∉ D → x ≤ x' → y ≤ y' → H x y ≤ H x' y') ∧
      (∀ x ∈ D, ∀ y, y ∉ D → ¬ H x y ≤ x ∧ ¬ y ≤ H x y) ∧
      (∀ x ∈ D, ∀ y, y ∉ D → (H x y).2 = (F x y).2 ∧
        ((H x y).1 = ((A (lab (F x y).2)).filter (· ≤ (F x y).1)).sup id ∨
         (H x y).1 = ((B (lab (F x y).2)).filter ((F x y).1 ≤ ·)).inf id)) := by
  let fl : β × K → β := fun z => ((A (lab z.2)).filter (· ≤ z.1)).sup id
  let cl : β × K → β := fun z => ((B (lab z.2)).filter (z.1 ≤ ·)).inf id
  let lo : β × K → β × K := fun z => (fl z, z.2)
  let hi : β × K → β × K := fun z => (cl z, z.2)
  have fl_le : ∀ z, fl z ≤ z.1 := fun z => Finset.sup_le fun f hf => (Finset.mem_filter.1 hf).2
  have le_cl : ∀ z, z.1 ≤ cl z := fun z => Finset.le_inf fun f hf => (Finset.mem_filter.1 hf).2
  have fl_self : ∀ z, z.1 ∈ A (lab z.2) → fl z = z.1 := fun z h =>
    le_antisymm (fl_le z) (Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨h, le_rfl⟩))
  have cl_self : ∀ z, z.1 ∈ B (lab z.2) → cl z = z.1 := fun z h =>
    le_antisymm (Finset.inf_le (f := id) (Finset.mem_filter.2 ⟨h, le_rfl⟩)) (le_cl z)
  obtain ⟨H, hHm, nwH, hval⟩ := Plane.zone_lo (D := D) hF nw (fun _ => False) lo hi
    (fun x z => lo z ≤ x) (fun y z => y ≤ hi z)
    (fun z => Prod.mk_le_mk.2 ⟨fl_le z, le_rfl⟩) (fun z => Prod.mk_le_mk.2 ⟨le_cl z, le_rfl⟩)
    (fun x y x' y' _ _ _ _ hxx hyy _ _ => by
      have h := Prod.le_def.1 (hF _ _ _ _ hxx hyy)
      have hl := hlab h.2
      refine ⟨Prod.mk_le_mk.2 ⟨Finset.sup_mono fun f hf => ?_, h.2⟩,
        Prod.mk_le_mk.2 ⟨Finset.inf_mono fun f hf => ?_, h.2⟩⟩
      · exact Finset.mem_filter.2 ⟨hA _ _ hl (Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 hf).2.trans h.1⟩
      · exact Finset.mem_filter.2 ⟨hB _ _ hl (Finset.mem_filter.1 hf).1, h.1.trans (Finset.mem_filter.1 hf).2⟩)
    (fun _ _ h _ => h.elim) (fun _ _ h _ => h.elim) (fun x z h => h) (fun y z h => h)
    (by
      intro x y x' y' hx hy hx' hy' hxx hyy _ hlo hhi
      rcases hpair x y x' y' hx hy hx' hy' hxx hyy (Prod.le_def.1 hlo).2 (Prod.le_def.1 hhi).2 with h | h
      · have e : lo (F x y) = F x y := Prod.ext (fl_self _ h) rfl
        exact (nw x hx y hy).1 (e ▸ hlo)
      · have e : hi (F x' y') = F x' y' := Prod.ext (cl_self _ h) rfl
        exact (nw x' hx' y' hy').2 (e ▸ hhi))
  refine ⟨H, hHm, nwH, fun x hx y hy => ?_⟩
  rcases hval x hx y hy with ⟨h, -⟩ | ⟨-, e | e⟩
  · exact h.elim
  · rw [e]; exact ⟨rfl, Or.inl rfl⟩
  · rw [e]; exact ⟨rfl, Or.inr rfl⟩

end Mordor.GenCollapse
