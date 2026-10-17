import Mordor.Derived

/-!
# The Retract Theorem, abstract form (log §23.1)

`ι : C → L`, `σ : L → C` monotone with `σ ∘ ι = id`, between complete lattices. For `F₀` on `C` let
`F x y = ι (F₀ (σ x) (σ y))`. Then `a_F = ι ∘ a₀ ∘ σ`, `b_F = ι ∘ b₀ ∘ σ`, `m_F = ι m₀`, `n_F = ι n₀`, and
commutation transfers. The log states this for a complete subchain `C ∋ ⊥, ⊤` of `L` with the least-above
retraction; neither the subchain, nor completeness of `C` inside `L`, nor `⊥, ⊤ ∈ C` is needed.
-/

namespace Mordor
variable {C L : Type*} [CompleteLattice C] [CompleteLattice L]
variable (ι : C →o L) (σ : L →o C) (F₀ : C →o C →o C)

/-- The transported bifunction `ι ∘ F₀ ∘ (σ × σ)`. -/
def transport : L →o L →o L where
  toFun x := ⟨fun y => ι (F₀ (σ x) (σ y)), fun _ _ h => ι.mono ((F₀ (σ x)).mono (σ.mono h))⟩
  monotone' _ _ h _ := ι.mono (F₀.mono (σ.mono h) _)

variable {ι σ F₀} (hσι : ∀ c, σ (ι c) = c)
include hσι

theorem transport_a (x : L) : a (transport ι σ F₀) x = ι (a F₀ (σ x)) := by
  apply le_antisymm
  · show ((transport ι σ F₀) x).gfp ≤ _
    apply OrderHom.gfp_le; intro c hc
    change c ≤ ι (F₀ (σ x) (σ c)) at hc
    have h1 : σ c ≤ F₀ (σ x) (σ c) := by have := σ.mono hc; rwa [hσι] at this
    have h2 : σ c ≤ a F₀ (σ x) := le_a h1
    exact hc.trans (ι.mono (((F₀ (σ x)).mono h2).trans (row_a _).le))
  · apply le_a
    show ι (a F₀ (σ x)) ≤ ι (F₀ (σ x) (σ (ι (a F₀ (σ x)))))
    rw [hσι, row_a]

theorem transport_b (y : L) : b (transport ι σ F₀) y = ι (b F₀ (σ y)) := by
  apply le_antisymm
  · apply b_le
    show ι (F₀ (σ (ι (b F₀ (σ y)))) (σ y)) ≤ ι (b F₀ (σ y))
    rw [hσι, col_b]
  · show _ ≤ (col (transport ι σ F₀) y).lfp
    apply OrderHom.le_lfp; intro c hc
    change ι (F₀ (σ c) (σ y)) ≤ c at hc
    have h1 : F₀ (σ c) (σ y) ≤ σ c := by have := σ.mono hc; rwa [hσι] at this
    have h2 : b F₀ (σ y) ≤ σ c := b_le h1
    calc ι (b F₀ (σ y)) = ι (F₀ (b F₀ (σ y)) (σ y)) := by rw [col_b]
      _ ≤ ι (F₀ (σ c) (σ y)) := ι.mono (F₀.mono h2 _)
      _ ≤ c := hc

theorem transport_m : m (transport ι σ F₀) = ι (m F₀) := by
  apply le_antisymm
  · apply OrderHom.lfp_le_fixed
    show a (transport ι σ F₀) (ι (m F₀)) = ι (m F₀)
    rw [transport_a hσι, hσι, a_m]
  · have hfix := a_m (F := transport ι σ F₀)
    rw [transport_a hσι] at hfix
    -- m_F = ι c with c = a₀ (σ m_F), and σ m_F = c, so c is a₀-fixed and m₀ ≤ c
    set c := a F₀ (σ (m (transport ι σ F₀)))
    have hc : σ (m (transport ι σ F₀)) = c := by rw [← hfix, hσι]
    have hca : a F₀ c = c := by
      calc a F₀ c = a F₀ (σ (m (transport ι σ F₀))) := by rw [hc]
        _ = c := rfl
    rw [← hfix]; exact ι.mono (m_le_common hca)

theorem transport_n : n (transport ι σ F₀) = ι (n F₀) := by
  apply le_antisymm
  · have hfix := b_n (F := transport ι σ F₀)
    rw [transport_b hσι] at hfix
    set c := b F₀ (σ (n (transport ι σ F₀)))
    have hc : σ (n (transport ι σ F₀)) = c := by rw [← hfix, hσι]
    have hcb : b F₀ c = c := by
      calc b F₀ c = b F₀ (σ (n (transport ι σ F₀))) := by rw [hc]
        _ = c := rfl
    rw [← hfix]; exact ι.mono (common_le_n hcb)
  · apply OrderHom.le_gfp
    show ι (n F₀) ≤ b (transport ι σ F₀) (ι (n F₀))
    rw [transport_b hσι, hσι, b_n]

/-- **Retract Theorem.** A CL failure on `C` transports to `L`. -/
theorem retract_fail (hc : ∀ x, a F₀ (b F₀ x) = b F₀ (a F₀ x)) (hne : m F₀ ≠ n F₀) :
    (∀ x, a (transport ι σ F₀) (b (transport ι σ F₀) x) = b (transport ι σ F₀) (a (transport ι σ F₀) x)) ∧
    m (transport ι σ F₀) ≠ n (transport ι σ F₀) := by
  refine ⟨fun x => ?_, fun h => hne ?_⟩
  · rw [transport_b hσι, transport_a hσι, hσι, transport_a hσι, transport_b hσι, hσι, hc]
  · rw [transport_m hσι, transport_n hσι] at h
    have := congrArg σ h; rwa [hσι, hσι] at this

end Mordor
