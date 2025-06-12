import Deontic.Basic
import Deontic.Finset
import Deontic.Venn
import Deontic.Canonical

/-!

Here we go beyond A and B graded possible worlds to consider an
arbitrary preorder on worlds.

-/

open Classical Finset
noncomputable def theob (U : Type*) [Preorder U] [Fintype U] : Finset U → Finset (Finset U) := by
  intro Y
  exact {X | X ∩ Y ≠ ∅ ∧ ∀ a ∈ Y, ∀ b ∈ Y, a ∈ X ∧ a ≤ b → b ∈ X}

theorem theob5a  (U : Type*) [Preorder U] [Fintype U] : A5 (theob U) := by
  intro X
  unfold theob
  simp

theorem theob5b  (U : Type*) [Preorder U] [Fintype U] : B5 (theob U) := by
  unfold theob
  intro X Y Z h₀ h
  simp at h ⊢
  constructor
  · aesop
  · intro a ha b hb h₁ h₂
    have : b ∈ Y := by
      apply h.2 a ha b hb
      have : a ∈ Z ∩ X := mem_inter_of_mem h₁ ha
      rw [← h₀] at this
      simp at this
      exact this.1
      exact h₂
    have : b ∈ Y ∩ X := by exact mem_inter_of_mem this hb
    rw [h₀] at this
    simp at this
    exact this.1

theorem theob5c  (U : Type*) [Preorder U] [Fintype U] : C5 (theob U) := by
  unfold theob
  intro X Y Z h₀ h₁ h₂
  simp at *
  constructor
  · contrapose! h₂
    rw [← h₂]
    ext;simp;tauto
  · intro a ha b hb hY hZ hab
    constructor
    · exact h₀.2 a ha b hb hY hab
    · exact h₁.2 a ha b hb hZ hab

theorem theob5e  (U : Type*) [Preorder U] [Fintype U] : E5 (theob U) := by
  unfold theob
  intro X Y Z h₀ h₁ h₂
  simp at *
  constructor
  · contrapose! h₂
    rw [← h₂]
    ext;simp;tauto
  · intro a ha b hb hZ hab
    have haX : a ∈ X := h₀ ha
    apply h₁.2 a haX b (h₀ hb) hZ hab

theorem theob5g  (U : Type*) [Preorder U] [Fintype U] : G5 (theob U) := by
  unfold theob
  intro X Y Z h₀ h₁ h₂
  simp at *
  constructor
  · contrapose! h₂
    rw [← h₂]
    ext;simp;tauto
  · intro a ha b hb hY hZ hab
    have : b ∈ Y := h₀.2 a ha b hb hY hab
    constructor
    · exact this
    · exact h₁.2 a hY b this hZ hab
