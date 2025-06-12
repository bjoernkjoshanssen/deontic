
import Deontic.Basic
import Deontic.Finset
import Deontic.Venn
import Deontic.Canonical
import Deontic.LeastModels

/-!
  We explore the extent to which models of Carmo and Jones axioms form lattices.
  Closure under ∩ is quite trivial for all A5-G5.
  For ∪ we get failure for C5 and F5 and G5.

  Once we know there is a maximal model we can deduce "lattice" from
  "finite semilattice". However, {A5, ..., G5} has no maximal model.
-/
theorem A5_inter {n : ℕ} (ob₀ ob₁ : Finset (Fin n) → Finset (Finset (Fin n))) (a5: A5 ob₀ ∧ A5 ob₁) :
    A5 (fun X => ob₀ X ∩ ob₁ X) := by
  intro X hc
  simp at hc
  exact a5.1 _ hc.1

theorem B5_inter {n : ℕ} (ob₀ ob₁ : Finset (Fin n) → Finset (Finset (Fin n))) (a5: B5 ob₀ ∧ B5 ob₁) :
    B5 (fun X => ob₀ X ∩ ob₁ X) := by
  intro X Y Z h₀ h₁
  rw [Finset.mem_inter] at h₁ ⊢
  exact ⟨a5.1 X Y Z h₀ h₁.1, a5.2 X Y Z h₀ h₁.2⟩

theorem C5_inter {n : ℕ} (ob₀ ob₁ : Finset (Fin n) → Finset (Finset (Fin n)))
    (c5: C5 ob₀ ∧ C5 ob₁) :
  C5 (fun X => ob₀ X ∩ ob₁ X) := by
  intro X Y Z h₀ h₁ h₂
  rw [Finset.mem_inter] at h₀ h₁ ⊢
  exact ⟨c5.1 X Y Z h₀.1 h₁.1 h₂, c5.2 X Y Z h₀.2 h₁.2 h₂⟩

theorem D5_inter {n : ℕ} (ob₀ ob₁ : Finset (Fin n) → Finset (Finset (Fin n)))
    (d5: D5 ob₀ ∧ D5 ob₁) :
  D5 (fun X => ob₀ X ∩ ob₁ X) := by
  intro X Y Z h₀ h₁ h₂
  rw [Finset.mem_inter] at h₁ ⊢
  exact ⟨d5.1 X Y Z h₀ h₁.1 h₂, d5.2 X Y Z h₀ h₁.2 h₂⟩

theorem E5_inter {n : ℕ} (ob₀ ob₁ : Finset (Fin n) → Finset (Finset (Fin n)))
    (e5: E5 ob₀ ∧ E5 ob₁) :
  E5 (fun X => ob₀ X ∩ ob₁ X) := by
  intro X Y Z h₀ h₁ h₂
  rw [Finset.mem_inter] at h₁ ⊢
  exact ⟨e5.1 X Y Z h₀ h₁.1 h₂, e5.2 X Y Z h₀ h₁.2 h₂⟩

theorem F5_inter {n : ℕ} (ob₀ ob₁ : Finset (Fin n) → Finset (Finset (Fin n)))
    (f5: F5 ob₀ ∧ F5 ob₁) :
  F5 (fun X => ob₀ X ∩ ob₁ X) := by
  intro X Y Z h₀ h₁
  rw [Finset.mem_inter] at h₀ h₁ ⊢
  exact ⟨f5.1 X Y Z h₀.1 h₁.1, f5.2 X Y Z h₀.2 h₁.2⟩

theorem G5_inter {n : ℕ} (ob₀ ob₁ : Finset (Fin n) → Finset (Finset (Fin n)))
    (g5: G5 ob₀ ∧ G5 ob₁) :
  G5 (fun X => ob₀ X ∩ ob₁ X) := by
  intro X Y Z h₀ h₁ h₂
  rw [Finset.mem_inter] at h₀ h₁ ⊢
  exact ⟨g5.1 X Y Z h₀.1 h₁.1 h₂, g5.2 X Y Z h₀.2 h₁.2 h₂⟩

-- And union:

theorem A5_union {n : ℕ} (ob₀ ob₁ : Finset (Fin n) → Finset (Finset (Fin n))) (a5: A5 ob₀ ∧ A5 ob₁) :
    A5 (fun X => ob₀ X ∪ ob₁ X) := by
  intro X hc
  simp at hc
  cases hc with
  | inl h =>
    apply a5.1 _ h
  | inr h =>
    apply a5.2 _ h

theorem B5_union {n : ℕ} (ob₀ ob₁ : Finset (Fin n) → Finset (Finset (Fin n)))
  (b5: B5 ob₀ ∧ B5 ob₁) :
    B5 (fun X => ob₀ X ∪ ob₁ X) := by
  intro X Y Z h₀ h₁
  rw [Finset.mem_union] at h₁ ⊢
  cases h₁ with
  | inl h =>
    left
    exact b5.1 X Y Z h₀ h
  | inr h =>
    right
    exact b5.2 X Y Z h₀ h

theorem not_C5_union : ∃ ob₀ ob₁ : Finset (Fin 3) → Finset (Finset (Fin 3)),
    C5 ob₀ ∧ C5 ob₁ ∧ ¬ C5 (fun X => ob₀ X ∪ ob₁ X) := by
  use fun X => {{0,1}}, fun X => {{1,2}}
  simp
  constructor
  · intro X Y Z h₀ h₁ h₂
    simp at *
    subst h₀ h₁
    simp
  · constructor
    · intro X Y Z h₀ h₁ h₂
      simp at *
      subst h₀ h₁
      simp
    · unfold C5
      push_neg
      simp
      use {1}
      decide

theorem D5_union {n : ℕ} (ob₀ ob₁ : Finset (Fin n) → Finset (Finset (Fin n)))
  (d5: D5 ob₀ ∧ D5 ob₁) :
    D5 (fun X => ob₀ X ∪ ob₁ X) := by
  intro X Y Z h₀ h₁
  rw [Finset.mem_union] at h₁ ⊢
  cases h₁ with
  | inl h =>
    intro h₂
    left
    exact d5.1 X Y Z h₀ h h₂
  | inr h =>
    intro h₂
    right
    exact d5.2 X Y Z h₀ h h₂

theorem E5_union {n : ℕ} (ob₀ ob₁ : Finset (Fin n) → Finset (Finset (Fin n)))
  (e5: E5 ob₀ ∧ E5 ob₁) :
    E5 (fun X => ob₀ X ∪ ob₁ X) := by
  intro X Y Z h₀ h₁
  rw [Finset.mem_union] at h₁ ⊢
  cases h₁ with
  | inl h =>
    intro h₂
    left
    exact e5.1 X Y Z h₀ h h₂
  | inr h =>
    intro h₂
    right
    exact e5.2 X Y Z h₀ h h₂

theorem not_F5_union : ∃ ob₀ ob₁ : Finset (Fin 2) → Finset (Finset (Fin 2)),
    F5 ob₀ ∧ F5 ob₁ ∧ ¬ F5 (fun X => ob₀ X ∪ ob₁ X) := by
  use fun X => ite (X = {0}) {{0}} ∅
  use fun X => ite (X = {1}) {{0}} ∅
  constructor
  · intro X Y Z
    simp
    split_ifs with g₀ g₁ g₂
    · simp
    · subst g₀ g₁
      simp at g₂
    · intro _ h
      simp at h
    · intro _ h
      simp at h
    · intro h
      simp at h
    · intro h
      simp at h
    · intro h
      simp at h
    · intro h
      simp at h
  · constructor
    · intro X Y Z
      simp
      split_ifs with g₀ g₁ g₂
      · simp
      · subst g₀ g₁
        simp at g₂
      · intro _ h
        simp at h
      · intro _ h
        simp at h
      · intro h
        simp at h
      · intro h
        simp at h
      · intro h
        simp at h
      · intro h
        simp at h
    · unfold F5
      push_neg
      use {0}, {0}, {1}
      simp

theorem not_G5_union : ∃ ob₀ ob₁ : Finset (Fin 2) → Finset (Finset (Fin 2)),
    G5 ob₀ ∧ G5 ob₁ ∧ ¬ G5 (fun X => ob₀ X ∪ ob₁ X) := by
  have hh₁ : {1} ≠ ({0,1} : Finset (Fin 2)) := by
    intro hc
    have h₀ : 0 ∈ ({1} : Finset (Fin 2)) := by
      rw [hc]
      simp
    simp at h₀
  use fun X => ite (X = {1}) {{0,1}} ∅
  use fun X => ite (X = {0,1}) {{1}} ∅
  constructor
  · intro X Y Z
    simp
    split_ifs with g₀ g₁ g₂
    · intro h₀ h₁ h₂
      simp at *
      subst g₀ g₁ h₁
      simp
      exact h₀
    · intro _ h
      simp at h
    · intro h
      simp at h
    · intro h
      simp at h
  constructor
  · intro X Y Z
    simp
    split_ifs with g₀ g₁ g₂
    · intro h₀ h₁ h₂
      simp at *
      subst g₀ g₁ h₁
      simp
    · intro _ h
      simp at h
    · intro h
      simp at h
    · intro h
      simp at h
  unfold G5
  push_neg
  use {1}, {0,1}, {1}
  simp
  constructor
  exact hh₁
  intro hc
  rw [if_neg hh₁] at hc
  simp at hc

/-- Maximal models -/
def mm {n : ℕ} : Finset (Fin n) → Finset (Finset (Fin n)) :=
  fun X => {Y | X ∩ Y ≠ ∅}

/-- `mm` is a maximal model of A5 and B5. -/
theorem mm_maximal {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n)))
    (a5 : A5 ob) (b5 : B5 ob) (X : Finset (Fin n)):
    ob X ⊆ mm X := by
  intro Y h
  simp [mm]
  intro hc
  have : X ∩ Y ∈ ob X := b5 X Y (X ∩ Y) (by ext;simp) h
  rw [hc] at this
  exact a5 _ this

theorem mm_A5 {n : ℕ} : A5 <| @mm n := by simp [mm, A5]

open Finset
theorem mm_B5 {n : ℕ} : B5 <| @mm n := by
  intro X Y Z h₀ h₁
  simp [mm, B5] at *
  contrapose! h₁
  rw [← h₁,inter_comm,h₀, inter_comm]

theorem mm_C5 {n : ℕ} : C5 <| @mm n := by
  intro X Y Z h₀ h₁
  simp [mm] at *

theorem mm_D5 {n : ℕ} : D5 <| @mm n := by
  intro X Y Z h₀ h₁ h₂
  simp [mm] at *
  contrapose! h₁
  apply subset_empty.mp
  apply subset_trans
  show _ ⊆ Z ∩ (Z \ X ∪ Y)
  intro;simp;tauto
  rw [h₁]

theorem mm_E5 {n : ℕ} : E5 <| @mm n := by
  intro X Y Z h₀ h₁ h₂
  simp [mm] at *
  exact h₂

theorem mm_F5 {n : ℕ} : F5 <| @mm n := by
  intro X Y Z h₀ h₁
  simp [mm] at *
  rw [union_inter_distrib_right]
  contrapose! h₀
  apply subset_empty.mp
  apply subset_trans
  show _ ⊆ Y ∩ X ∪ Z ∩ X
  simp
  rw [h₀]

theorem mm_G5 {n : ℕ} : G5 <| @mm n := by
  intro X Y Z h₀ h₁ h₂
  simp [mm] at *
  exact h₂

theorem without_A5_we_have_a_very_large_model {n : ℕ} :
    B5 (fun _ : Finset (Fin n) => univ) ∧
    C5 (fun _ : Finset (Fin n) => univ) ∧
    D5 (fun _ : Finset (Fin n) => univ) ∧
    E5 (fun _ : Finset (Fin n) => univ) ∧
    F5 (fun _ : Finset (Fin n) => univ) ∧
    G5 (fun _ : Finset (Fin n) => univ) := by
  simp [B5, C5, D5, E5, F5, G5]

/-- Can also define and prove that this model is maximal for the {all except B5} set
in fact using just A5. -/
def maximal_model {α : Type*} [Fintype α] [DecidableEq α]
  (ob : Finset α → Finset (Finset α))
  (axioms : (Finset α → Finset (Finset α)) → Prop) :=
  axioms ob ∧ ∀ ob', axioms ob' → ∀ X, ob' X ⊆ ob X
-- since this is unique if it exists, maybe should be defined using a `Part` type

example (U : Type*) (h : Unique U) : U := default

example (U : Type*) : Option U := default

example : Unique {x : ℕ // x < 3 ∧ x > 1} := {
  default := ⟨2, by omega⟩
  uniq := by
    intro a;show a = ⟨2, by omega⟩;have := a.2
    suffices a.1 =2 by exact Subtype.coe_eq_of_eq_mk this
    omega
}


lemma without_B5_we_have_a_very_large_model {n : ℕ} :
    A5 (fun _ : Finset (Fin n) => univ \ {∅}) ∧
    C5 (fun _ : Finset (Fin n) => univ \ {∅}) ∧
    D5 (fun _ : Finset (Fin n) => univ \ {∅}) ∧
    E5 (fun _ : Finset (Fin n) => univ \ {∅}) ∧
    F5 (fun _ : Finset (Fin n) => univ \ {∅}) ∧
    G5 (fun _ : Finset (Fin n) => univ \ {∅}) := by
  simp [A5, C5, D5, E5, F5, G5]
  constructor
  · intro X Y Z h₀ h₁ h₂
    contrapose! h₂
    rw [h₂]
    simp
  constructor
  · intro X Y Z h₀ h₁ h₂ h₃ hc
    subst hc
    simp at h₁
  constructor
  · intro X Y Z h₀ h₁ h₂ h₃
    exact h₁ h₃
  · intro X Y Z h₀ h₁ h₂ h₃
    apply h₂
    rw [h₃]
    simp

theorem max_except_B5 {n : ℕ} :
    maximal_model (fun _ : Finset (Fin n) => univ \ {∅})
    (fun ob => A5 ob ∧ C5 ob ∧ D5 ob ∧ E5 ob ∧ F5 ob ∧ G5 ob) := by
  constructor
  simp
  exact without_B5_we_have_a_very_large_model
  intro ob
  simp
  intro a5 _ _ _ _ _
  intro X Y h
  simp
  intro hc
  rw [hc] at h
  exact a5 _ h


theorem ought_mm {n : ℕ} (A B : Finset (Fin n)) :
    Ought mm A univ ∧ Ought mm B Aᶜ := by simp [Ought,mm]
