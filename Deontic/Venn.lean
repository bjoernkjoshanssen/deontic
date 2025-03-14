import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Finset.Basic

/-!

## Venn diagram lemmas

-/

open Finset


lemma inter_eq_empty_of_subset {α : Type*} [Fintype α] [DecidableEq α]
    {A X Y : Finset α} (h₀ : Y ⊆ X) (h₁ : X ∩ A = ∅) : Y ∩ A = ∅ := by
  rw [← subset_empty] at h₁ ⊢
  exact (inter_subset_inter h₀ (subset_refl _)).trans h₁

lemma inter_subset_restrict {α : Type*} [Fintype α] [DecidableEq α]
    {B X Y Z : Finset α} (h₀ : Y ⊆ X) (h₁ : X ∩ B ⊆ X ∩ Z) :
    Y ∩ B ⊆ Y ∩ Z := by
  apply subset_inter
  · exact inter_subset_left
  · intro a ha
    apply mem_of_mem_inter_right
    apply h₁
    simp only [mem_inter] at ha ⊢
    constructor
    · exact h₀ ha.1
    · exact ha.2

lemma inter_eq_restrict {α : Type*} [Fintype α] [DecidableEq α]
    {B X Y Z : Finset α} (h₀ : Y ⊆ X) (h₁ : X ∩ B = X ∩ Z) :
    Y ∩ B = Y ∩ Z := by
  apply subset_antisymm
  exact inter_subset_restrict h₀ (by rw [h₁])
  exact inter_subset_restrict h₀ (by rw [h₁])

lemma eq_inter_inter {α : Type*} [Fintype α] [DecidableEq α]
    {U X Y Z : Finset α} (h₀ : U = X ∩ Y) (h₁ : U = X ∩ Z) :
    U = X ∩ (Y ∩ Z) := by
  rw [← inter_self U]
  nth_rewrite 1 [h₀]
  rw [h₁]
  ext;simp;tauto

lemma inter_empty_of_restrict {α : Type*} [Fintype α] [DecidableEq α]
    {B X Y Z : Finset α} (h₀ : Y ⊆ X) (h₃ : Y ∩ B = ∅)
    (h₁ : X ∩ B = X ∩ Z) : Y ∩ Z = ∅ := by
  apply subset_empty.mp
  intro a h
  simp only [mem_inter] at h
  exact h₃ ▸ mem_inter_of_mem h.1 <| mem_of_mem_inter_right
     <| h₁ ▸ mem_inter_of_mem (h₀ h.1) h.2


lemma inter_empty_of_restrict₂ {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Finset α} (hAB : A ⊆ B) {X Y Z : Finset α} (hYX : Y ⊆ X)
    (h₀ : Y ∩ B = ∅) (h₁ : X ∩ Z ⊆ X ∩ A) : Y ∩ Z = ∅ := by
  apply subset_empty.mp
  intro a ha
  rw [← h₀]
  simp only [mem_inter] at ha ⊢
  constructor
  exact ha.1
  apply hAB
  suffices a ∈ X ∩ A by rw [mem_inter] at this; exact this.2
  apply h₁
  simp only [mem_inter]
  exact ⟨hYX ha.1, ha.2⟩

lemma subset_same {α : Type*} [Fintype α] [DecidableEq α]
    {B X Y Z : Finset α} (h₀ : Y ∩ X = Z ∩ X) :
    X ∩ B ⊆ Y ↔ X ∩ B ⊆ Z := by
  constructor <;> exact fun h => by
      apply subset_trans <|subset_inter h inter_subset_left
      exact h₀ ▸ inter_subset_left


lemma eq_inter_inter_of_inter₀ {α : Type*} [Fintype α] [DecidableEq α]
    {B X Y Z : Finset α} (h₀ : X ∩ B = X ∩ Y) (h₁ : Y ∩ B = Y ∩ Z) :
    X ∩ Y ⊆ Z := by
  have := @subset_same α _ _ X Y B Z (by rw [inter_comm, h₁,inter_comm])
  rw [inter_comm]
  apply this.mp
  rw [inter_comm, ← h₀]
  simp

lemma eq_inter_inter_of_inter {α : Type*} [Fintype α] [DecidableEq α]
    {B X Y Z : Finset α} (h₀ : X ∩ B = X ∩ Y) (h₁ : Y ∩ B = Y ∩ Z) :
    X ∩ Y = X ∩ (Y ∩ Z) := by
  rw [← inter_assoc]
  exact Eq.symm <| inter_eq_left.mpr <| eq_inter_inter_of_inter₀ h₀ h₁

lemma inter_eq_empty₀ {α : Type*} [Fintype α] [DecidableEq α]
    {A X Y : Finset α} (h₁ : Y ∩ A = ∅) (h₀ : X ∩ A = X ∩ Y) :
    X ∩ Y = ∅ := by
  suffices (X ∩ Y) ∩ (X ∩ Y) = ∅  by
    simp at this
    exact this
  nth_rewrite 1 [← h₀]
  rw [inter_assoc]
  nth_rewrite 3 [inter_comm]
  nth_rewrite 2 [← inter_assoc]
  nth_rewrite 3 [inter_comm]
  rw [h₁]
  simp

lemma inter_inter_eq_empty {α : Type*} [Fintype α] [DecidableEq α]
    {A X Y Z : Finset α} (h₁ : Y ∩ A = ∅) (h₀ : X ∩ A = X ∩ Y) :
    X ∩ (Y ∩ Z) = ∅ := by
  rw [← inter_assoc, inter_eq_empty₀ h₁ h₀, empty_inter]

lemma inter_inter_eq_empty' {α : Type*} [Fintype α] [DecidableEq α]
    {A B y z x : Finset α} (h₂ : A ∩ y = ∅) (h₀ : y ∩ B = y  ∩ z)
    (h₁ : z ∩ A = z ∩ x) : y ∩ (z ∩ x) = ∅ := by
  rw [← h₁, ← inter_assoc, ← h₀, inter_assoc, inter_comm,
              inter_assoc,   h₂, inter_empty]

theorem subset_inter_within {α : Type*} [Fintype α] [DecidableEq α]
    {A X Y Z : Finset α} (h₀ : X ∩ A ⊆ Y) (h₁ : Y ∩ A ⊆ Z) :
    X ∩ A ⊆ Y ∩ Z :=
  subset_inter h₀ <| (subset_inter h₀ inter_subset_right).trans h₁

theorem inter_empty_of_inter_union_empty {α : Type*} [Fintype α]
    [DecidableEq α] {B Y Z : Finset α} (h₂ : (Y ∪ Z) ∩ B = ∅) :
    Y ∩ B = ∅ := by
  apply subset_empty.mp
  apply subset_trans
  · show Y ∩ B ⊆ (Y ∪ Z) ∩ B
    exact inter_subset_inter subset_union_left (subset_refl B)
  · apply subset_empty.mpr h₂

lemma forall_or_right_mem {α : Type*} (β : Set α)
    (F : α → Prop) (Q : Prop) :
    (∀ x ∈ β, F x ∨ Q) ↔ (∀ x ∈ β, F x) ∨ Q := by
  constructor
  exact fun h => forall_or_right.mp
        fun y => forall_or_right.mp (h y)
  tauto


lemma forall_or_right_union {U : Type*}  {β : Set (Set U)} {X : Set U} :
    ⋂₀ {(⋃₀ β) \ Z ∪ X | Z ∈ β} = (⋂₀ {(⋃₀ β) \ Z | Z ∈ β}) ∪ X := by
  ext u
  simp
  apply forall_or_right_mem

lemma exists_mem_of_ne_empty {U : Type*}
    {β : Set (Set U)} (h2 : β ≠ ∅) : ∃ B, B ∈ β := by
  by_contra
  apply h2
  ext q
  tauto

/-- An element cannot belong to ⋃β, while for each particular Z ∈ β,
 not belonging to *that* one. -/
theorem in_union_yet_in_none.{u_1} {U : Type u_1} {β : Set (Set U)}
    (h2 : β ≠ ∅) : ⋂₀ {⋃₀ β \ Z | Z ∈ β} = ∅ := by
  ext a
  constructor
  · intro ha
    simp at ha
    obtain ⟨B, hB⟩ := exists_mem_of_ne_empty h2
    have uh := ha B hB
    obtain ⟨C, hC⟩ := uh.1
    exact (ha C hC.1).2 hC.2
  · simp

lemma in_union_yet_in_none'
    {U : Type*} {β : Set (Set U)} (X : Set U) (h2 : β ≠ ∅) :
    X = ⋂₀ {(⋃₀ β \ Z) ∪ X | Z ∈ β} := by
  rewrite [forall_or_right_union, in_union_yet_in_none h2]
  simp

lemma not_empty {U : Type*} {β : Set (Set U)} (X : Set U) (h2 : β ≠ ∅) :
    {⋃₀ β \ Z ∪ X | Z ∈ β} ≠ ∅ := by
   obtain ⟨Z, hZ⟩ := exists_mem_of_ne_empty h2
   have : (⋃₀β \ Z ∪ X) ∈ {x | ∃ Z ∈ β, ⋃₀ β \ Z ∪ X = x} := by use Z
   exact ne_of_mem_of_not_mem' this (fun a ↦ a)
