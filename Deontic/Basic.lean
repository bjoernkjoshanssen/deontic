import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Deontic.Venn
/-!
# Lemma II.2.2

We prove Lemma II.2.2 from [Carmo and Jones 2022].
-/

open Set

-- Carmo and Jones' axioms
def CJ5a {U : Type*} (ob : Set U → Set (Set U)) :=
    ∀ (X : Set U), ∅ ∉ ob X

def CJ5b {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (X Y Z : Set U), Z ∩ X = Y ∩ X → (Z ∈ ob X ↔ Y ∈ ob X)

/- This is the old one from 2002.
 def CJ5c (ob : Set U → Set (Set U)) :=
 ∀ (X Y Z : Set U), Y ∈ ob X → (Z ∈ ob X → Y ∩ Z ∈ ob X)
-/

def CJ5c_star {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (X : Set U) (β : Set (Set U)),
  (h1 : β ⊆ ob X) → (h2 : β ≠ ∅) → ⋂₀β ∩ X ≠ ∅ → ⋂₀β ∈ ob X

def CJ5c_star_finite {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (X : Set U) (Y Z : (Set U)),
  (Y ∈ ob X) → (Z ∈ ob X) → (X ∩ Y ∩ Z ≠ ∅) → (Y ∩ Z) ∈ ob X

def CJ5d {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (X Y Z : Set U), Y ⊆ X → Y ∈ ob X → X ⊆ Z → (Z \ X) ∪ Y ∈ ob Z

def CJ5e {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (X Y Z : Set U), Y ⊆ X → Z ∈ ob X → Y ∩ Z ≠ ∅ → Z ∈ ob Y

def CJ5bd {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (X Y Z : Set U), Y ∈ ob (X) ∧ X ⊆ Z → (Z \ X) ∪ Y ∈ ob (Z)

def CJ5f {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (β : Set (Set U)) (_ : β ≠ ∅) (X : Set U),
  (∀ Z, Z ∈ β →  X ∈ ob Z)  → (X ∈ ob (⋃₀ β))


--Lemma II.2.1 --
theorem bd5 {U : Type*} {ob : Set U → Set (Set U)}
    (b5 : CJ5b ob) (d5 : CJ5d ob) : CJ5bd ob := by
  intro X Y Z h
  have sets_eq : ((Z \ X) ∪ (Y ∩ X)) ∩ Z = ((Z \ X) ∪ Y) ∩ Z := by
    ext
    simp
    tauto
  have input2 : Y ∩ X ∈ ob X :=
    (b5 X Y (Y ∩ X) (by rw [inter_assoc, inter_self])).mpr h.1
  exact (b5 Z ((Z \ X) ∪ Y) ((Z \ X) ∪ (Y ∩ X)) sets_eq).mp
    (d5 X (Y ∩ X) Z inter_subset_right input2 h.2)


lemma implication_in_ob {U : Type*} {ob : Set U → Set (Set U)}
    (b5 : CJ5b ob) (d5 : CJ5d  ob) {β : Set (Set U)} {X : Set U}
    (h : X ∈ ⋂₀ (ob '' β)) : {(⋃₀ β \ Z) ∪ X | Z ∈ β} ⊆ ob (⋃₀ β) := by
  have h : ∀ Z ∈ β, X ∈ ob Z := by simp at h;exact h
  exact fun _ ⟨Y,hY⟩ => hY.2 ▸ bd5 b5 d5 Y X (⋃₀ β)
    ⟨h Y hY.1, fun _ hy => mem_sUnion.mpr ⟨Y,hY.1, hy⟩⟩

lemma inter_not_empty {U : Type*} {ob : Set U → Set (Set U)}
    {β : Set (Set U)} {X : Set U} (h2 : β ≠ ∅)
    (h3 : ∀ Z ∈ β, X ∈ ob Z) (a5 : CJ5a ob) (b5 : CJ5b ob) :
    ⋂₀ {⋃₀ β \ Z ∪ X | Z ∈ β} ∩ ⋃₀ β ≠ ∅ := by
  obtain ⟨Z, hZ⟩ := exists_mem_of_ne_empty h2
  have hZ2 := h3 Z hZ
  have xz_not_empty : X ∩ Z ≠ ∅ := by
    intro hc
    apply a5 Z
    specialize b5 Z ∅ X (by rw [hc,empty_inter])
    apply b5.mp <| h3 _ hZ
  have xz_subset_xh : X ∩ Z ⊆ X ∩ ⋃₀β := fun a ha =>
    ⟨ha.1, mem_sUnion.mpr ⟨Z,hZ, ha.2⟩⟩
  rw [← in_union_yet_in_none' X h2]
  exact fun hi => xz_not_empty <| subset_eq_empty (hi ▸ xz_subset_xh) rfl

/-- Lemma II.2.2 -/
theorem II_2_2 {U : Type} {ob : Set U → Set (Set U)} (a5 : CJ5a ob)
    (b5 : CJ5b ob) (cstar5 : CJ5c_star ob) (d5 : CJ5d ob) : CJ5f ob := by
  intro β h2 X h3
  rw [in_union_yet_in_none' X h2]
  have h3₀ : X ∈ ⋂₀ (ob '' β) := by simp; exact h3
  exact cstar5
    (⋃₀ β) {(⋃₀ β \ Z) ∪ X | Z ∈ β}
    (implication_in_ob b5 d5 h3₀)
    (not_empty X h2)
    (inter_not_empty h2 h3 a5 b5)
