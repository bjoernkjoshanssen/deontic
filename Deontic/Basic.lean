import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Basic

/-!
## Carmo and Jones' system(s) of deontic logic for contrary-to-duty obligations

 - Carmo and Jones 2002
 - Carmo and Jones 2013
 - Kjos-Hanssen 2017
 - Carmo and Jones 2022
-/

open Set

-- Carmo and Jones' axioms
def CJ5a {U : Type*} (ob : Set U → Set (Set U)) := ∀ (X : Set U), ∅ ∉ ob X

def CJ5b {U : Type*} (ob : Set U → Set (Set U)) := ∀ (X Y Z : Set U), Z ∩ X = Y ∩ X → (Z ∈ ob X ↔ Y ∈ ob X)

-- This is the old one from 2002.
-- def CJ5c (ob : Set U → Set (Set U)) := ∀ (X Y Z : Set U), Y ∈ ob X → (Z ∈ ob X → Y ∩ Z ∈ ob X)

def CJ5c_star {U : Type*} (ob : Set U → Set (Set U)) := ∀ (X : Set U) (β : Set (Set U)),
  (h1 : β ⊆ ob X) → (h2 : β ≠ ∅) → ⋂₀β ∩ X ≠ ∅ → ⋂₀β ∈ ob X

def CJ5c_star_finite {U : Type*} (ob : Set U → Set (Set U)) := ∀ (X : Set U) (Y Z : (Set U)),
  (Y ∈ ob X) → (Z ∈ ob X) → (X ∩ Y ∩ Z ≠ ∅) → (Y ∩ Z) ∈ ob X

def CJ5d {U : Type*} (ob : Set U → Set (Set U)) := ∀ (X Y Z : Set U), Y ⊆ X → Y ∈ ob X → X ⊆ Z → (Z \ X) ∪ Y ∈ ob Z

def CJ5e {U : Type*} (ob : Set U → Set (Set U)) := ∀ (X Y Z : Set U), Y ⊆ X → Z ∈ ob X → Y ∩ Z ≠ ∅ → Z ∈ ob Y

def CJ5bd {U : Type*} (ob : Set U → Set (Set U)) := ∀ (X Y Z : Set U), Y ∈ ob (X) ∧ X ⊆ Z → (Z \ X) ∪ Y ∈ ob (Z)

def CJ5f {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (β : Set (Set U)) (_ : β ≠ ∅) (X : Set U),
  (∀ Z, Z ∈ β →  X ∈ ob Z)  → (X ∈ ob (⋃₀ β))


--Lemma II.2.1 --
theorem bd5 {U : Type*} {ob : Set U → Set (Set U)} (b5 : CJ5b ob) (d5 : CJ5d ob) : CJ5bd ob := by
 intro X Y Z h
 have YZX_eq_YX : (Y ∩ X) ∩ X = Y ∩ X := by
    ext
    simp
 have sets_eq : ((Z \ X) ∪ (Y ∩ X)) ∩ Z = ((Z \ X) ∪ Y) ∩ Z := by
    ext
    simp
    tauto
 have input1 : Y ∩ X ⊆ X := by
    simp
 have input2 : Y ∩ X ∈ ob X := by
    exact (b5 X Y (Y ∩ X) YZX_eq_YX).mpr h.1
 exact (b5 Z ((Z \ X) ∪ Y) ((Z \ X) ∪ (Y ∩ X)) sets_eq).mp (d5 X (Y ∩ X) Z input1 input2 h.2)

lemma first_equality {U : Type*}  {β : Set (Set U)} {X : Set U} :
  ⋂₀ {x | ∃ Z ∈ β, ⋃₀ β \ Z ∪ X = x}
= ⋂₀ {x | ∃ Z ∈ β, ⋃₀ β \ Z = x} ∪ X := by
      ext x
      simp
      constructor
      intro ha
      by_cases hx : x ∈ X
      exact Or.inr hx
      left
      intros b hb
      have hb2 := ha b
    --   apply hb2 at hb
      constructor
      tauto --exact hb.left
      cases hb2 hb
      tauto
      exfalso
      tauto
      intro ha
      intros b hb
      cases ha with
      | inl h => left; have := h b;tauto
      | inr h => tauto


lemma subset_of_Union {U : Type*}
 {ob : Set U → Set (Set U)}
(b5 : CJ5b ob) (d5 : CJ5d  ob)
{β : Set (Set U)}
{X : Set U}
{h3 : ∀ Z ∈ β, X ∈ ob Z}
: {(⋃₀ β \ Z) ∪ X | Z ∈ β} ⊆ ob (⋃₀ β) := by
   intros a ha
   simp_all
   obtain ⟨Y,hY⟩ := mem_setOf.mp ha
   have X_in_obY := h3 Y hY.left
   have Y_subset_H : Y ⊆ (⋃₀β) := by
      intros y hy
      apply mem_sUnion.mpr
      use Y
      exact And.intro hY.left hy
   have hfinal := bd5 b5 d5 Y X (⋃₀β) (And.intro (X_in_obY) (Y_subset_H))
   rewrite [hY.right] at hfinal
   exact hfinal

lemma exists_at_beta {U : Type*}
{β : Set (Set U)} {h2 : β ≠ ∅} : ∃ B, B ∈ β := by
  by_contra; apply h2; ext q; tauto

lemma defX {U : Type*}
{β : Set (Set U)}
{X : Set U}
{h2 : β ≠ ∅}
: X = ⋂₀ {x | ∃ Z ∈ β, ⋃₀ β \ Z ∪ X = x} := by
    have second_equality : ⋂₀{⋃₀β \ Z | Z ∈ β} = ∅ := by
      ext a
      constructor
      intro ha
      simp at ha
      exfalso
      have exists_at_beta := @exists_at_beta U β h2
      obtain ⟨B, hB⟩ := exists_at_beta
      have uh := ha B hB
      obtain ⟨C, hC⟩ := uh.left
      have oh := ha C hC.left
      tauto --exact oh hC.right
      tauto
    rewrite [first_equality, second_equality]
    simp

lemma not_empty  {U : Type*} {ob : Set U → Set (Set U)}
  {β : Set (Set U)} {X : Set U} {h2 : β ≠ ∅} {h3 : ∀ Z ∈ β, X ∈ ob Z}
(a5 : CJ5a ob)
: {x | ∃ Z ∈ β, ⋃₀ β \ Z ∪ X = x} ≠ ∅ := by
   have exists_at_beta := @exists_at_beta U β h2
   obtain ⟨Z, hZ⟩ := exists_at_beta
   have hZ2 := h3 Z hZ
   have h := a5 Z
   have fx : X ≠ ∅ := by intro f2; subst f2; tauto
   by_contra oh_no
   have here_we_go : (⋃₀β \ Z ∪ X) ∈  {x | ∃ Z ∈ β, ⋃₀ β \ Z ∪ X = x} := by tauto
   rewrite [oh_no] at here_we_go
   tauto

lemma inter_not_empty {U : Type*} {ob : Set U → Set (Set U)}
{β : Set (Set U)}
{X : Set U}
{h2 : β ≠ ∅}
{h3 : ∀ Z ∈ β, X ∈ ob Z} (a5 : CJ5a ob) (b5 : CJ5b ob)
: ⋂₀ {x | ∃ Z ∈ β, ⋃₀ β \ Z ∪ X = x} ∩ ⋃₀ β ≠ ∅ := by
   rw [←defX]
   intro hi
   obtain ⟨Z, hZ⟩ := @exists_at_beta U β h2
   have hZ2 := h3 Z hZ
   have xz_not_empty : X ∩ Z ≠ ∅ := by
      intro f
      have obvious : X ∩ Z = ∅ ∩ Z := by (simp; exact f)
      have hc := b5 Z ∅ X obvious
      tauto
   have xz_subset_xh : X ∩ Z ⊆ X ∩ ⋃₀β := by
      intros a ha
      exact And.intro (ha.left) (mem_sUnion.mpr (Exists.intro Z (And.intro hZ ha.right)))
   rewrite [hi] at xz_subset_xh
   apply xz_not_empty
   ext u
   simp
   tauto
   exact h2

--Lemma II.2.2 --
theorem II_2_2 {U : Type} {ob : Set U → Set (Set U)}
  (a5 : CJ5a ob)
  (b5 : CJ5b ob)
  (cstar5 : CJ5c_star ob)
  (d5 : CJ5d ob)
  : CJ5f ob := by
  unfold CJ5f
  intro β h2 X
  intros h3
  have defX := @defX U β X h2
  have not_empty := @not_empty U ob β X h2 h3
  have inter_not_empty := @inter_not_empty U ob β X h2 h3
  have ending := cstar5
    (⋃₀ β) ({(⋃₀ β \ Z) ∪ X | Z ∈ β})
    (@subset_of_Union U ob b5 d5 β X h3)
    (not_empty a5)
    (inter_not_empty a5 b5)
  rewrite [←defX] at ending
  exact ending
