import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Finset.Basic
import Deontic.Basic
import Deontic.Finset

/-!

## Canonical models of Carmo and Jones' systems

Abstract: We show that the two approaches sketched in

* Kjos-Hanssen 2017

are both consistent with

* Carmo Jones 2022.

Preferably, we let `F(X) = X ∩ A` for a fixed set `A`.

However, to incorporate contrary-to-duty obligations we introduce a predicate `B`,
where `A` worlds, `A ⊆ B`, are the best and `B \ A` worlds the second best.

Thus, if `X ∩ A = ∅` but `X ∩ B ≠ ∅`, we let `F(X) = X ∩ B`.

We prove the following results about which axioms hold in which model.

| Axiom \ Model | `canon` | `canon_II` | `canon₂` | `canon₂_II` |
| ------------- | ------- | ---------- | -------- | ----------- |
| A             | ✓       | ✓          | ✓        | ✓           |
| B             | ✓       | ✓          | ✓        | ✓           |
| C             | ✓       | ✓          | ✓        | ✓           |
| D             | thus ✓  | ×          | ✓        | thus ×      |
| E             | ×       | ✓          | thus ×   | ✓           |
| F             | ✓       | ✓          | ✓        | ×!          |
| G             | ✓       | ✓          | ×!       | ✓           |

-/

open Finset

section Venn_lemmas

lemma inter_eq_empty_of_subset {n : ℕ} {A X Y : Finset (Fin n)}
    (h₀ : Y ⊆ X) (h₁ : X ∩ A = ∅) : Y ∩ A = ∅ := by
  rw [← subset_empty] at h₁ ⊢
  exact (inter_subset_inter h₀ (subset_refl _)).trans h₁

lemma inter_subset_restrict {n : ℕ} {B X Y Z : Finset (Fin n)} (h₀ : Y ⊆ X)
    (h₁ : X ∩ B = X ∩ Z) : Y ∩ B ⊆ Y ∩ Z := by
  apply subset_inter
  · exact inter_subset_left
  · intro a ha
    apply mem_of_mem_inter_right
    rw [← h₁]
    simp only [mem_inter] at ha ⊢
    constructor
    · exact h₀ ha.1
    · exact ha.2

lemma inter_eq_restrict {n : ℕ} {B X Y Z : Finset (Fin n)}
    (h₀ : Y ⊆ X) (h₁ : X ∩ B = X ∩ Z) : Y ∩ B = Y ∩ Z := by
  apply subset_antisymm
  exact inter_subset_restrict h₀ h₁
  exact inter_subset_restrict h₀ h₁.symm

lemma eq_inter_inter {n : ℕ} {U X Y Z : Finset (Fin n)}
    (h₀ : U = X ∩ Y) (h₁ : U = X ∩ Z) : U = X ∩ (Y ∩ Z) := by
  rw [← inter_self U]
  nth_rewrite 1 [h₀]
  rw [h₁]
  ext;simp;tauto

lemma inter_empty_of_restrict {n : ℕ} {B X Y Z : Finset (Fin n)}
    (h₀ : Y ⊆ X) (h₃ : Y ∩ B = ∅) (h₁ : X ∩ B = X ∩ Z) : Y ∩ Z = ∅ := by
  apply subset_empty.mp
  intro a h
  simp only [mem_inter] at h
  exact h₃ ▸ (mem_inter_of_mem h.1
         <| mem_of_mem_inter_right <| h₁ ▸ mem_inter_of_mem (h₀ h.1) h.2)


lemma inter_empty_of_restrict_restrict {n : ℕ} {A B : Finset (Fin n)} (h : A ⊆ B)
    {X Y Z : Finset (Fin n)}
    (h₀ : Y ⊆ X) (h₃ : Y ∩ B = ∅) (h₁ : X ∩ A = X ∩ Z) : Y ∩ Z = ∅ := by
  apply subset_empty.mp
  intro a ha
  simp only [mem_inter] at ha
  rw [← h₃]
  simp
  constructor
  exact ha.1
  apply h
  apply mem_of_mem_inter_right
  rw [h₁]
  simp only [mem_inter]
  tauto

lemma subset_same {n : ℕ} {B X Y Z : Finset (Fin n)}
    (h₀ : Y ∩ X = Z ∩ X) : X ∩ B ⊆ Y ↔ X ∩ B ⊆ Z := by
  constructor <;> exact fun h => by
      apply subset_trans <|subset_inter h inter_subset_left
      exact h₀ ▸ inter_subset_left


lemma eq_inter_inter_of_inter {n : ℕ} {B X Y Z : Finset (Fin n)}
    (h₀ : X ∩ B = X ∩ Y)
    (h₁ : Y ∩ B = Y ∩ Z) : X ∩ Y = X ∩ (Y ∩ Z) := by
  calc
    _ = (X ∩ Y) ∩ (X ∩ Y) := by simp only [inter_self]
    _ = (X ∩ Y) ∩ (X ∩ B) := by rw [← h₀]
    _ = X ∩ (Y ∩ B)       := by ext;simp;tauto
    _ = _                 := by rw [h₁]

lemma inter_inter_eq_empty {n : ℕ} {A B X Y Z : Finset (Fin n)}
    (h₁₀ : Y ∩ A = ∅)
    (h₀ : X ∩ A = X ∩ Y)
    (h₁ : Y ∩ B = Y ∩ Z) : X ∩ (Y ∩ Z) = ∅ := by
  calc
  _ = (X ∩ Y) ∩ (Y ∩ Z) := by ext;simp
  _ = (X ∩ A) ∩ (Y ∩ B) := by rw [← h₀,← h₁]
  _ = (X ∩ (Y ∩ A) ∩ B) := by ext;simp;tauto
  _ = ∅ := by rw [h₁₀];simp

lemma inter_inter_eq_empty' {n : ℕ} {A B y z x : Finset (Fin n)}
    (h₂ : y ∩ A = ∅)
    (h₀ : y ∩ B = y  ∩ z)
    (h₁ : z ∩ A = z ∩ x) : y ∩ (z ∩ x) = ∅ := by
  rw [← h₁, ← inter_assoc, ← h₀]
  rw [inter_assoc,inter_comm,inter_assoc]
  nth_rewrite 2 [inter_comm]
  rw [h₂]
  simp


end Venn_lemmas

def canon {n : ℕ} (A : Finset (Fin n)) :
Finset (Fin n) → Finset (Finset (Fin n)) :=
  fun S ↦ ite (S ∩ A = ∅) ∅ ((filter (fun T ↦ S ∩ A ⊆ T)) univ)

/-- The `canon` models, which say that
what is obligatory is to be in one of the still-possible optimal worlds,
satisfy all axioms except E5.
This corresponds to approach (I) in my 2017 paper.

CJ 2022 presumably prefer (II) and 5e.
We make a CJ style `canon_II` by letting `ob X = {Y | Y ∩ X = A ∩ X}`.
My 2017 (II) corresponds to:
-/
def canon_II {n : ℕ} (A : Finset (Fin n)) :
Finset (Fin n) → Finset (Finset (Fin n)) :=
  fun X ↦ ite (X ∩ A = ∅) ∅
  ((filter (fun Y ↦ X ∩ Y = X ∩ A)) univ)

lemma canon_II_symmetry {n : ℕ} (A : Finset (Fin n)) :
  canon_II A = (fun X ↦ ite (X ∩ A = ∅) ∅ ((filter (fun Y ↦ X ∩ A = X ∩ Y)) univ)) := by
    unfold canon_II
    ext x y
    split_ifs;tauto;simp;tauto

-- `canon_II` says that Y is obligatory if Y ≃ A.


theorem canon_II_E5 {n : ℕ} (A : Finset (Fin n)) :  E5 (canon_II A) := by
  unfold canon_II
  intro X Y Z h₀ h₁ h₂
  simp at *
  by_cases h₃ : X ∩ A = ∅
  . rw [if_pos h₃] at *; simp at h₁
  . rw [if_neg h₃] at *
    simp at *
    by_cases h₄ : Y ∩ A = ∅
    . rw [if_pos h₄] at *
      contrapose h₂;simp
      have h₅: Y ∩ Z ⊆ A := calc
        Y ∩ Z ⊆ X ∩ Z := by intro x;simp;tauto
        _     ⊆ _     := by rw [h₁];intro x;simp
      have h₆: Y ∩ Z ⊆ Y ∩ A := by intro x;simp;aesop
      rw [h₄] at h₆
      exact subset_empty.mp h₆
    . rw [if_neg h₄] at *; simp at *; exact inter_eq_restrict h₀ h₁

theorem not_canon_E5 : ∃ n : ℕ, ∃ A : Finset (Fin n), ¬ E5 (canon A) := by
  use 2; use filter (fun x ↦ x = 0) univ
  unfold E5 canon
  push_neg
  use univ
  use filter (fun x ↦ x = 1) univ
  use univ
  have h₀ (i : Fin 2): ¬ filter (fun x ↦ x = (i:Fin 2)) univ = ∅ := by
    intro hc
    have : (i:Fin 2) ∈ (∅:Finset (Fin 2)) := by rw [← hc];simp
    simp at this
  have h₂: filter (fun x ↦ x = (1:Fin 2)) univ ∩ filter (fun x ↦ x = 0) univ = ∅  := by
    ext x;simp;aesop
  constructor
  . intro x;simp
  . constructor
    . simp; rw [if_neg (h₀ 0)]; simp
    . simp
      constructor
      . aesop
      . intro hc; rw [if_pos h₂] at hc; simp at *


-- Finally let us show that canon_II does not satisfy D5.
theorem not_canon_II_D5 : ∃ n, ∃ A : Finset (Fin n), ¬ D5 (canon_II A) := by
  use 2
  use filter (fun i ↦ i = 0) univ
  unfold D5; push_neg
  use filter (fun i ↦ i = 0) univ
  use filter (fun i ↦ i = 0) univ
  use univ
  have h : 0 ∈ filter (fun i ↦ i = (0:Fin 2)) univ := by simp
  have h₀: ¬ filter (fun i ↦ i = (0:Fin 2)) univ = ∅ := by
    intro hc;rw [hc] at h;
    simp at h
  unfold canon_II; simp
  constructor
  . trivial
  . rw [if_neg h₀]; simp; tauto


def canon₂ {n : ℕ} (A B : Finset (Fin n))  : Finset (Fin n) → Finset (Finset (Fin n)) :=
  fun X ↦ ite (X ∩ B = ∅) ∅ (
      ite (X ∩ A = ∅)
      (filter (fun T ↦ X ∩ B ⊆ T) univ)
      (filter (fun T ↦ X ∩ A ⊆ T) univ)
  )


def canon₂_II {n : ℕ} (A B : Finset (Fin n))  : Finset (Fin n) → Finset (Finset (Fin n)) :=
  fun X ↦ ite (X ∩ B = ∅) ∅ (
      ite (X ∩ A = ∅)
      (filter (fun Y ↦ X ∩ B = X ∩ Y) univ)
      (filter (fun Y ↦ X ∩ A = X ∩ Y) univ)
  )

theorem canon₂_II_A5 {n:ℕ} (A B : Finset (Fin n)) : A5 (canon₂_II A B) := by
  intro X; unfold canon₂_II; split_ifs
  tauto;simp;tauto;simp;tauto

theorem canon₂_II_B5 {n:ℕ} (A B : Finset (Fin n)) : B5 (canon₂_II A B) := by
  unfold B5 canon₂_II
  intro X Y Z h₀
  split_ifs with h₁ h₂
  . simp
  . simp
    nth_rewrite 1 [inter_comm] at h₀; nth_rewrite 2 [inter_comm] at h₀
    rw [h₀]
  . simp
    nth_rewrite 1 [inter_comm] at h₀; nth_rewrite 2 [inter_comm] at h₀
    rw [h₀]


theorem canon₂_II_C5 {n:ℕ} (A B : Finset (Fin n)) : C5 (canon₂_II A B) := by
  unfold C5 canon₂_II
  intro X Y Z h₀ h₁ h₂
  simp at *
  split_ifs at * with h₃ h₄
  . simp only [not_mem_empty] at h₀
  . simp at *; exact eq_inter_inter h₀ h₁
  . simp at *; exact eq_inter_inter h₀ h₁

theorem canon₂_II_E5 {n : ℕ} {A B : Finset (Fin n)} (h : A ⊆ B) :
  E5 (canon₂_II A B) := by
  unfold canon₂_II
  intro X Y Z h₀ h₁ h₂
  simp at *
  split_ifs at * with h₃ _ _ h₆ _ _ _ h₁₀
  . tauto
  . simp at *; contrapose h₂; simp; exact inter_empty_of_restrict h₀ h₃ h₁
  . simp at *; contrapose h₂; simp; exact inter_empty_of_restrict_restrict h h₀ h₃ h₁
  . simp at *
  . simp at *; exact inter_eq_restrict h₀ h₁
  . simp at *; contrapose h₂; simp; exact inter_empty_of_restrict h₀ h₆ h₁
  . tauto
  . simp at *; contrapose h₆; simp; exact inter_eq_empty_of_subset h₀ h₁₀
  . simp at *; exact inter_eq_restrict h₀ h₁

theorem canon₂_II_G5 {n:ℕ} {A B : Finset (Fin n)} : G5 (canon₂_II A B) := by
  unfold G5 canon₂_II
  intro X Y Z h₀ h₁ h₂
  simp at *
  split_ifs at * with h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀
  simp at *
  tauto;tauto;tauto
  . simp at *; rw [h₀]; exact eq_inter_inter_of_inter h₀ h₁
  . simp at *; contrapose h₂; simp; exact inter_inter_eq_empty' h₆ h₀ h₁
  . tauto
  . simp at *; contrapose h₂; simp; exact inter_inter_eq_empty h₁₀ h₀ h₁
  . simp at *; exact h₀ ▸ eq_inter_inter_of_inter h₀ h₁


theorem not_canon₂_II_F5 : ∃ n : ℕ, ∃ A B : Finset (Fin n), A ⊆ B ∧ ¬ F5 (canon₂_II A B) := by
  use 2; use filter (fun i ↦ i = 0) univ; use univ
  use (by trivial)
  unfold F5; push_neg
  use univ; use filter (fun i ↦ i = 1) univ; use filter (fun i ↦ i = 0) univ
  trivial

-- The guess would be that this has the same properties as `canon`.
-- For A5, the property A ⊆ B is not even needed:
theorem canon₂_A5 {n:ℕ} (A B : Finset (Fin n)) : A5 (canon₂ A B) := by
  unfold A5
  unfold canon₂
  intro X
  split_ifs with h₀ h₁;tauto;simp;contrapose h₀;simp at *;
  apply subset_empty.mp;simp_all
  simp;contrapose h₁;simp;apply subset_empty.mp;simp_all


theorem canon₂_B5 {n:ℕ} (A B : Finset (Fin n)) : B5 (canon₂ A B) := by
  unfold B5 canon₂
  intro X Y Z h₀
  split_ifs
  tauto;simp;exact subset_same h₀;simp;exact subset_same h₀

theorem canon₂_C5 {n:ℕ} (A B : Finset (Fin n)) : C5 (canon₂ A B) := by
  intro X Y Z h₀ h₁ h₂
  unfold canon₂ at *
  split_ifs at * with h₁
  . tauto
  . simp at *;exact subset_inter h₀ h₁
  . simp at *;exact subset_inter h₀ h₁


theorem canon₂_D5 {n:ℕ} {A B : Finset (Fin n)} (h : A ⊆ B) : D5 (canon₂ A B) := by
  unfold D5 canon₂
  intro X Y Z _ h₁ h₂
  split_ifs at * with h₃ h₄ h₅ h₆ h₇ h₈
  . tauto
  . simp at *
    contrapose h₄
    simp
    ext u;simp;intro hu hc;
    have : u ∈ Z := h₂ hu
    have : u ∈ Z ∩ B := by simp;tauto
    rw [h₃] at this;simp at this
  . simp at *
    contrapose h₄
    simp
    ext u;simp;intro hu hc;
    have : u ∈ Z := h₂ hu
    have : u ∈ Z ∩ B := by simp;tauto
    rw [h₃] at this;simp at this
  . simp at *
  . simp at *
    intro u hu;simp;
    by_cases H : u ∈ X
    right;simp at hu;apply h₁;simp;tauto
    left; simp at hu;tauto
  . simp at *
    contrapose h₈
    simp;ext u;simp;intro hu hc;
    have : u ∈ Z ∩ A := by simp;tauto
    rw [h₆] at this
    simp at this
  . simp at *
  . simp at *
    intro u hu;simp;
    by_cases H : u ∈ X
    right;simp at hu;apply h₁;simp;tauto
    left; simp at hu;tauto
  . simp at *
    intro u hu;simp;
    by_cases H : u ∈ X
    right;simp at hu;apply h₁;simp;tauto
    left; simp at hu;tauto


-- July 7: Surprisingly, canon₂ doesn't satisfy G:
-- However, if canon₂_II does satisfy G then we can say G firmly belongs in the II category.
theorem not_canon₂_G: ∃ n:ℕ, ∃ (A B : Finset (Fin n)), A ⊆ B ∧ ¬ G5 (canon₂ A B) := by
  use 3
  use filter (fun i ↦ i = 2) univ
  use filter (fun i ↦ i = 0 ∨ i = 2) univ
  -- simp
  constructor
  . trivial
  . unfold G5 canon₂
    push_neg
    use filter (fun i ↦ i = 0 ∨ i = 1) univ
    use univ
    use filter (fun i ↦ i = 1 ∨ i = 2) univ
    simp
    constructor
    split_ifs with h₀ h₁
    . simp only [not_mem_empty]
      exact ne_of_beq_false rfl h₀
    . simp at *
    . contrapose h₁; simp; ext x; aesop

    constructor
    split_ifs with g₀ g₁
    . simp only [not_mem_empty]
      exact ne_of_beq_false rfl g₀
    . exact (ne_of_beq_false rfl g₁).elim
    . simp; trivial
    constructor
    . exact ne_of_beq_false rfl

    split_ifs with h₀ h₁
    . aesop
    . exact of_decide_eq_false rfl
    . contrapose h₁; simp; ext x;simp;aesop

lemma canon₂_F5 {n:ℕ} (A B : Finset (Fin n)) : F5 (canon₂ A B) := by
  unfold F5 canon₂; intro X Y Z h₀ h₁
  split_ifs at * with
    h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ _ _ _ _ _ h₁₇ h₁₈
  tauto;tauto;tauto;tauto;tauto;
  . simp at *;contrapose h₃;simp;rw [union_inter_distrib_right] at h₂
    exact (union_eq_empty.mp h₂).1
  . simp at *;contrapose h₃;simp;rw [union_inter_distrib_right] at h₂
    exact (union_eq_empty.mp h₂).1
  . simp at *;contrapose h₃;simp;rw [union_inter_distrib_right] at h₂
    exact (union_eq_empty.mp h₂).1
  . simp at *;contrapose h₃;simp;rw [union_inter_distrib_right] at h₂
    exact (union_eq_empty.mp h₂).1
  simp at *;simp at *;simp at *;simp at *;simp at *;
  . simp at *; rw [union_inter_distrib_right];apply union_subset;tauto;tauto
  . simp at *; contrapose h₁₈;simp;rw [union_inter_distrib_right] at h₁₁;
    exact (union_eq_empty.mp h₁₁).2
  . simp at *; contrapose h₁₇;simp;rw [union_inter_distrib_right] at h₁₁;
    exact (union_eq_empty.mp h₁₁).1
  . simp at *; contrapose h₁₇;simp;rw [union_inter_distrib_right] at h₁₁;
    exact (union_eq_empty.mp h₁₁).1
  simp at *;simp at *;simp at *;simp at *;simp at *;
  . simp at *; rw [union_inter_distrib_right]; apply union_subset
    rw [‹ Y ∩ A = ∅›]; simp; rw [‹ Z ∩ A = ∅›]; simp
  . simp at *; rw [union_inter_distrib_right]; apply union_subset
    rw [‹ Y ∩ A = ∅›]; simp; tauto
  . simp at *; rw [union_inter_distrib_right]; apply union_subset
    tauto; rw [‹ Z ∩ A = ∅›]; simp
  . simp at *; rw [union_inter_distrib_right]; apply union_subset
    tauto; tauto

/-- All the axioms (including the paradoxical B, D, E): -/
def CJ_all_2022 {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) : Prop :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧ D5 ob ∧ E5 ob ∧ F5 ob ∧ G5 ob

def CJ_noE_2022 {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) : Prop :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧ D5 ob         ∧ F5 ob ∧ G5 ob

/-- This could also be called CJ_2022. -/
def CJ_noD_2022 {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) : Prop :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧         E5 ob ∧ F5 ob ∧ G5 ob

def CJ_noDF_2022 {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) : Prop :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧         E5 ob ∧         G5 ob

def CJ_noEG_2022 {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) : Prop :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧ D5 ob         ∧ F5 ob

theorem CJ_no_DF_canon₂_II {n : ℕ} {A B : Finset (Fin n)} (h : A ⊆ B) :
  CJ_noDF_2022 (canon₂_II A B) := by
    use canon₂_II_A5 _ _
    use canon₂_II_B5 _ _
    use canon₂_II_C5 _ _
    use canon₂_II_E5 h
    use canon₂_II_G5

theorem CJ_no_EG_canon₂ {n : ℕ} {A B : Finset (Fin n)} (h : A ⊆ B) :
  CJ_noEG_2022 (canon₂ A B) := by
    use canon₂_A5 _ _
    use canon₂_B5 _ _
    use canon₂_C5 _ _
    use canon₂_D5 h
    use canon₂_F5 _ _

theorem F5_canon_II  {n : ℕ} {A : Finset (Fin n)} : F5 (canon_II A) := by
    -- must prove directly since F fails for canon₂_II !
      unfold F5 canon_II
      intro X Y Z h₀ h₁
      -- simp at *
      split_ifs at * with h₂ h₃ h₄ h₅
      tauto;tauto;tauto;simp at *;
      rw [union_inter_distrib_right] at h₂
      contrapose h₃;simp;
      let Q := @union_eq_empty (Fin n) _ (Y ∩ A) (Z ∩ A)
      tauto
      tauto;tauto;tauto;simp at *;
      rw [union_inter_distrib_right,h₀,h₁,union_inter_distrib_right]

theorem CJ_noD_canon_II {n : ℕ} {A : Finset (Fin n)} : CJ_noD_2022 (canon_II A) := by
    let R := @canon_II_symmetry n A
    rw [R]

    let W := @CJ_no_DF_canon₂_II n A A (by trivial)
    unfold CJ_noDF_2022 canon₂_II at W
    unfold CJ_noD_2022

    use (by

      let Q := @canon₂_II_A5 n A A
      unfold canon₂_II at Q
      simp at Q
      tauto
    )
    use (by
      let Q := @canon₂_II_B5 n A A
      unfold canon₂_II at Q
      simp at Q
      tauto
    )
    use (by
      let Q := @canon₂_II_C5 n A A
      unfold canon₂_II at Q
      simp at Q
      tauto
    )
    use (by
      let W := @canon_II_E5 n A
      rw [canon_II_symmetry] at W
      tauto
    )
    use (by
      let W := @F5_canon_II n A
      rw [@canon_II_symmetry n A] at W
      exact W
    )
    use (by
      let Q := @canon₂_II_G5 n A A
      unfold canon₂_II at Q
      simp at Q
      tauto
    )



theorem CJ_noE_canon {n : ℕ} {A : Finset (Fin n)} :
  CJ_noE_2022 (canon A) := by
    unfold canon
    use (by
      let Q := @canon₂_A5 n A A
      unfold canon₂ at Q;simp at Q; exact Q
    )
    use (by
      let Q := @canon₂_B5 n A A
      unfold canon₂ at Q;simp at Q; exact Q
    )
    use (by
      let Q := @canon₂_C5 n A A
      unfold canon₂ at Q;simp at Q; exact Q
    )
    use (by
      let Q := @canon₂_D5 n A A (by trivial)
      unfold canon₂ at Q; simp at Q; exact Q
    )
    use (by
      let Q := @canon₂_F5 n A A
      unfold canon₂ at Q; simp at Q; exact Q
    )
    use (by
      unfold G5 -- can't use canon₂_G since that doesn't hold!
      intro X Y Z h₀ h₁ h₂;simp at *;split_ifs at *
      tauto;tauto;tauto;simp at *;intro x hx;aesop
    )

lemma coincidence {n : ℕ} : canon    (univ : Finset (Fin n))
                          = canon_II (univ : Finset (Fin n)) := by
  unfold canon canon_II;simp


/-- We prove that for any n, there is an n-world model of A5 through G5,
namely: let ob(X) be all the supersets of X, except that ob(∅)=∅. -/
theorem CJ_all_canon_univ {n : ℕ} : CJ_all_2022 (canon (univ: Finset (Fin n))) := by
    unfold CJ_all_2022
    let R := @canon_II_E5 n univ
    rw [← coincidence] at R
    let Q := @CJ_noE_canon n univ
    unfold CJ_noE_2022 at Q
    tauto
