import Deontic.Basic
import Deontic.Finset
import Deontic.Venn
/-!

## Canonical models of Carmo and Jones' systems

Abstract: We show that the two approaches sketched in [Kjos-Hanssen 2017]
are both consistent with [Carmo Jones 2022].

Preferably, we let `F(X) = X ∩ A` for a fixed set `A`.

However, to incorporate contrary-to-duty obligations we introduce a predicate `B`,
where `A` worlds, `A ⊆ B`, are the best and `B \ A` worlds the second best.

Thus, if `X ∩ A = ∅` but `X ∩ B ≠ ∅`, we let `F(X) = X ∩ B`.

We prove the following results about which axioms hold in which model.
Since the models without the subscript ₂ are special cases of those
with it, some results follow: these are indicated with (parentheses).

| Axiom \ Model | `canon`      | `canon_II`      | `canon₂`     | `canon₂_II`      |
| ------------- | ------------ | --------------- | ------------ | ---------------- |
| A             | (✓           | (✓)             | ✓            | ✓                |
|               |              |                 |`canon₂_A5`   |`canon₂_II_A5`    |
| ------------- | ------------ | --------------- | ------------ | ---------------- |
| B             | (✓)          | (✓)             | ✓            | ✓                |
|               |              |                 |`canon₂_B5`   |`canon₂_II_B5`    |
| ------------- | ------------ | --------------- | ------------ | ---------------- |
| C             | (✓)          | (✓)             | ✓            | ✓                |
|               |              |                 |`canon₂_C5`   |`canon₂_II_C5`    |
| ------------- | ------------ | --------------- | ------------ | ---------------- |
| D             | (✓)          | ×               | ✓            |(×)               |
|               |              |`not_canon_II_D5`|`canon₂_D5`   |                  |
| ------------- | ------------ | --------------- | ------------ | ---------------- |
| E             | ×            | ✓               |(×)           | ✓                |
|               |`not_canon_E5`|`canon_II_E5`    |              |`canon₂_II_E5`    |
| ------------- | ------------ | --------------- | ------------ | ---------------- |
| F             | (✓)          | ✓               | ✓            | ×!               |
|               |              |`canon_II_F5`    |`canon₂_F5`   |`not_canon₂_II_F5`|
| ------------- | ------------ | --------------- | ------------ | ---------------- |
| G             | ✓            | (✓)             | ×!           | ✓                |
|               |`canon_G`     |                 |`not_canon₂_G`|`canon₂_II_G5`    |
| ------------- | ------------ | --------------- | ------------ | ---------------- |
-/

open Finset

def canon {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
Finset α → Finset (Finset α) :=
  fun S ↦ ite (S ∩ A = ∅) ∅ ((filter (fun T ↦ S ∩ A ⊆ T)) univ)

/-- The `canon` models, which say that
what is obligatory is to be in one of the still-possible optimal worlds,
satisfy all axioms except E5.
This corresponds to approach (I) in my 2017 paper.

CJ 2022 presumably prefer (II) and 5e.
We make a CJ style `canon_II` by letting `ob X = {Y | Y ∩ X = A ∩ X}`.
My 2017 (II) corresponds to:
-/
def canon_II {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
Finset α → Finset (Finset α) :=
  fun X ↦ ite (X ∩ A = ∅) ∅
  ((filter (fun Y ↦ X ∩ Y = X ∩ A)) univ)

lemma canon_II_symmetry {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
  canon_II A = (fun X ↦ ite (X ∩ A = ∅) ∅ ((filter (fun Y ↦ X ∩ A = X ∩ Y)) univ)) := by
    unfold canon_II
    ext x
    by_cases H : x ∩ A = ∅
    · rw [H]
      simp
    · repeat rw [if_neg H]
      simp only [mem_filter, mem_univ, true_and]
      tauto

-- `canon_II` says that Y is obligatory if Y ≃ A.

/-- canon_II does satisfy axiom 5(e). -/
theorem canon_II_E5 {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :  E5 (canon_II A) := by
  unfold canon_II
  intro X Y Z h₀ h₁ h₂
  simp at *
  by_cases h₃ : X ∩ A = ∅
  . rw [h₃] at h₁
    simp at h₁
  . rw [if_neg h₃] at *
    simp at *
    by_cases h₄ : Y ∩ A = ∅
    . rw [if_pos h₄] at *
      exfalso
      apply h₂
      apply subset_empty.mp
      refine subset_trans ?_ <| subset_empty.mpr h₄
      apply subset_trans
      · show Y ∩ Z ⊆ Y ∩ (Y ∩ Z)
        rw [← inter_assoc, inter_self]
      · exact inter_subset_inter (fun ⦃a⦄ a ↦ a)
        <| subset_trans (inter_subset_inter h₀ fun ⦃a⦄ a ↦ a)
          <| h₁ ▸ inter_subset_right
    . rw [if_neg h₄] at *; simp at *; exact inter_eq_restrict h₀ h₁

/-- canon does not satisfy axiom 5(e). -/
theorem not_canon_E5 : ∃ n : ℕ, ∃ A : Finset (Fin n), ¬ E5 (canon A) := by
  use 2; use filter (fun x ↦ x = 0) univ
  unfold E5 canon
  push_neg
  use univ, filter (fun x ↦ x = 1) univ, univ
  constructor
  . exact filter_subset (fun x ↦ x = 1) univ
  . constructor
    . simp; rw [if_neg (by apply ne_empty_of_mem (a := 0);trivial)]; simp
    . simp
      constructor
      . apply ne_empty_of_mem (a := 1)
        trivial
      . intro hc; rw [if_pos (by rfl)] at hc; simp at *


/-- canon_II does not satisfy axiom 5(d). -/
theorem not_canon_II_D5 : ∃ n, ∃ A : Finset (Fin n), ¬ D5 (canon_II A) := by
  use 2, filter (fun i ↦ i = 0) univ
  unfold D5; push_neg
  use filter (fun i ↦ i = 0) univ, filter (fun i ↦ i = 0) univ, univ
  constructor
  . trivial
  · unfold canon_II
    rw [if_neg <| ne_empty_of_mem (by simp;rfl)]
    simp
    tauto


def canon₂ {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α)  : Finset α → Finset (Finset α) :=
  fun X ↦ ite (X ∩ B = ∅) ∅ (
      ite (X ∩ A = ∅)
      (filter (fun T ↦ X ∩ B ⊆ T) univ)
      (filter (fun T ↦ X ∩ A ⊆ T) univ)
  )


def canon₂_II {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α)  : Finset α → Finset (Finset α) :=
  fun X ↦ ite (X ∩ B = ∅) ∅ (
      ite (X ∩ A = ∅)
      (filter (fun Y ↦ X ∩ B = X ∩ Y) univ)
      (filter (fun Y ↦ X ∩ A = X ∩ Y) univ)
  )

/-- The canon₂_II models satisfy axiom 5(a). -/
theorem canon₂_II_A5  {α : Type*} [Fintype α] [DecidableEq α]
(A B : Finset α) : A5 (canon₂_II A B) := by
  intro X
  unfold canon₂_II
  split_ifs
  any_goals (simp only [mem_filter, mem_univ, inter_empty, true_and]; tauto)
  tauto

/-- The canon₂_II models satisfy axiom 5(b). -/
theorem canon₂_II_B5  {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : B5 (canon₂_II A B) := by
  unfold B5 canon₂_II
  intro X Y Z h₀
  split_ifs with h₁ h₂
  any_goals (
    simp only [mem_filter, mem_univ, true_and]
    nth_rewrite 1 [inter_comm] at h₀
    nth_rewrite 2 [inter_comm] at h₀
    rw [h₀]
  )
  simp only [not_mem_empty]


/-- The canon₂_II models satisfy axiom 5(c). -/
theorem canon₂_II_C5  {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : C5 (canon₂_II A B) := by
  unfold C5 canon₂_II
  intro X Y Z h₀ h₁ h₂
  split_ifs at * with h₃ h₄
  any_goals (simp only [not_mem_empty, mem_filter, mem_univ, true_and] at h₀ h₁ ⊢) <;>
  exact eq_inter_inter h₀ h₁

/-- The canon₂_II models satisfy axiom 5(e) if `A ⊆ B`. -/
theorem canon₂_II_E5 {α : Type*} [Fintype α] [DecidableEq α] {A B : Finset α} (h : A ⊆ B) :
  E5 (canon₂_II A B) := by
  unfold canon₂_II
  intro X Y Z h₀ h₁ h₂
  simp at *
  split_ifs at * with h₃ _ _ h₄ _ _ _ h₅
  any_goals (simp only [mem_filter, mem_univ, true_and, not_mem_empty] at h₁ ⊢)
  . exact h₂ <| inter_empty_of_restrict h₀ h₃ h₁
  . exact h₂ <| inter_empty_of_restrict_restrict h h₀ h₃ (by rw [h₁])
  . exact inter_eq_restrict h₀ h₁
  . exact False.elim <| h₂ <| inter_empty_of_restrict h₀ h₄ h₁
  . apply False.elim <| h₄ <| inter_eq_empty_of_subset h₀ h₅
  . exact inter_eq_restrict h₀ h₁

/-- The canon₂_II models satisfy axiom 5(g). -/
theorem canon₂_II_G5  {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : G5 (canon₂_II A B) := by
  unfold G5 canon₂_II
  intro X Y Z h₀ h₁ h₂
  split_ifs at * with _ _ _ h₃ _ _ _ h₄
  repeat tauto
  all_goals (simp only [inter_assoc, ne_eq, mem_filter, mem_univ, true_and] at *)
  . exact h₀ ▸ eq_inter_inter_of_inter h₀ h₁
  . rw [inter_comm] at h₃
    apply False.elim <| h₂ <| inter_inter_eq_empty' h₃ h₀ h₁
  · simp at h₁
  . apply False.elim <| h₂ <| inter_inter_eq_empty h₄ h₀
  . exact h₀ ▸ eq_inter_inter_of_inter h₀ h₁

/-- The canon₂_II models do not satisfy axiom 5(f). -/
theorem not_canon₂_II_F5 : ∃ n : ℕ, ∃ A B : Finset (Fin n), A ⊆ B ∧ ¬ F5 (canon₂_II A B) := by
  use 2, filter (fun i ↦ i = 0) univ, univ, by trivial
  unfold F5
  push_neg
  use univ, filter (fun i ↦ i = 1) univ, filter (fun i ↦ i = 0) univ
  trivial

/-- The canon₂ models satisfy axiom 5(a). -/
theorem canon₂_A5  {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) : A5 (canon₂ A B) := by
  intro X
  unfold canon₂
  split_ifs with h₀ h₁
  any_goals (simp only [mem_filter, mem_univ, subset_empty, true_and,not_mem_empty, not_false_eq_true])
  · exact h₀
  · exact h₁

/-- The canon₂ models satisfy axiom 5(b). -/
theorem canon₂_B5 {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) : B5 (canon₂ A B) := by
  unfold B5 canon₂
  intro X Y Z h₀
  split_ifs
  simp
  repeat simp only [mem_filter, mem_univ, true_and]; exact subset_same h₀

/-- The canon₂ models satisfy axiom 5(c). -/
theorem canon₂_C5 {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) : C5 (canon₂ A B) := by
  intro X Y Z h₀ h₁ h₂
  unfold canon₂ at *
  split_ifs at * with h₁
  . tauto
  repeat simp at *;exact subset_inter h₀ h₁

/-- The canon₂ models satisfy axiom 5(d). -/
theorem canon₂_D5 {α : Type*} [Fintype α] [DecidableEq α] {A B : Finset α} (h : A ⊆ B) : D5 (canon₂ A B) := by
  unfold D5 canon₂
  intro X Y Z _ h₁ h₂
  split_ifs at * with h₃ h₄ h₅ h₆ h₇ h₈
  . simp at h₁
  repeat exact (h₄ <| subset_empty.mp
      <| (inter_subset_inter h₂ (subset_refl _)).trans <| subset_empty.mpr h₃).elim
  . simp at h₁
  . simp only [mem_filter, mem_univ, true_and] at h₁ ⊢
    nth_rewrite 1 [← sdiff_union_inter Z]
    rw [union_inter_distrib_right]
    exact union_subset_union inter_subset_left
      <| (inter_subset_inter inter_subset_right (subset_refl _)).trans h₁
  . exact False.elim <| h₈ <| subset_empty.mp
      <| (inter_subset_inter h₂ (subset_refl _)).trans
      <| subset_empty.mpr h₆
  . simp at h₁
  . simp at h₁ ⊢
    nth_rewrite 1 [← sdiff_union_inter Z]
    rw [union_inter_distrib_right]
    exact union_subset_union inter_subset_left
      <| (inter_subset_inter inter_subset_right (subset_refl _)).trans
      ((inter_subset_inter (subset_refl _) h).trans h₁)
  . simp at h₁ ⊢
    nth_rewrite 1 [← sdiff_union_inter Z]
    rw [union_inter_distrib_right]
    exact union_subset_union inter_subset_left
      <| (inter_subset_inter inter_subset_right (subset_refl _)).trans h₁


-- Surprisingly, thee canon₂ models do not satisfy Axiom 5(g).
-- However, since canon₂_II does satisfy G (see `canon₂_II_G5`) G firmly belongs in the II category.
theorem not_canon₂_G: ∃ n:ℕ, ∃ (A B : Finset (Fin n)), A ⊆ B ∧ ¬ G5 (canon₂ A B) := by
  use 3, filter (fun i ↦ i = 2) univ, filter (fun i ↦ i = 0 ∨ i = 2) univ
  constructor
  . trivial
  . unfold G5
    push_neg
    use filter (fun i ↦ i = 0 ∨ i = 1) univ, univ, filter (fun i ↦ i = 1 ∨ i = 2) univ
    simp
    constructor
    unfold canon₂
    split_ifs with h₀ h₁
    . simp only [not_mem_empty]
      exact ne_of_beq_false rfl h₀
    . simp at *
    . contrapose h₁; simp; ext x; aesop

    constructor
    unfold canon₂
    split_ifs with g₀ g₁
    . simp only [not_mem_empty]
      exact ne_of_beq_false rfl g₀
    . exact (ne_of_beq_false rfl g₁).elim
    . simp; trivial
    constructor
    . exact ne_of_beq_false rfl

    unfold canon₂
    split_ifs with h₀ h₁
    . aesop
    . exact of_decide_eq_false rfl
    . contrapose h₁; simp; ext x;simp;aesop


/-- The canon₂ models satisfy axiom 5(f). -/
lemma canon₂_F5 {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) : F5 (canon₂ A B) := by
  intro X Y Z h₀ h₁
  unfold canon₂ at *
  split_ifs with h₂ h₃
  · rw [if_pos (inter_empty_of_inter_union_empty h₂)] at h₀
    exact h₀
  · split_ifs at * with
      h₁₀ h₃ h₄ h₅ h₆ h₇ h₈ h₉
    repeat (simp at h₀ h₁)
    · simp
      rw [union_inter_distrib_right]
      exact union_subset h₀ h₁
    · rw [union_comm] at h₃
      exact (h₈ <| inter_empty_of_inter_union_empty h₃).elim
    repeat exact (h₇ <| inter_empty_of_inter_union_empty h₃).elim
  · split_ifs at * with _ _ _ _ _ g₅ g₆ g₇
    repeat tauto
    · rw [union_inter_distrib_right,g₅,g₆]
      simp
    · simp at h₁ ⊢
      rw [union_inter_distrib_right,g₅,empty_union]
      exact h₁
    · simp at h₀
      rw [union_inter_distrib_right,g₇]
      simp only [union_empty, mem_filter, mem_univ, true_and]
      exact h₀
    · simp at h₀ h₁ ⊢
      rw [union_inter_distrib_right]
      exact union_subset h₀ h₁

/-- All the axioms (including the paradoxical B, D, E): -/
def CJ_all_2022 {α : Type*} [Fintype α] [DecidableEq α] (ob : Finset α → Finset (Finset α)) :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧ D5 ob ∧ E5 ob ∧ F5 ob ∧ G5 ob

def CJ_noE_2022 {α : Type*} [Fintype α] [DecidableEq α] (ob : Finset α → Finset (Finset α)) :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧ D5 ob ∧ F5 ob ∧ G5 ob

/-- This could also be called CJ_2022. -/
def CJ_noD_2022 {α : Type*} [Fintype α] [DecidableEq α] (ob : Finset α → Finset (Finset α)) :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧ E5 ob ∧ F5 ob ∧ G5 ob

def CJ_noDF_2022 {α : Type*} [Fintype α] [DecidableEq α] (ob : Finset α → Finset (Finset α)) :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧ E5 ob ∧ G5 ob

def CJ_noEG_2022 {α : Type*} [Fintype α] [DecidableEq α] (ob : Finset α → Finset (Finset α)) :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧ D5 ob ∧ F5 ob

theorem CJ_no_DF_canon₂_II {α : Type*} [Fintype α] [DecidableEq α] {A B : Finset α} (h : A ⊆ B) :
    CJ_noDF_2022 (canon₂_II A B) := by
  use canon₂_II_A5 _ _, canon₂_II_B5 _ _, canon₂_II_C5 _ _, canon₂_II_E5 h, canon₂_II_G5 _ _

theorem CJ_no_EG_canon₂ {α : Type*} [Fintype α] [DecidableEq α] {A B : Finset α} (h : A ⊆ B) :
    CJ_noEG_2022 (canon₂ A B) := by
  use canon₂_A5 _ _, canon₂_B5 _ _, canon₂_C5 _ _, canon₂_D5 h, canon₂_F5 _ _

theorem canon_II_F5  {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) : F5 (canon_II A) := by
    -- must prove directly since F fails for canon₂_II !
      unfold F5 canon_II
      intro _ _ _ h₀ h₁
      split_ifs at * with h₂ h₃ h₄ h₅
      repeat exact h₀
      · exact h₁
      · simp only [mem_filter, mem_univ, true_and, not_mem_empty] at h₀ h₁ ⊢
        rw [union_inter_distrib_right, union_eq_empty] at h₂
        exact h₃ h₂.1
      repeat simp at h₀
      · simp at h₁
      · simp at *;
        rw [union_inter_distrib_right,h₀,h₁,union_inter_distrib_right]

theorem CJ_noD_canon_II {α : Type*} [Fintype α] [DecidableEq α] {A : Finset α} : CJ_noD_2022 (canon_II A) := by
    rw [canon_II_symmetry]
    have := canon₂_II_A5 A A
    have := canon₂_II_B5 A A
    have := canon₂_II_C5 A A
    have := canon_II_E5 A
    have := canon_II_F5 A
    have := canon₂_II_G5 A A
    rw [canon_II_symmetry] at *
    unfold canon₂_II at *
    simp only [ite_self] at *
    repeat use (by tauto)


theorem canon_G.{u_1} {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] (A : Finset α) :
    G5 (canon A) := by
  unfold canon G5 -- can't use canon₂_G since that doesn't hold!
  intro X Y Z h₀ h₁ h₂
  simp only at *
  split_ifs at *
  any_goals (simp only [not_mem_empty] at *)
  simp only [mem_filter, mem_univ, true_and, mem_inter] at h₀ h₁ ⊢
  exact subset_inter_within h₀ h₁

theorem CJ_noE_canon {α : Type*} [Fintype α] [DecidableEq α] {A : Finset α} :
  CJ_noE_2022 (canon A) := by
    have := canon₂_A5 A A
    have := canon₂_B5 A A
    have := canon₂_C5 A A
    have := canon₂_D5 (by show A ⊆ A; trivial)
    have := canon₂_F5 A A
    have := canon_G A -- can't use canon₂_G since that doesn't hold!
    unfold canon₂ at *
    simp only [ite_self] at *
    repeat use (by tauto)

lemma coincidence {α : Type*} [Fintype α] [DecidableEq α] :
    canon (univ : Finset α) = canon_II (univ : Finset α) := by
  unfold canon canon_II;simp


/-- For any n, there is an n-world model of A5 through G5,
namely: let ob(X) be all the supersets of X, except that ob(∅)=∅. -/
theorem CJ_all_canon_univ {α : Type*} [Fintype α] [DecidableEq α] : CJ_all_2022 (canon (univ: Finset α)) := by
    have R := (@coincidence α _ _) ▸ @canon_II_E5 α _ _ univ
    have Q := @CJ_noE_canon α _ _ univ
    unfold CJ_noE_2022 at Q
    unfold CJ_all_2022
    tauto
