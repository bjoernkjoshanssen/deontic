import Deontic.Basic
import Deontic.Finset
import Deontic.Venn
import Deontic.Canonical

/-!
We verify that the Maple model from 1996 is actually a `canon₃_II` model.
Thus the definition of `canon_II` was foreshadowed in 1996;
In this example `canon_II` can be characterized as the model obtain by a certain greedy algorithm
for A5-C5 and automatically satisfies E5.
-/
open Finset

def canon₃ {α : Type*} [Fintype α] [DecidableEq α] (A B C : Finset α) :
    Finset α → Finset (Finset α) :=
  fun X ↦
      ite (X ∩ C = ∅)
      ∅
      (ite (X ∩ B = ∅)
      (filter (fun T ↦ X ∩ C ⊆ T) univ)

      (ite (X ∩ A = ∅)
      (filter (fun T ↦ X ∩ B ⊆ T) univ)

      (filter (fun T ↦ X ∩ A ⊆ T) univ)
      )
  )

def canon₃'' {α : Type*} [Fintype α] [DecidableEq α] (A B C : Finset α) :
    Finset α → Finset (Finset α) :=
  fun X ↦
      ite (X ∩ C = ∅)
      {∅}ᶜ
      (ite (X ∩ B = ∅)
      (filter (fun T ↦ X ∩ C ⊆ T) univ)

      (ite (X ∩ A = ∅)
      (filter (fun T ↦ X ∩ B ⊆ T) univ)

      (filter (fun T ↦ X ∩ A ⊆ T) univ)
      )
  )

def canon₃''' {α : Type*} [Fintype α] [DecidableEq α] (A B C : Finset α) :
    Finset α → Finset (Finset α) :=
  fun X ↦
      ite (X ∩ C = ∅)
      {T | T ≠ ∅ ∧ X ⊆ T}.toFinset
      (ite (X ∩ B = ∅)
      (filter (fun T ↦ X ∩ C ⊆ T) univ)

      (ite (X ∩ A = ∅)
      (filter (fun T ↦ X ∩ B ⊆ T) univ)

      (filter (fun T ↦ X ∩ A ⊆ T) univ)
      )
  )
  -- fun X ↦ ite (X ∩ B = ∅) ({T | T ≠ ∅ ∧ X ⊆ T}.toFinset) (
  --     ite (X ∩ A = ∅)
  --     ({T | X ∩ B ⊆ T}.toFinset)
  --     ({T | X ∩ A ⊆ T}.toFinset)
  -- )


/-- Ought (Y | Z) as in 1996 Maple code. -/
def Ought {α : Type*} [Fintype α] [DecidableEq α]
    (ob : Finset α → Finset (Finset α))
    (Y Z : Finset α) := ∀ X ⊆ Z, X ∩ Y ≠ ∅ → Y ∈ ob X

/- The next two results show that canon₂_II is the least model
 satisfying B5 and two Ought conditions.
-/

lemma not_empty_inter {α : Type*} [Fintype α] [DecidableEq α] {A B : Finset α} {i : α}
    (hA : i ∈ A) (hB : i ∈ B) : A ∩ B ≠ ∅ := by
  intro hc
  have : i ∈ A ∩ B := by simp;tauto
  rw [hc] at this
  simp at this

/--

Limited Principle of Explosion:
If `C` is at least somewhat desirable
and the most desirable (`A`) is violated then `C` is obligatory.
-/
theorem paradox_in_CJ2022_general'' {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (e5 : E5 ob) (f5 : F5 ob) {A B C D : Finset (Fin n)}
    (hC : C ≠ ∅) (hab : A ∩ B = ∅) (hbc : B ∩ C = ∅)
    (hAD : A ∩ D = ∅)
    (hf₁₀ : A ∈ ob (A ∪ B)) (hf₀₀ : C ∈ ob (C ∪ D)) : C ∈ ob (B ∪ C ∪ D) := by
  have hf₀ : A ∪ C ∈ ob (C ∪ D) := b5 (C ∪ D) C (A ∪ C)
    (by
      ext i
      simp
      intro h₀ h₁
      cases h₀ with
      | inl h => tauto
      | inr h =>
        have := not_empty_inter h₁ h
        tauto) hf₀₀
  have hf₁ : A ∪ C ∈ ob (A ∪ B) := by -- yes
    apply b5 _ A _
    ext i
    simp
    intro h₀ h₁
    cases h₀ with
    | inl h => exact h
    | inr h => exact False.elim $ not_empty_inter h h₁ hbc
    exact hf₁₀
  have hf : A ∪ C ∈ ob ((A ∪ B) ∪ C ∪ D) := by -- yes
    convert f5 _ _ _ hf₀ hf₁ using 2
    ext i
    simp
    tauto
  have he : A ∪ C ∈ ob (B ∪ C ∪ D) := e5 _ _ _
    (by intro;simp;tauto) hf (by
      contrapose! hC
      exact subset_empty.mp $ hC ▸ (by intro i hi; simp; tauto))
  exact b5 _ _ _ (by
      ext i
      simp
      intro h₀ h₁
      cases h₀ with
      | inl h =>
        have := not_empty_inter h₁ h
        tauto
      | inr h =>
        cases h with
        | inl h => tauto
        | inr h =>
          have := not_empty_inter h₁ h
          tauto) he


/-
where U = A ∪ B
      V = C ∪ D
-/
theorem limited_explosion {n : ℕ} {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (e5 : E5 ob) (f5 : F5 ob) {A C U V : Finset (Fin n)}
    (h₀ : A ∈ ob U)
    (h₁ : C ∈ ob V)
    (h₂ : C ≠ ∅)
    (h₃ : C ∩ U = ∅)
    (h₄ : A ∩ V = ∅)
    (h₅ : A ⊆ U)
    (h₆ : C ⊆ V) :
    C ∈ ob ((U \ A) ∪ V) := by
  have := @paradox_in_CJ2022_general'' n ob b5 e5 f5
    A (U \ A) C (V \ C) h₂ (by ext;simp) (by
      ext i;simp
      intro hi₀ _ hi₂
      exact not_empty_inter hi₂ hi₀ h₃) (by
      ext i;simp
      intro hi₀ hi₁
      exact False.elim $ not_empty_inter hi₀ hi₁ h₄) (by convert h₀ using 2;ext;simp;apply h₅)
      (by convert h₁ using 2;ext;simp;apply h₆)
  convert this using 2
  ext i;simp
  aesop


  -- Use B5 twice and then F5 on the results, then E5 on that and finally B5 again.
theorem paradox_in_CJ2022_general' {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (e5 : E5 ob) (f5 : F5 ob) {A B C : Finset (Fin n)}
    (hC : C ≠ ∅) (hab : A ∩ B = ∅) (hbc : B ∩ C = ∅)
    (hf₁₀ : A ∈ ob (A ∪ B)) (hf₀₀ : C ∈ ob C) : C ∈ ob (B ∪ C) := by
  have hf₀ : A ∪ C ∈ ob C := b5 C C (A ∪ C) (by simp) hf₀₀
  have hf₁ : A ∪ C ∈ ob (A ∪ B) := by -- yes
    apply b5 _ A _
    ext i
    simp
    intro h₀ h₁
    cases h₀ with
    | inl h => exact h
    | inr h => exact False.elim $ not_empty_inter h h₁ hbc
    exact hf₁₀
  have hf : A ∪ C ∈ ob ((A ∪ B) ∪ C) := by -- yes
    convert f5 _ _ _ hf₀ hf₁ using 2
    ext i
    simp
    tauto
  have he : A ∪ C ∈ ob (B ∪ C) := e5 _ _ _
    (by intro;simp;tauto) hf (by
      contrapose! hC
      exact subset_empty.mp $ hC ▸ (by intro i hi; simp; tauto))
  exact b5 _ _ _ (by
      ext i
      simp
      constructor
      · intro h
        by_contra H
        simp_all
        exact False.elim $ not_empty_inter h.1 h.2 hab
      · intro hi
        constructor <;> tauto) he


theorem paradox_in_CJ2022_general {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (e5 : E5 ob) (f5 : F5 ob) {A B C T : Finset (Fin n)}
    (hA : A ≠ ∅) (hC : C ≠ ∅) (hac : A ∩ C = ∅) -- T = took the test
    (hab : A ∩ B = ∅) (hbc : B ∩ C = ∅)
    (hAT : A ⊆ T)
    (hBT : B ⊆ T)
    (hCT : C ⊆ T)
    (ought₀ : Ought ob A T)

    (ought₂ : Ought ob C (T  ∩ (A ∪ B)ᶜ)) :
    C ∈ ob (B ∪ C) := by
  have h₀ : A ∈ ob (A ∪ B) := ought₀ (A ∪ B) (by intro;simp;tauto) (by simp;exact hA)
  have h₁ : A ∪ C ∈ ob (A ∪ B) := by
    apply b5
    show A ∩ _ = _
    ext i;
    simp
    intro h₀ h₁
    cases h₀ with
    | inl h => tauto
    | inr h =>
      exfalso
      have : i ∈ B ∩ C := by simp;tauto
      rw [hbc] at this
      simp at this
    exact h₀
  have h₂ : C ∈ ob C := ought₂ C (by
    intro i hi
    simp
    constructor
    exact hCT hi
    constructor
    intro hc
    have : i ∈ A ∩ C := by simp;tauto
    rw [hac] at this
    simp at this
    intro hc

    have : i ∈ B ∩ C := by simp;tauto
    rw [hbc] at this
    simp at this) (by simp; exact hC)
  have h₃ : A ∪ C ∈ ob C := b5 C C (A ∪ C) (by simp) h₂
  have h₄ : A ∪ C ∈ ob ((A ∪ B) ∪ C) := by
    convert f5 (A ∪ C) C (A ∪ B) h₃ (by tauto) using 2
    ext i
    simp
    tauto
  have h₅ : A ∪ C ∈ ob (B ∪ C) := e5 ((A ∪ B) ∪ C) (B ∪ C) (A ∪ C) (by intro;simp;tauto)
      h₄ (by
        simp
        intro hc
        have : C ⊆ (B ∪ C) ∩ ((A ∪ C) : Finset (Fin n)) := by
          intro i hi
          simp
          constructor <;> (right; exact hi)
        rw [hc] at this
        simp at this
        exact hC this
        )
  have h₆ : C ∈ ob (B ∪ C) := b5 (B ∪ C) (A ∪ C) C (by
      ext i
      simp
      constructor
      intro h
      by_contra H
      simp_all
      have : i ∈ A ∩ B := by simp;tauto
      rw [hab] at this
      simp at this
      intro hi
      constructor <;> tauto) h₅
  exact e5 (B ∪ C) (B ∪ C) C (by simp) h₆ (by simp;exact hC)


theorem paradox_in_CJ2022_generalest {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (e5 : E5 ob) (f5 : F5 ob) {A B C : Finset (Fin n)}
    (hA : A ≠ ∅) (hC : C ≠ ∅) (hac : A ∩ C = ∅)
    (hab : A ∩ B = ∅) (hbc : B ∩ C = ∅)
    (ought₀ : Ought ob A univ)
    (ought₂ : Ought ob C (A ∪ B)ᶜ) :
    C ∈ ob (B ∪ C) := by
  have h₀ : A ∈ ob (A ∪ B) := ought₀ (A ∪ B) (by simp) (by simp;exact hA)
  have h₁ : A ∪ C ∈ ob (A ∪ B) := by
    apply b5
    show A ∩ _ = _
    ext i;
    simp
    intro h₀ h₁
    cases h₀ with
    | inl h => tauto
    | inr h =>
      exfalso
      have : i ∈ B ∩ C := by simp;tauto
      rw [hbc] at this
      simp at this
    exact h₀
  have h₂ : C ∈ ob C := ought₂ C (by
    intro i hi
    simp
    constructor
    intro hc
    have : i ∈ A ∩ C := by simp;tauto
    rw [hac] at this
    simp at this
    intro hc

    have : i ∈ B ∩ C := by simp;tauto
    rw [hbc] at this
    simp at this) (by simp; exact hC)
  have h₃ : A ∪ C ∈ ob C := b5 C C (A ∪ C) (by simp) h₂
  have h₄ : A ∪ C ∈ ob ((A ∪ B) ∪ C) := by
    convert f5 (A ∪ C) C (A ∪ B) h₃ (by tauto) using 2
    ext i
    simp
    tauto
  have h₅ : A ∪ C ∈ ob (B ∪ C) := e5 ((A ∪ B) ∪ C) (B ∪ C) (A ∪ C) (by intro;simp;tauto)
      h₄ (by
        simp
        intro hc
        have : C ⊆ (B ∪ C) ∩ ((A ∪ C) : Finset (Fin n)) := by
          intro i hi
          simp
          constructor <;> (right; exact hi)
        rw [hc] at this
        simp at this
        exact hC this
        )
  have h₆ : C ∈ ob (B ∪ C) := b5 (B ∪ C) (A ∪ C) C (by
      ext i
      simp
      constructor
      intro h
      by_contra H
      simp_all
      have : i ∈ A ∩ B := by simp;tauto
      rw [hab] at this
      simp at this
      intro hi
      constructor <;> tauto) h₅
  exact e5 (B ∪ C) (B ∪ C) C (by simp) h₆ (by simp;exact hC)


/--
This is paradoxical if a is the best world, then b, then c.
-/
theorem paradox_in_CJ2022 {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (e5 : E5 ob) (f5 : F5 ob)
    (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ought₀ : Ought ob {a} univ)
    (ought₂ : Ought ob {c} {a,b}ᶜ) :
    {c} ∈ ob {b,c} := by
  apply paradox_in_CJ2022_generalest (C := {c}) (A := {a}) (B := {b})
  tauto
  tauto
  tauto
  simp
  exact singleton_ne_empty c
  aesop
  aesop
  aesop
  tauto
  tauto

/-

We could consider also imposing G5:
  ∀ (X Y Z : Finset U), Y ∈ ob X → Z ∈ ob Y →
    X ∩ Y ∩ Z ≠ ∅ → Y ∩ Z ∈ ob X
but it will only add ob-members.

The good thing is that this Maple minimal-model
methodology can be used for any future axiom systems
as well to guard against unintended consequences.

The minimal model of B5 D5 F5 (with E5 excluded) is canon₂.
So we have surprising characterizations of both canon₂
and canon₂_II in terms of
{B,D,F} and {B} respectively.
Maybe should be called canonBDF, canonB.

-/
theorem characterize_canon₂_II₀ {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α)
  (hAB : A ⊆ B):
  Ought (canon₂_II A B) A univ ∧ Ought (canon₂_II A B) B Aᶜ := by
  constructor
  · intro X _ h₀
    unfold canon₂_II
    rw [if_neg h₀]
    have H : X ∩ B ≠ ∅ := by
      contrapose! h₀
      apply subset_empty.mp
      apply subset_trans
      show X ∩ A ⊆ X ∩ B
      exact inter_subset_inter (fun ⦃a⦄ a ↦ a) hAB
      rw [h₀]
    rw [if_neg H]
    simp
  · intro X h₁ h₀
    unfold canon₂_II
    rw [if_neg h₀]
    have : X ∩ A = ∅ := by
      ext i
      simp
      intro hi
      have := h₁ hi
      simp at this ⊢
      tauto
    rw [this]
    simp


theorem characterize_canon₂₀ {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α)
  (hAB : A ⊆ B):
  Ought (canon₂ A B) A univ ∧ Ought (canon₂ A B) B Aᶜ := by
  constructor
  · intro X _ h₀
    unfold canon₂
    rw [if_neg h₀]
    have H : X ∩ B ≠ ∅ := by
      contrapose! h₀
      apply subset_empty.mp
      apply subset_trans
      show X ∩ A ⊆ X ∩ B
      exact inter_subset_inter (fun ⦃a⦄ a ↦ a) hAB
      rw [h₀]
    rw [if_neg H]
    simp
  · intro X h₁ h₀
    unfold canon₂
    rw [if_neg h₀]
    have : X ∩ A = ∅ := by
      ext i
      simp
      intro hi
      have := h₁ hi
      simp at this ⊢
      tauto
    rw [this]
    simp

-- Taste Tea definitions
-- def Ought {α : Type*} [Fintype α] [DecidableEq α]
--     (ob : Finset α → Finset (Finset α))
--     (Y Z : Finset α) := ∀ X ⊆ Z, X ∩ Y ≠ ∅ → Y ∈ ob X
--      A univ
--      B Aᶜ

-- inductive oblig (A B : Set ℕ) : Set (Set ℕ × Set ℕ)
-- | basic₁ {X} : X ⊆ Set.univ → X ∩ A ≠ ∅ → oblig A B (A, X) -- Ought (A | univ)
-- | basic₂ {X} : X ⊆ Aᶜ       → X ∩ B ≠ ∅ → oblig A B (B, X) -- Ought (B | Aᶜ)
-- | B5 {X Y} : oblig A B (X, Y) → oblig A B (X ∩ Y, Y)


-- | C5 {X Y Z} : CJ_closure ob₀ (Y,X) → CJ_closure ob₀ (Z,X) → CJ_closure ob₀ (Y ∩ Z,X)
-- | D5 {X Y Z} : Y ⊆ X → CJ_closure ob₀ (Y, X) → X ⊆ Z → CJ_closure ob₀ (((Z \ X) ∪ Y), Z )
-- | E5 {X Y Z} : Y ⊆ X → CJ_closure ob₀ (Z, X) → Y ∩ Z ≠ ∅ → CJ_closure ob₀ (Z, Y)


-- inductive CJ_closure (ob₀ : Set (Set ℕ × Set ℕ)) : Set (Set ℕ × Set ℕ)
-- | basic {s} : s ∈ ob₀ → CJ_closure ob₀ s
-- | B5 {X Y} : CJ_closure ob₀ (X, Y) → CJ_closure ob₀ (X ∩ Y, Y)
-- | C5 {X Y Z} : CJ_closure ob₀ (Y,X) → CJ_closure ob₀ (Z,X) → CJ_closure ob₀ (Y ∩ Z,X)
-- | D5 {X Y Z} : Y ⊆ X → CJ_closure ob₀ (Y, X) → X ⊆ Z → CJ_closure ob₀ (((Z \ X) ∪ Y), Z )
-- | E5 {X Y Z} : Y ⊆ X → CJ_closure ob₀ (Z, X) → Y ∩ Z ≠ ∅ → CJ_closure ob₀ (Z, Y)

-- inductive CJ_closure' {n : ℕ} (ob₀ : Set (Fin n) → Set (Set (Fin n))) : Set (Fin n) → Set (Set (Fin n))
-- | basic {X Y} : X ∈ ob₀ Y → CJ_closure' ob₀ Y X

-- inductive UnionClos {α : Type*} (𝒜 : Set (Set α)) : Set (Set α)
-- | basic {s} : s ∈ 𝒜 → UnionClos 𝒜 s
-- | union {s t} : UnionClos 𝒜 s → UnionClos 𝒜 s → UnionClos 𝒜 (s ∪ t)
-- example : UnionClos { (∅ : Set ℕ)} = (({ (∅ : Set ℕ)}) : Set (Set (ℕ))) := by
--   sorry

inductive Ob_chisholm_b {n : ℕ} (A B : Finset (Fin n)) : Set ((Finset (Fin n)) × Finset (Fin n))
| basic₁ {X} : X ⊆ univ → X ∩ A ≠ ∅ → Ob_chisholm_b A B (A, X) -- Ought (A | univ)
| basic₂ {X} : X ⊆ Aᶜ   → X ∩ B ≠ ∅ → Ob_chisholm_b A B (B, X) -- Ought (B | Aᶜ)
| B5 {X Y Z} : Ob_chisholm_b A B (X, Y) → X ∩ Y = Z ∩ Y → Ob_chisholm_b A B (Z, Y)

inductive Ob_chisholm_bdf {n : ℕ} (A B : Finset (Fin n)) : Set ((Finset (Fin n)) × Finset (Fin n))
| basic₁ {X} : X ⊆ univ → X ∩ A ≠ ∅ → Ob_chisholm_bdf A B (A, X) -- Ought (A | univ)
| basic₂ {X} : X ⊆ Aᶜ   → X ∩ B ≠ ∅ → Ob_chisholm_bdf A B (B, X) -- Ought (B | Aᶜ)
| B5 {X Y Z} : Ob_chisholm_bdf A B (X, Y) → X ∩ Y = Z ∩ Y → Ob_chisholm_bdf A B (Z, Y)
| D5 {X Y Z} : Y ⊆ X → Ob_chisholm_bdf A B (Y, X) → X ⊆ Z → Ob_chisholm_bdf A B (((Z \ X) ∪ Y), Z )
| F5 {X Y Z} : Ob_chisholm_bdf A B (X, Y) → Ob_chisholm_bdf A B (X, Z) → Ob_chisholm_bdf A B (X, Y ∪ Z)

-- legg til D of F

open Classical
noncomputable def ob_chisholm_b {n : ℕ} (A B : Finset (Fin n)) :
  Finset (Fin n) → Finset (Finset (Fin n)) := fun Y => {X | (X,Y) ∈ Ob_chisholm_b A B}

noncomputable def ob_chisholm_bdf {n : ℕ} (A B : Finset (Fin n)) :
  Finset (Fin n) → Finset (Finset (Fin n)) := fun Y => {X | (X,Y) ∈ Ob_chisholm_bdf A B}

/-- Theorem 2 in the first version of the paper. -/
theorem characterize_canon₂_II {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α)
  (ob : Finset α → Finset (Finset α)) (b5 : B5 ob)
  (ought : Ought ob A univ ∧ Ought ob B Aᶜ) : ∀ X, canon₂_II A B X ⊆ ob X := by
  intro X Y h
  unfold canon₂_II at h
  by_cases H₀ : X ∩ B = ∅
  · rw [H₀] at h
    simp at h
  · rw [if_neg H₀] at h
    by_cases H₁ : X ∩ A = ∅
    · rw [H₁] at h
      simp at h
      nth_rewrite 1 [inter_comm] at h
      nth_rewrite 2 [inter_comm] at h
      apply b5
      exact h
      unfold Ought at ought
      apply ought.2
      refine sdiff_eq_empty_iff_subset.mp ?_
      simp
      exact H₁
      exact H₀
    · rw [if_neg H₁] at h
      simp at h
      apply b5
      nth_rewrite 1 [inter_comm] at h
      nth_rewrite 2 [inter_comm] at h
      exact h
      unfold Ought at ought
      apply ought.1
      simp
      tauto

/-- Note that if `ob` depends on some parameters `A, B, ...` then
so can the `axioms`.
-/
def least_model {α : Type*} [Fintype α] [DecidableEq α]
  (ob : Finset α → Finset (Finset α))
  (axioms : (Finset α → Finset (Finset α)) → Prop) :=
  axioms ob ∧ ∀ ob', axioms ob' → ∀ X, ob X ⊆ ob' X

recall infinitely_many_adequate
/-- Since canon₂_II also satisfies
A B C E G
we can furthermore characterize it as the least model of those axioms and B5
and these Oughts.
It is remarkable that A, C, E, G do not add anything to this least model.

            least model of  also of
canon₂_II   A B C E G       B
canon₂      A B C D         B D F

What are the least models of the paradoxical ABCDEFG and ABCEFG?

-/

lemma ought_complement {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) (ob : Finset α → Finset (Finset α)) :
     Ought ob A Aᶜ := by
  intro X h₀ h₁
  exfalso
  apply h₁
  ext i
  simp
  intro h
  have := h₀ h
  convert this
  simp

theorem least_model_canon₂_II {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (h : A ⊆ B) :
    least_model (canon₂_II A B)
    (fun ob => B5 ob ∧ Ought ob A univ ∧ Ought ob B Aᶜ) := by
  have := characterize_canon₂_II₀ A B h
  constructor
  · simp
    constructor
    · exact canon₂_II_B5 A B
    · exact characterize_canon₂_II₀ A B h
  · intro ob h₀
    exact characterize_canon₂_II A B ob h₀.1 h₀.2

/-- We need to assume `A ⊆ B`, perhaps relevant to referee's question,
although it was already in `least_model_canon₂_II`.
The contribution of this theorem is to obtain canon₂_II as *equal* to a certain closure,
not just satisfying a "least model" *predicate*.
January 5, 2026.
-/
theorem canon₂_II_eq_ob_chisholm_b {n : ℕ} (A B : Finset (Fin n)) (h : A ⊆ B):
canon₂_II A B = ob_chisholm_b A B := by
  ext Y X
  simp [ob_chisholm_b]
  constructor
  · intro h
    have := @characterize_canon₂_II (Fin n) _ _ A B (ob_chisholm_b A B)
      (by
      clear h X Y
      intro X Y Z h₀ h₁
      simp [ob_chisholm_b] at h₁ ⊢
      exact @Ob_chisholm_b.B5 (X := Y) (Y := X) n A B Z h₁ h₀) (by
      constructor
      · intro X hu h₀
        simp [ob_chisholm_b]
        apply Ob_chisholm_b.basic₁ _ h₀
        exact hu
      · intro X hu h₀
        simp [ob_chisholm_b]
        apply Ob_chisholm_b.basic₂ _ h₀
        exact hu
      ) Y _ h
    unfold ob_chisholm_b at this
    simp at this
    exact this
  · intro h
    set a := (X,Y)
    show a.1 ∈ canon₂_II A B a.2
    apply Ob_chisholm_b.rec (motive := fun a ha => a.1 ∈ canon₂_II A B a.2)
      (A := A) (B := B) -- whoa!
    · clear h a X
      have := @least_model_canon₂_II (Fin n) _ _ A B h
      simp [least_model] at this
      have := this.1.2.1
      unfold Ought at this
      simp
      intro X h₀
      exact this X (by simp) h₀
    · clear h a X
      have := @least_model_canon₂_II (Fin n) _ _ A B h
      simp [least_model] at this
      have := this.1.2.2
      unfold Ought at this
      simp
      intro X h₀
      exact this X h₀

    · clear h a X
      have := @least_model_canon₂_II (Fin n) _ _ A B h
      simp [least_model] at this
      intro X Y Z h h₀ h₁
      exact this.1.1 Y X Z h₀ h₁
    · exact h





/- `canon_II A` is the least model of ABCEFG + ¬ CX + Ought(A | univ).
Not really worth proving.
-/
-- theorem least_model_adequate {α : Type*} [Fintype α] [DecidableEq α]
--     (A : Finset α) :
--     least_model (canon_II A)
--     (fun ob => A5 ob ∧ B5 ob ∧ C5 ob ∧ E5 ob ∧ F5 ob ∧ G5 ob ∧ Ought ob A univ) := by
--     sorry

lemma characterize_canon₂_case {α : Type*} [Fintype α] [DecidableEq α] {A B X Y : Finset α}
    {ob : Finset α → Finset (Finset α)} (b5 : B5 ob) (d5 : D5 ob) (f5 : F5 ob)
    (H₀ : ¬X ∩ B = ∅) (H₁ : X ∩ A = ∅)
    (ought : Ought ob B Aᶜ) (h : X ∩ B ⊆ Y) : Y ∈ ob X := by
  have hXA : X ⊆ Aᶜ := sdiff_eq_empty_iff_subset.mp (by
    convert H₁ using 1
    simp)
  have h₂ : B ∈ ob (X ∩ B) := ought (X ∩ B)
    (subset_trans (b := X) (by simp) hXA) (by simp; tauto)
  have d₁ : X ∩ B ∈ ob (X ∩ B) := b5 (X ∩ B) B _ (by simp) (by tauto)
  have h₄ : X ∩ Y ∈ ob (X ∩ Y) := by
    convert d5 (X ∩ B) (X ∩ B) (X ∩ Y)
      (by simp) d₁ (subset_inter (by simp) h) using 1
    simp
    exact subset_inter (by simp) h
  have hj : B ∈ ob (X \ Y ∪ X ∩ B) := by
    apply ought
    · apply union_subset
      all_goals (exact subset_trans (b := X) (by simp) hXA)
    · contrapose! H₀
      rw [← H₀, union_inter_distrib_right]
      simp
      apply subset_inter
      rw [sdiff_eq]
      all_goals simp
  have june6₁ : X ∩ Y ∈ ob ((X \ Y) ∪ (X ∩ B)) := by
    apply b5 ((X \ Y) ∪ (X ∩ B)) (X ∩ B) (X ∩ Y)
    ext i;simp
    · intro hi
      constructor
      · intro hi'
        constructor
        · apply h
          simp;tauto
        · tauto
      · tauto
    · exact b5 ((X \ Y) ∪ (X ∩ B)) B (X ∩ B) (by ext;simp;tauto) hj
  have : X ∩ Y ∈ ob X := by
    have := f5 (X ∩ Y) (X ∩ Y) ((X \ Y) ∪ (X ∩ B)) h₄ june6₁
    convert this using 2
    ext;simp;tauto
  apply b5 (Y := X ∩ Y)
  · simp
  · tauto

theorem BD5_of_B5_of_D5 {α : Type*} [Fintype α] [DecidableEq α]
    {ob : Finset α → Finset (Finset α)}
    (b5 : B5 ob) (d5 : D5 ob) : BD5 ob := by
        intro X Y Z h h₀
        have sets_eq : ((Z \ X) ∪ (Y ∩ X)) ∩ Z = ((Z \ X) ∪ Y) ∩ Z := by
            ext
            simp
            tauto
        have input2 : Y ∩ X ∈ ob X := b5 X Y (Y ∩ X) (by simp) h
        have := d5 X (Y ∩ X) Z inter_subset_right input2 h₀
        suffices  (Z \ X ∪ Y) ∩ Z ∈ ob Z by
            exact b5 Z ((Z \ X ∪ Y) ∩ Z) ((Z \ X ∪ Y)) (by simp) this
        rw [← sets_eq]
        exact b5 Z ((Z \ X ∪ Y ∩ X)) ((Z \ X ∪ Y ∩ X) ∩ Z) (by simp)
            this

theorem II_2_2_finset  {α : Type*} [Fintype α] [DecidableEq α]
    {ob : Finset α → Finset (Finset α)}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5 ob) (d5 : D5 ob) :
    F5 ob := by
  intro X Y Z h₀ h₁
  unfold C5 at c5
  suffices ((Y ∪ Z) \ Y ∪ X) ∩ ((Y ∪ Z) \ Z ∪ X) ∈ ob (Y ∪ Z) by
    convert this using 2
    ext;simp;tauto
  have bd5 : BD5 ob := BD5_of_B5_of_D5 b5 d5
  apply c5
  · apply bd5 Y X (Y ∪ Z) h₀
    simp
  · apply bd5
    exact h₁
    simp
  · simp
    have : X ∩ Y ≠ ∅ := by
        have : X ∩ Y ∈ ob Y := b5 Y X (X ∩ Y) (by simp) h₀
        intro hc
        rw [hc] at this
        exact a5 _ this
    contrapose! this
    have : (Y ∪ Z) ∩ X = ∅ := by
        convert this using 1
        ext;simp;tauto
    apply subset_empty.mp
    rw [← this]
    intro;simp;tauto

/-- canon₂ is the minimal model satisfying certain Ought's
and B5, D5, F5.
Actually F5 follows from B5, C5, D5, A5 (Lemma II-2-2)
although here we do not need to assume C5.

June 6, 2025
-/
lemma characterize_canon₂ {α : Type*} [Fintype α] [DecidableEq α]
  {A B : Finset α} {ob : Finset α → Finset (Finset α)}
  (b5 : B5 ob) (d5 : D5 ob) (f5 : F5 ob)
  (ought : Ought ob A univ ∧ Ought ob B Aᶜ) : ∀ X, canon₂ A B X ⊆ ob X := by
  intro X Y h
  unfold canon₂ at h
  by_cases H₀ : X ∩ B = ∅
  · rw [H₀] at h; simp at h
  · rw [if_neg H₀] at h
    by_cases H₁ : X ∩ A = ∅
    · rw [H₁] at h; simp at h
      apply characterize_canon₂_case <;> tauto
    · -- the same but with A instead of B
      rw [if_neg H₁] at h; simp at h
      exact characterize_canon₂_case (A := ∅) b5 d5 f5 H₁ (by simp)
        (by convert ought.1;simp) h

theorem least_model_canon₂ {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (h : A ⊆ B) :
    least_model (canon₂ A B)
    (fun ob => B5 ob ∧ D5 ob ∧ F5 ob ∧ Ought ob A univ ∧ Ought ob B Aᶜ) :=
  ⟨
    ⟨canon₂_B5 A B, canon₂_D5 h, canon₂_F5 A B, characterize_canon₂₀ A B h⟩,
    fun _ h₀ => characterize_canon₂ h₀.1 h₀.2.1 h₀.2.2.1 h₀.2.2.2⟩

structure Rule (α : Type*) where
(params : Type*)
(ι : Type*)                      -- indices of premises
(premise_set : params → ι → Set α)
(conclusion : params → Set α)

inductive Closure {α : Type*} (𝒜 : Set (Set α))
  {R : Type*} (rule : R → Rule α) :
  Set α → Prop
| basic {s} : s ∈ 𝒜 → Closure 𝒜 rule s
| apply (r : R) (p : (rule r).params) :
    (∀ i : (rule r).ι, Closure 𝒜 rule ((rule r).premise_set p i)) →
    Closure 𝒜 rule ((rule r).conclusion p)

/-!
# General setup for CJ rules
 -/

structure sets_instance (α : Type*) (n : ℕ) (P : (Fin n → Finset α) → Prop) where
(s : Fin n → Finset α)
(h : P s)

structure closure_rule (α : Type*) where
(numSets num_in : ℕ)
(P : (Fin numSets → Finset α) → Prop)
(premises : sets_instance α numSets P → Fin num_in → (Finset α × Finset α))
(conclusion : sets_instance α numSets P → (Finset α × Finset α))

inductive closure_under {α : Type*} (𝒜 : Finset (Finset α × Finset α))
  (rule : Finset (closure_rule α)) :
  Set (Finset α × Finset α)
| basic {s} : s ∈ 𝒜 → closure_under 𝒜 rule s
| apply (r : closure_rule α) (hr : r ∈ rule)
  (sets : sets_instance α (r.numSets) r.P )
    (h : ∀ i, closure_under 𝒜 rule (r.premises sets i)) :
              closure_under 𝒜 rule (r.conclusion sets)

/-- If we add more rules then the closure becomes larger. -/
-- January 6, 2026
lemma closure_under_sub {α : Type*} (𝒜 : Finset (Finset α × Finset α))
  (rules₁ rules₂ : Finset (closure_rule α)) (h : rules₁ ⊆ rules₂) :
  closure_under 𝒜 rules₁ ⊆ closure_under 𝒜 rules₂ :=
  @closure_under.rec α 𝒜 rules₁
    (motive := fun a _ => closure_under 𝒜 rules₂ a)
    (@closure_under.basic α 𝒜 rules₂)
    (fun r hr sets _ => @closure_under.apply α 𝒜 rules₂ r (h hr) sets)


--  ∀ (X Y Z : Finset U), (Y ∩ X = Z ∩ X) → (Y ∈ ob X → Z ∈ ob X)
def B5rule (n : ℕ) : closure_rule (Fin n) := {
      numSets := 3,
      num_in := 1,
      P := fun X => X 1 ∩ X 0 = X 2 ∩ X 0,
      premises := fun X _ ↦ (X.s 1, X.s 0),
      conclusion := fun X => (X.s 2, X.s 0)}

def ObArule {n : ℕ} (A : Finset (Fin n)) : closure_rule (Fin n) := {
      numSets := 1,
      num_in := 0,
      P := fun X => X 0 ∩ A ≠ ∅,
      premises := fun _ i ↦ (not_lt_zero i.2).elim
      conclusion := fun X => (A, X.s 0)}

def ObBArule {n : ℕ} (A B : Finset (Fin n)) : closure_rule (Fin n) := {
      numSets := 1,
      num_in := 0,
      P := fun X => X 0 ⊆ Aᶜ ∧ X 0 ∩ B ≠ ∅, --(Y Z : Finset α) := ∀ X ⊆ Aᶜ, X ∩ B ≠ ∅ → B ∈ ob X
      premises := fun _ i ↦ (not_lt_zero i.2).elim
      conclusion := fun X => (B, X.s 0)}

example (P : Fin 0 → Prop) : ∀ i, P i := by exact fun i ↦ Fin.elim0 i

/-- This shows, together with earlier results,
how to express canon₂_II as a closure under a set of operators. -/
lemma close_under_eq_ob_chisholm_b {n : ℕ} (A B : Finset (Fin n)) :
    closure_under ∅ {B5rule n, ObArule A, ObBArule A B} =
    {p | p.1 ∈ ob_chisholm_b A B p.2} := by
  ext p
  simp
  constructor
  · exact @closure_under.rec _ _ _
      (motive := fun p _ =>  p.1 ∈ ob_chisholm_b _ _ p.2)
      (by simp)
      (fun r hr ins hins ho => by
        simp [ob_chisholm_b] at hr ⊢
        cases hr with
        | inl h =>
          subst h
          simp [ob_chisholm_b] at ho
          change ∀ (_ : Fin 1), _ at ho
          exact Ob_chisholm_b.B5 (ho 0) ins.h -- ins.2 also works
        | inr h =>
          rcases h with (h | h)
          all_goals subst h
          exact Ob_chisholm_b.basic₁ (subset_univ _) ins.2
          exact Ob_chisholm_b.basic₂ ins.2.1 ins.2.2) _
  · intro h
    unfold ob_chisholm_b at h
    simp at h
    exact @Ob_chisholm_b.rec _ _ _
      (fun p _ => closure_under _ _ p)
      (fun {X} hu hA => closure_under.apply (ObArule A)
        (by simp) ({s := fun z => X, h := hA})
        (fun z => Fin.elim0 z))
      (fun {X} h₀ h₁ => closure_under.apply (ObBArule A B)
          (by simp) {s := fun _ => X, h := ⟨h₀,h₁⟩} fun z => Fin.elim0 z)
      (fun {X} {Y} {Z} h₀ h₁ h₂ => closure_under.apply (B5rule n)
        (by simp) {s := ![Y,X,Z], h := h₁} fun _ => h₂) p h

/-- The closure of a set under some operations can be defined
in a very noneffective way as the intersection of all closed sets.
Second, it can be defined in a recursively enumerable way in terms of
being generated by some operations. Sometimes, it can be characterized
even more concretely in a quantifier-free way, like here.
For example, in a vector space over F_2 the subspace generated by `v`
is just `{v,0}`.
 -/
lemma close_under_eq_canon₂_II {n : ℕ} (A B Y : Finset (Fin n)) (h : A ⊆ B) :
    canon₂_II A B Y =
    {X | (X,Y) ∈ closure_under ∅ {B5rule n, ObArule A, ObBArule A B}} := by
  have : {(X,Y) | (X,Y) ∈  closure_under ∅ {B5rule n, ObArule A, ObBArule A B}} =
    {p | p.1 ∈ canon₂_II A B p.2} := by
    rw [canon₂_II_eq_ob_chisholm_b ]
    exact close_under_eq_ob_chisholm_b A B
    exact h
  ext X
  simp at this
  rw [this]
  simp

lemma closure_under_empty {n : ℕ} :
  closure_under ∅ ∅ = (∅ : Set (Finset (Fin n) × Finset (Fin n))) := by
  ext X
  constructor
  · intro h
    exfalso
    exact @closure_under.rec (Fin n) ∅ ∅ (motive := fun _ _ => False)
      (by simp) (by simp) X h
  · intro h
    simp at h



example {n : ℕ} (A B : Finset (Fin n)) :
  closure_under ∅ {B5rule n, ObArule A, ObBArule A B} =
  closure_under ∅ {B5rule n, ObBArule A B, ObArule A} := by
  apply congrArg
  compare


-- the num_in are how many things (like Z \ X ∪ Y, X ∩ Y)
-- are assumed to be in ob
-- the numSets is how many sets (X,Y,Z) are considered.


structure DisjointUnionParams (α : Type*) where
(s : Fin 2 → Set α)
(h : Disjoint (s 0) (s 1))

def disjointUnionRule (α : Type*) : Rule α :=
{ params := DisjointUnionParams α,
  ι := Fin 2,
  premise_set := DisjointUnionParams.s,
  conclusion := fun p => p.s 0 ∪ p.s 1}
example : Closure {(∅ : Set ℕ)}
  (fun _ : Fin 1 => disjointUnionRule ℕ)
  = ({(∅ : Set ℕ)} : Set (Set (ℕ))) := by
  ext A
  constructor
  · intro h
    show A = ∅
    have := @Closure.rec ℕ {∅} (Fin 1) (fun i : Fin 1 ↦ disjointUnionRule ℕ)
      (motive := fun a t => a = ∅)
    apply this
    · simp
    · intro i p h₀ h₁
      simp [disjointUnionRule] at h₁ ⊢
      exact h₁
    · exact h
  · exact Closure.basic


theorem canon₂_eq_ob_chisholm_bdf {n : ℕ} (A B : Finset (Fin n)) (h : A ⊆ B):
canon₂ A B = ob_chisholm_bdf A B := by
  ext Y X
  simp [ob_chisholm_bdf]
  constructor
  · intro h
    have := @characterize_canon₂ (Fin n) _ _ A B (ob_chisholm_bdf A B)
      (by
      clear h X Y
      intro X Y Z h₀ h₁
      simp [ob_chisholm_bdf] at h₁ ⊢
      apply @Ob_chisholm_bdf.B5 (X := Y) (Y := X) n A B Z h₁ h₀)

      (by
        unfold ob_chisholm_bdf
        intro X Y Z h₀ h₁ h₂
        simp at h₁ ⊢
        apply @Ob_chisholm_bdf.D5
        exact h₀
        exact h₁
        exact h₂
      )
      (by
        unfold ob_chisholm_bdf
        intro X Y Z h₀ h₁
        simp at h₀ h₁ ⊢
        apply @Ob_chisholm_bdf.F5
        exact h₀
        exact h₁
      ) (by
        constructor
        · unfold Ought ob_chisholm_bdf
          intro X hu h₀
          simp
          apply @Ob_chisholm_bdf.basic₁
          exact hu
          exact h₀
        · unfold Ought ob_chisholm_bdf
          intro X hu h₀
          simp
          apply @Ob_chisholm_bdf.basic₂
          exact hu
          exact h₀) Y _ h

    unfold ob_chisholm_bdf at this
    simp at this
    exact this
  · intro h
    set a := (X,Y)
    show a.1 ∈ canon₂ A B a.2
    apply @Ob_chisholm_bdf.rec (motive := fun a ha => a.1 ∈ canon₂ A B a.2) (A := A) (B := B)
    · clear h a X
      have := @least_model_canon₂ (Fin n) _ _ A B h
      simp [least_model] at this
      have := this.1.2.2.2.1
      unfold Ought at this
      simp
      intro X h₀
      exact this X (by simp) h₀

    · clear h a X
      have := @least_model_canon₂ (Fin n) _ _ A B h
      simp [least_model] at this
      have := this.1.2.2.2.2
      unfold Ought at this
      simp
      intro X h₀
      exact this X h₀
    · clear h a X
      have := @least_model_canon₂ (Fin n) _ _ A B h
      simp [least_model] at this
      intro X Y Z h h₀ h₁
      exact this.1.1 Y X Z h₀ h₁
    · clear h a X
      have := @least_model_canon₂ (Fin n) _ _ A B h
      simp [least_model] at this
      intro X Y Z h h₀ h₁ h₂
      have := this.1.2.1
      exact this X Y Z h h₂ h₁
    · clear h a X
      have := @least_model_canon₂ (Fin n) _ _ A B h
      simp [least_model] at this
      intro X Y Z h h₀ h₁ h₂
      have := this.1.2.2.1
      exact this X Y Z h₁ h₂
    exact h


/-- A version of `least_model_canon₂` that mentions only
older axioms than F5. -/
theorem least_model_canon₂' {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (h : A ⊆ B) :
    least_model (canon₂ A B)
    (fun ob => A5 ob ∧ B5 ob ∧ C5 ob ∧ D5 ob ∧ Ought ob A univ ∧ Ought ob B Aᶜ) := by
    have := least_model_canon₂ A B h
    unfold least_model at this ⊢
    simp_all
    constructor
    constructor
    exact canon₂_A5 A B
    exact canon₂_C5 A B
    intro ob a5 b5 c5 d5 hA hB
    exact this.2 ob b5 d5 (II_2_2_finset a5 b5 c5 d5) hA hB



def canon₃_II {α : Type*} [Fintype α] [DecidableEq α] (A B C : Finset α) :
    Finset α → Finset (Finset α) :=
  fun X ↦
      ite (X ∩ C = ∅)
      ∅
      (ite (X ∩ B = ∅)
      (filter (fun Y ↦ X ∩ C = X ∩ Y) univ)

      (ite (X ∩ A = ∅)
      (filter (fun Y ↦ X ∩ B = X ∩ Y) univ)

      (filter (fun Y ↦ X ∩ A = X ∩ Y) univ)
      )
  )


theorem maple_eq_canon₃_II (ob : Finset (Fin 4) → Finset (Finset (Fin 4))) (a b c d : Fin 4)
    (h : ob = canon₃_II {c} {c, d} {b, c, d})
    (h₀ : a = 0) (h₁ : b = 1) (h₂ : c = 2) (h₃ : d = 3) :
                                        ob ∅ = ∅
                                      ∧ ob {a} = ∅
    ∧ ob {b} = {{b}, {a, b}, {b, c}, {b, d}, {a, b, c}, {a, b, d}, {b, c, d}, {a, b, c, d}}
    ∧ ob {c} = {{c}, {a, c}, {b, c}, {c, d}, {a, b, c}, {a, c, d}, {b, c, d}, {a, b, c, d}}
    ∧ ob {d} = {{d}, {a, d}, {b, d}, {c, d}, {a, b, d}, {a, c, d}, {b, c, d}, {a, b, c, d}}
                            ∧ ob {a, b} = {{b}, {b, c}, {b, d}, {b, c, d}}
                            ∧ ob {a, c} = {{c}, {b, c}, {c, d}, {b, c, d}}
                            ∧ ob {a, d} = {{d}, {b, d}, {c, d}, {b, c, d}}
                            ∧ ob {b, c} = {{c}, {a, c}, {c, d}, {a, c, d}}
    ∧  ob {b, d} = {{d}, {a, d}, {c, d}, {a, c, d}}
                            ∧ ob {c, d} = {{c}, {a, c}, {b, c}, {a, b, c}}
     ∧ ob {a, b, c} = {{c}, {c, d}}
      ∧ ob {a, b, d} = {{d}, {c, d}}
     ∧ ob {a, c, d} = {{c}, {b, c}}
     ∧ ob {b, c, d} = {{c}, {a, c}}
     ∧ ob {a, b, c, d} = {{c}} := by
  rw [h,h₀,h₁,h₂,h₃]
  decide
