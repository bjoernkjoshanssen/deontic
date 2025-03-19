import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Finset.Basic
import Deontic.Basic

/-!

## Canonical models of CJ 2022 axioms

We demonstrate that Carmo and Jones 2022 axioms 5(a)(b)(c)(g) do not
imply their 5(d) or 5(f).
We also show that 5(a)(b)(c)(d)(f)(g) together do not imply 5(e).
This is done using two-world model counterexamples.

None of the other axioms imply 5a:
consider the no-worlds model (which contradicts CJ axiom 1) with
`∅ ∈ ob ∅`.

We show that the system has arbitrarily large models.

-/

open Set

def A5 {U : Type*} [Fintype U] (ob : Finset U → Finset (Finset U)) :=
  ∀ (X : Finset U), ¬ ∅ ∈ ob X

def B5 {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (X Y Z : Finset U), (Y ∩ X = Z ∩ X) → (Y ∈ ob X ↔ Z ∈ ob X)

-- 5c_2013:
def C5 {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (X Y Z : Finset U), Y ∈ ob X → Z ∈ ob X →
  X ∩ Y ∩ Z ≠ ∅ → Y ∩ Z ∈ ob X
/-
Axiom 5(c) in [CJ 2022] concerns potentially infinite
families, i.e., CJ5c_star. For simplicity we follow the [CJ 2013] terminology.
-/

/- 5c_2002:
def CJ5c (ob : Set U → Set (Set U)) :=
∀ (X Y Z : Set U), Y ∈ ob X → (Z ∈ ob X → Y ∩ Z ∈ ob X)
-/

/--
5c*_2013 = 5c_2022
def CJ5c_star (ob : Set U → Set (Set U)) :=
∀ (X : Set U) (β : Set (Set U)),
  (h1 : β ⊆ ob X) → (h2 : β ≠ ∅) → ⋂₀β ∩ X ≠ ∅ → ⋂₀β ∈ ob X
-/

def D5 {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (X Y Z : Finset U), Y ⊆ X → Y ∈ ob X → X ⊆ Z → (Z \ X) ∪ Y ∈ ob Z
def E5 {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (X Y Z : Finset U), Y ⊆ X → Z ∈ ob X → Y ∩ Z ≠ ∅ → Z ∈ ob Y
def F5 {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (X Y Z : Finset U), X ∈ ob Y → X ∈ ob Z → X ∈ ob (Y ∪ Z)
def G5 {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (X Y Z : Finset U), Y ∈ ob X → Z ∈ ob Y →
    X ∩ Y ∩ Z ≠ ∅ → Y ∩ Z ∈ ob X

/-- All the ob's satisfying 5(a) and 5(b) in a two-world domain. -/
def ob₂ (b : Fin 5 → Bool) (B : Finset (Fin 2)) :
    Finset (Finset (Fin 2)) :=
  Finset.filter (λ A =>
    A ∩ B ≠ ∅ ∧
    (B = {0} → b 0) ∧
    (B = {1} → b 1) ∧
    (B = {0,1} →
      ((A = {0} → b 3) ∧ (A = {1} → b 4) ∧ (A = {0,1} → b 2)))
  ) Finset.univ

theorem ob₂5a : ∀ (b : Fin 5 → Bool),
  A5 (ob₂ b) := by unfold A5 ob₂; decide
theorem ob₂5b : ∀ (b : Fin 5 → Bool),
  B5 (ob₂ b) := by unfold B5 ob₂; decide
theorem ob₂5c : ∀ (b : Fin 5 → Bool),
  C5 (ob₂ b) := by unfold C5 ob₂; decide
theorem ob₂5d : ∀ (b : Fin 5 → Bool), ((b 0 || b 1) → b 2) →
  D5 (ob₂ b) := by unfold D5 ob₂; decide
theorem ob₂5e :
    ∀ (b : Fin 5 → Bool), (b 0 = b 1) → (b 1 = b 2) →
    (b 3 → b 0) → (b 4 → b 1) → E5 (ob₂ b) :=
  by unfold E5 ob₂; decide
theorem ob₂5f : ∀ (b : Fin 5 → Bool), ((b 0 || b 1) → b 2) →
  F5 (ob₂ b) := by unfold F5 ob₂; decide
theorem ob₂5g : ∀ (b : Fin 5 → Bool),
  G5 (ob₂ b) := by unfold G5 ob₂; decide


theorem do_not_imply_5d_or_5f :
    ∃ ob : Finset (Fin 2) → Finset (Finset (Fin 2)),
    A5 ob ∧ B5 ob ∧ C5 ob ∧ ¬ D5 ob ∧ E5 ob ∧ ¬ F5 ob ∧ G5 ob := by
  unfold A5 B5 C5 D5 E5 F5 G5
  use ob₂ ![true,true,false,false,false]
  repeat use (by decide)

open Classical

def converter {U : Type} [Fintype U]
  (ob : Finset U → Finset (Finset U)) :
           Set U → Set       (Set U) := by
  intro S T
  exact T.toFinset ∈ ob S.toFinset

lemma empty_finset {U : Type} [Fintype U] {X : Set U}
  (h : X.toFinset = ∅) : X = ∅ := by
    ext x
    have : x ∈ X.toFinset ↔ x ∈ (∅ : Finset U) := by rw [h]
    simp at this
    simp
    tauto

lemma toFinset_empty' {U : Type} [Fintype U] :
    ∅ = @toFinset U ∅ (Fintype.ofFinite _) := by
  ext x; simp only [Finset.not_mem_empty, toFinset_empty]

lemma get_5a {U : Type} [Fintype U]
    {ob₀ : Finset U → Finset (Finset U)} (hob₀ : A5 ob₀) :
    CJ5a fun S => {T | T.toFinset ∈ ob₀ S.toFinset} := by
  unfold A5 at hob₀
  rw [toFinset_empty'] at hob₀
  intro X
  simp
  let Q := hob₀ X.toFinset
  rw [toFinset_empty']
  tauto

lemma get_5b {U : Type} [Fintype U] [DecidableEq U]
    {ob₀ : Finset U → Finset (Finset U)} (hob₀ : B5 ob₀) :
    CJ5b fun S => {T | T.toFinset ∈ ob₀ S.toFinset} := by
  intro X Y Z h
  repeat rw [mem_setOf_eq]
  symm
  exact hob₀ X.toFinset Y.toFinset Z.toFinset (by
    repeat rw [← toFinset_inter]
    exact toFinset_inj.mpr h.symm
  )

lemma inter_inter_toFinset {U : Type} [Fintype U] [DecidableEq U]
    {X Y Z : Set U} (h₀ : X ∩ Y ∩ Z ≠ ∅) :
    X.toFinset ∩ Y.toFinset ∩ Z.toFinset ≠ ∅ := by
  repeat rw [← toFinset_inter]
  exact fun h => h₀ <| toFinset_inj.mp <| h ▸ toFinset_empty.symm

lemma get_5c {U : Type} [Fintype U] [DecidableEq U]
    {ob₀ : Finset U → Finset (Finset U)} (hob₀ : C5 ob₀) :
    CJ5c_star_finite fun S => {T | T.toFinset ∈ ob₀ S.toFinset} := by
  intro _ _ _ hY hZ hβ
  simp only [mem_setOf_eq, toFinset_inter]
  apply hob₀ _ _ _ hY hZ <| inter_inter_toFinset hβ

lemma get_not_5d {U : Type} [Fintype U] [DecidableEq U]
    {ob₀ : Finset U → Finset (Finset U)} (hob₀ : ¬D5 ob₀) :
    ¬ CJ5d fun S => {T | T.toFinset ∈ ob₀ S.toFinset} := by
  unfold CJ5d
  contrapose hob₀
  simp only [Decidable.not_not]
  simp only [mem_setOf_eq, toFinset_union, toFinset_diff,
    not_forall, Classical.not_imp, exists_and_left, not_exists, not_and,
    Decidable.not_not] at hob₀
  intro X Y Z h₀ h₁ h₂
  specialize hob₀ X Y Z h₀
  simp only [Finset.toFinset_coe] at hob₀
  exact hob₀ h₁ h₂

theorem Set_result_from_computation :
    ∃ U : Type, ∃ ob : Set U → Set (Set U),
    CJ5a ob ∧ CJ5b ob ∧ CJ5c_star_finite ob ∧ ¬ CJ5d ob := by
  use Fin 2
  obtain ⟨ob₀,hob₀⟩ := do_not_imply_5d_or_5f
  use converter ob₀, get_5a hob₀.1,
    get_5b hob₀.2.1, get_5c hob₀.2.2.1, get_not_5d hob₀.2.2.2.1


theorem do_not_imply_5e :
    ∃ ob : Finset (Fin 2) → Finset (Finset (Fin 2)),
    A5 ob ∧ B5 ob ∧ C5 ob ∧ D5 ob ∧ ¬ E5 ob ∧ F5 ob ∧ G5 ob := by
  unfold A5 B5 C5 D5 E5 F5 G5
  use ob₂ ![false,false,true,false,false]
  repeat use (by decide)
