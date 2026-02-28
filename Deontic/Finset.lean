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
  ∀ (X Y Z : Finset U), (Y ∩ X = Z ∩ X) → (Y ∈ ob X → Z ∈ ob X)

def B5original {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (X Y Z : Finset U), (Y ∩ X = Z ∩ X) → (Y ∈ ob X ↔ Z ∈ ob X)

-- 5c_2013:
def C5 {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (X Y Z : Finset U), Y ∈ ob X → Z ∈ ob X →
  X ∩ Y ∩ Z ≠ ∅ → Y ∩ Z ∈ ob X

/-- An axiom going back to the 1990s. -/
def C5Strong {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (X Y Z : Finset U), Y ∈ ob X → Z ∈ ob X → Y ∩ Z ∈ ob X


/-
Axiom 5(c) in [CJ 2022] concerns potentially infinite
families, i.e., CJ5c_star. For simplicity we follow the [CJ 2013] terminology.
-/

/- 5c_2002:
def CJ5c (ob : Set U → Set (Set U)) :=
∀ (X Y Z : Set U), Y ∈ ob X → (Z ∈ ob X → Y ∩ Z ∈ ob X)
-/

open Finset
/--
5c*_2013 = 5c_2022
def CJ5c_star (ob : Set U → Set (Set U)) :=
∀ (X : Set U) (β : Set (Set U)),
  (h1 : β ⊆ ob X) → (h2 : β ≠ ∅) → ⋂₀β ∩ X ≠ ∅ → ⋂₀β ∈ ob X
-/
def D5 {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (X Y Z : Finset U), Y ⊆ X → Y ∈ ob X → X ⊆ Z → (Z \ X) ∪ Y ∈ ob Z

def BD5 {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (X Y Z : Finset U), Y ∈ ob X → X ⊆ Z → (Z \ X) ∪ Y ∈ ob Z

def E5 {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (X Y Z : Finset U), Y ⊆ X → Z ∈ ob X → Y ∩ Z ≠ ∅ → Z ∈ ob Y
def E5weak {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (Y Z : Finset U), Z ∈ ob univ → Y ∩ Z ≠ ∅ → Z ∈ ob Y
def F5 {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (X Y Z : Finset U), X ∈ ob Y → X ∈ ob Z → X ∈ ob (Y ∪ Z)
def G5 {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (X Y Z : Finset U), Y ∈ ob X → Z ∈ ob Y →
    X ∩ Y ∩ Z ≠ ∅ → Y ∩ Z ∈ ob X

-- Can we satisfy everything except B5? Not at Fin 0:
example : ∀ ob : Finset (Fin 0) → Finset (Finset (Fin 0)), C5 ob ∧ D5 ob ∧ E5 ob ∧ A5 ob → B5 ob := by
  intro ob h X Y Z h₀ h₁
  exfalso
  apply h.2.2.2
  convert h₁
  ext i
  have := i.2
  simp at this


-- Can we satisfy everything except C5? Not at Fin 0:
example : ∀ ob : Finset (Fin 0) → Finset (Finset (Fin 0)), B5 ob ∧ D5 ob ∧ E5 ob ∧ A5 ob → C5 ob := by
  intro ob h X Y Z h₀ h₁
  exfalso
  apply h.2.2.2
  convert h₁
  ext i
  have := i.2
  simp at this

-- Infinitely many models where all axioms except 5(b) hold.
-- In response to 2nd referee report from S.L., February 2026,
-- we show that B5 does not follow from
-- ACDE.
lemma B5_not_implied' {n : ℕ} : ∃ ob : Finset (Fin (n)) → Finset (Finset (Fin (n))),
  C5Strong ob ∧ D5 ob ∧ E5 ob ∧ (n ≥ 1 → A5 ob) ∧ F5 ob ∧ G5 ob ∧ (n ≥ 1 → ¬ B5 ob) := by
  use fun _ => {Finset.univ}
  constructor
  · intro X Y Z h₀ h₁
    simp at *
    tauto
  · constructor
    · intro X Y Z h₀ h₁ h₂
      simp at *
      rw [h₁]
      simp
    · constructor
      intro X Y Z h₀ h₁ h₂
      simp at *
      tauto
      constructor
      · intro hn
        simp at *
        obtain ⟨m,hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_one.mpr hn
        subst n
        intro X hc
        simp at hc
        have : 0 ∈ (∅ : Finset (Fin (m+1))) := by
          rw [hc]
          simp
        simp at this
      constructor
      · intro X Y Z h₀ h₁
        simp at *
        tauto
      constructor
      · intro X Y Z h₀ h₁
        simp at *
        tauto
      · intro hn
        simp at *
        obtain ⟨m,hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_one.mpr hn
        subst n
        unfold B5
        push_neg
        simp
        use ∅, ∅
        simp
        intro hc
        have : 0 ∈ (∅ : Finset (Fin (m+1))) := by
          rw [hc]
          simp
        simp at this


lemma A5_not_implied {n : ℕ} : ∃ ob : Finset (Fin n) → Finset (Finset (Fin n)),
  B5 ob ∧ C5 ob ∧ D5 ob ∧ E5 ob ∧ F5 ob ∧ G5 ob ∧ ¬ A5 ob := by
  use fun X => Finset.univ
  unfold B5 C5 D5 E5 F5 G5 A5
  simp


/-- Feb 22, 2026: A cool use of cosubsingletons.
    Feb 24: Can add `¬ F5 ∧ ¬ G5`.
    In contrast as proved elsewhere `abcd ⊢ f` and `bcde ⊢ g`.
-/
lemma C5_not_implied' {n : ℕ} : ∃ ob : Finset (Fin (n)) → Finset (Finset (Fin (n))),
  B5 ob ∧ D5 ob ∧ A5 ob ∧ E5 ob ∧ (n ≥ 3 → ¬ F5 ob) ∧ (n ≥ 4 → ¬ G5 ob) ∧ (n ≥ 3 → ¬ C5 ob) := by
  use fun X => {A | A ∩ X ≠ ∅ ∧ #(X \ A) ≤ 1}
  constructor
  intro X Y Z h₀ h₁
  simp at *
  have : X = Y ∩ X ∪ X \ Y := by compare
  rw [h₀] at this
  constructor
  · rw [h₀] at h₁;tauto
  · apply le_trans
    show _ ≤ #(X \ Y)
    refine Finset.card_le_card ?_
    rw [this]
    intro i hi
    simp at hi ⊢
    tauto
    exact h₁.2
  constructor
  · intro X Y Z h₀ h₁ h₂
    simp at *
    have : Z \ (Z \ X ∪ Y) = Z ∩ (X \ Y) := by
      compare
    rw [this]
    constructor
    have := h₁.1
    contrapose! this
    apply subset_empty.mp
    apply subset_trans
    show _ ⊆  (Z \ X ∪ Y) ∩ Z
    intro i ; simp;tauto
    rw [this]
    apply le_trans
    show _ ≤ #(X \ Y)
    refine Finset.card_le_card ?_
    simp
    tauto
  · constructor
    intro X
    simp
    constructor
    · intro X Y Z h₀ h₁ h₂
      simp at *
      constructor
      contrapose! h₂
      rw [← h₂]
      compare
      apply le_trans
      show _ ≤ #(X \ Z)
      refine Finset.card_le_card ?_
      exact sdiff_subset_sdiff h₀ fun ⦃a⦄ a_1 ↦ a_1
      tauto
    · constructor
      · intro hn
        simp at *
        obtain ⟨m,hm⟩ : ∃ m, n = m + 3 := by exact Nat.exists_eq_add_of_le' hn
        subst n

        unfold F5
        push_neg
        use {1}, {0,1}, {1,2}
        simp
        constructor
        have : ({1,2} : Finset (Fin (m+3))) \ {1} = {2} := by
          ext i;simp
          constructor
          · intro h
            cases h.1
            tauto
            tauto
          · intro h
            subst h
            simp
            exact not_eq_of_beq_eq_false rfl
        rw [this]
        simp
        have : ({2,0,1} : Finset (Fin (m+3))) \ {1} = {2,0} := by
          ext i;simp
          constructor
          · intro h
            cases h.1
            tauto
            tauto
          · intro h
            cases h with
            | inl h => subst h;simp;exact not_eq_of_beq_eq_false rfl
            | inr h => subst h;simp
        rw [this]
        have : #({2,0} : Finset (Fin (m+3))) = 2 := by
          exact Eq.symm (Nat.eq_of_beq_eq_true rfl)
        rw [this]
        simp
      constructor
      · intro hn
        simp at *
        obtain ⟨m,hm⟩ : ∃ m, n = m + 4 := by exact Nat.exists_eq_add_of_le' hn
        subst n
        unfold G5
        push_neg
        simp at *
        use {0,1,3}, {1,2,3}
        constructor
        · constructor
          · simp_all
          · simp_all
            rfl
        use {2,0,3}
        constructor
        · constructor
          · simp_all
          · simp_all
            rfl
        · constructor
          · refine Finset.nonempty_def.mpr ?_
            aesop
          · intro h
            have : ({0, 1, 3} : Finset (Fin (m+4))) \ ({1, 2, 3} ∩ {2, 0, 3}) =
              {0,1} := by compare
            rw [this]
            aesop
      · intro hn
        simp at *
        obtain ⟨m,hm⟩ : ∃ m, n = m + 3 := by exact Nat.exists_eq_add_of_le' hn
        subst n
        unfold C5
        push_neg
        simp
        use {0,1,2}
        use {1,2}
        constructor
        · constructor
          · simp
          · aesop
        use {0,2}
        constructor
        simp
        aesop
        constructor
        refine Finset.nonempty_def.mpr ?_
        use 2
        simp
        intro _
        have : ({0,1,2} : Finset (Fin (m+3))) \ ({1,2} ∩ {0,2}) = {0,1} := by
          ext i
          simp
          constructor
          tauto
          intro h
          constructor
          tauto
          intro h'
          cases h with
          | inl h =>
            subst h
            cases h' with
            | inl h => simp at h
            | inr h => exfalso;revert h;simp;exact NeZero.ne' 2
          | inr h =>
            subst h
            cases h' with
            | inl h => simp;exact not_eq_of_beq_eq_false rfl
            | inr h => exfalso;revert h;simp;exact not_eq_of_beq_eq_false rfl
        rw [this]
        simp



-- Superseded by `C5_not_implied'` except for the case `n=0`.
lemma C5Strong_not_implied {n : ℕ} : ∃ ob : Finset (Fin (n+2)) → Finset (Finset (Fin (n+2))),
  B5 ob ∧ D5 ob ∧ E5 ob ∧ A5 ob ∧ C5 ob ∧ ¬ C5Strong ob := by
  use (fun X =>
    {A | X ∩ A ≠ ∅})
  constructor
  · intro X Y Z h₀ h₁
    simp at h₁ ⊢
    contrapose! h₁
    rw [Finset.inter_comm, h₀, Finset.inter_comm]
    exact h₁
  · constructor
    · intro X Y Z h₀ h₁ h₂
      simp at h₁ ⊢
      contrapose! h₁
      apply subset_empty.mp
      rw [← h₁]
      intro i;simp;tauto
    · constructor
      · intro X Y Z h₀ h₁ h₂
        simp at h₁ ⊢
        exact h₂
      · constructor
        · intro X hc
          simp at hc
        · constructor
          · intro X Y Z
            simp
          unfold C5Strong
          push_neg
          simp
          use univ
          simp
          use {0}
          simp
          use {1}
          simp

/-- Weak conditional deontic explosion, implicit in [KH17]. -/
def CXweak {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (A B : Finset U), A ∈ ob univ → B \ A ≠ ∅ → B ∈ ob Aᶜ

/-- Full conditional deontic explosion, implicit in [KH17].
Many variations of this statement could be considered.
-/
def CX {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) :=
  ∀ (A B C : Finset U), A ∈ ob C → B ∩ Aᶜ ∩ C ≠ ∅ → B ∈ ob (Aᶜ ∩ C)

theorem CXimpliesWeak {U : Type*} [Fintype U] [DecidableEq U]
    (ob : Finset U → Finset (Finset U)) (h : CX ob) : CXweak ob := by
  intro A B h₀ h₁
  have := h A B univ h₀ (by
    contrapose! h₁
    rw [← h₁]
    ext;simp
  )
  convert this using 1
  simp

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
    A5 ob ∧ B5original ob ∧ C5 ob ∧ ¬ D5 ob ∧ E5 ob ∧ ¬ F5 ob ∧ G5 ob := by
  unfold A5 B5original C5 D5 E5 F5 G5
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
  ext x; simp only [Finset.notMem_empty, toFinset_empty]

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
    {ob₀ : Finset U → Finset (Finset U)} (hob₀ : B5original ob₀) :
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
  simp only [mem_setOf_eq, toFinset_union, toFinset_diff] at hob₀
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
