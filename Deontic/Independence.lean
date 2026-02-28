import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Finset.Basic
import Deontic.Basic
import Deontic.Canonical

/-!

## Independence results CJ 2022 axioms

We demonstrate that Carmo and Jones 2022 axioms 5(a)(b)(c)(g) do not
imply their 5(d) or 5(f).
We also show that 5(a)(b)(c)(d)(f)(g) together do not imply 5(e).
This is done using two-world model counterexamples.

None of the other axioms imply 5a:
consider the no-worlds model (which contradicts CJ axiom 1) with
`∅ ∈ ob ∅`.

Among the axioms 5(abcde), no four imply the fifth.

We show that the system has arbitrarily large models.

-/

open Set




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
  B5 ob ∧ C5Strong ob ∧ D5 ob ∧ E5 ob ∧ F5 ob ∧ G5 ob ∧ ¬ A5 ob := by
  use fun X => Finset.univ
  unfold B5 C5Strong D5 E5 F5 G5 A5
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



theorem CJ97_not_implied {n : ℕ} :
  ∀ i : Fin 5,
  ∃ ob : Finset (Fin (n+4)) → Finset (Finset (Fin (n+4))),
  let li := ![A5 ob, B5 ob, C5Strong ob, D5 ob, E5 ob]
  (∀ j : Fin 5, j ≠ i → li j) ∧ ¬ li i := by
  intro i
  fin_cases i
  · have ⟨ob,hob⟩ := @A5_not_implied (n+4)
    use ob
    simp
    constructor
    · intro j
      fin_cases j
      all_goals try simp
      all_goals try tauto
    · apply hob.2.2.2.2.2.2
  · have ⟨ob,hob⟩ := @B5_not_implied' (n+4)
    use ob
    simp
    constructor
    · intro j
      fin_cases j
      all_goals try simp
      all_goals try tauto
      apply hob.2.2.2.1
      omega
    · apply hob.2.2.2.2.2.2
      omega
  · have ⟨ob,hob⟩ := @C5Strong_not_implied (n+2)
    use ob
    constructor
    · intro j
      fin_cases j
      all_goals try simp
      all_goals try tauto
    · tauto
  · use @canon_II (Fin (n+4)) _ _ {0}
    simp
    constructor
    · intro j
      fin_cases j
      all_goals try simp
      · rw [canon_II_is_canon₂_II]
        apply canon₂_II_A5
      · rw [canon_II_is_canon₂_II]
        apply canon₂_II_B5
      · rw [canon_II_is_canon₂_II]
        apply canon₂_II_C5Strong
      · apply canon_II_E5
    · apply many_not_canon_II_D5 <;> simp
  · use @canon (Fin (n+4)) _ _ {0}
    simp
    constructor
    · intro j
      fin_cases j
      all_goals try simp
      · rw [canon_eq_canon₂]
        apply canon₂_A5
      · rw [canon_eq_canon₂]
        apply canon₂_B5
      · rw [canon_eq_canon₂]
        apply canon₂_C5Strong
      · rw [canon_eq_canon₂]
        apply canon₂_D5
        simp
    · exact @many_not_canon_E5 (n+4) {0} (by simp) (by simp)
