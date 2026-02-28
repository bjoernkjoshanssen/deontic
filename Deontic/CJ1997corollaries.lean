import Deontic.Basic
import Deontic.Finset
import Deontic.Venn
import Deontic.Canonical
import Deontic.CJ1997characterization

/-!
After the hard work in `CJ1997characterization` here we draw some abstract corollaries
such as finding the number of models and the models up to isomorphism.
-/

open Finset

/-- `stayAlive` is the ``largest'' models of CJ97. -/
example {n : ℕ} (a : Fin n) (X : Finset (Fin n)) :
  alive n X ⊆ stayAlive a X := by
  simp [alive, stayAlive]
  intro Y h₀
  simp at h₀ ⊢
  rw [inter_eq_left.mpr h₀.2]
  constructor
  · exact h₀.1
  · simp

/-- `stayAlive` is the only nontrivial model of CJ97. -/
example {n : ℕ}
    (ob : Finset (Fin n) → Finset (Finset (Fin n)))
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    (h : ∃ Y, ∃ X ⊂ Y, X ∈ ob Y) : ∃ a, ob = stayAlive a := by
  cases models_ofCJ_1997 ⟨a5, b5, c5, d5, e5⟩ with
  | inl h => exact h
  | inr h =>
    cases h with
    | inl h₀ =>
      exfalso
      obtain ⟨Y,X,h₁,h₂⟩ := h
      rw [funext_iff] at h₀
      specialize h₀ Y
      rw [h₀] at h₂
      unfold alive at h₂
      simp at h₂
      have : X = Y := by apply subset_antisymm;exact subset_of_ssubset h₁;tauto
      subst this
      revert h₁
      simp
      exact not_ssubset_of_subset fun ⦃a⦄ a ↦ a
    | inr h₀ =>
      exfalso
      rw [h₀] at h
      simp [noObligations] at h

lemma stayAlive_inter {n : ℕ} (a b : Fin n) (h : a ≠ b) (X : Finset (Fin n)) :
  stayAlive a X ∩ stayAlive b X = alive n X := by
  simp [stayAlive, alive, Finset.ext_iff]
  intro Y
  constructor
  · intro h₁
    constructor
    · tauto
    · apply subset_trans
      · intro i _
        have : i ≠ a ∨ i ≠ b :=
          Decidable.not_and_iff_or_not.mp fun hc => (hc.1 ▸ h) hc.2
        cases this with
        | inl h₀ => apply h₁.1.2; compare
        | inr h₀ => apply h₁.2.2; compare
      · simp
  · intro h
    constructor
    · constructor
      · obtain ⟨x,hx⟩ := h.1
        use x
        constructor
        · tauto
        · exact h.2 hx
      · intro i hi
        simp at hi ⊢
        constructor
        · tauto
        · exact h.2 hi.1
    · constructor
      · obtain ⟨x,hx⟩ := h.1
        use x
        constructor
        · tauto
        · apply h.2 hx
      · intro i hi
        simp at hi ⊢
        constructor
        · tauto
        · apply h.2 hi.1


-- example {n : ℕ} (a : Fin n) (X : Finset (Fin n)) :
--   canon_II {a}ᶜ X ⊆ stayAlive n a X := by
--   simp [canon_II, stayAlive]
--   intro Y hY
--   simp at *
--   by_cases H : X ∩ {a}ᶜ = ∅
--   · rw [H] at hY
--     simp at hY
--   · rw [if_neg H] at hY
--     simp at hY
--     rw [hY]
--     constructor
--     tauto
--     intro;simp

example {n : ℕ} (a : Fin n) (X : Finset (Fin n)) :
  canon {a}ᶜ X ⊆ stayAlive a X := by
  simp [canon, stayAlive]
  intro Y hY
  simp at *
  by_cases H : X ∩ {a}ᶜ = ∅
  · rw [H] at hY
    simp at hY
  · rw [if_neg H] at hY
    simp at hY
    constructor
    · contrapose! H
      apply subset_empty.mp
      rw [← H]
      apply subset_inter
      simp
      tauto
    apply subset_inter
    simp
    convert hY using 1
    exact sdiff_eq_inter_compl X {a}

example {n : ℕ} (a : Fin n) :
  ∃ X : Finset (Fin n), ¬ alive n X ⊆ canon {a}ᶜ X := by
  use {a}
  simp [alive, canon]
  use {a}
  simp


/-

        stayAlive a
          |      \
          |       \
          |      canon {a}ᶜ
          |           |
        alive         |
          |           |
          |    canon_II {a}ᶜ
           \      /
            \    /
             \  /
               ∅

-/


example {n : ℕ} :
  ∃ X,
  ¬ canon_II {0}ᶜ X ⊆ alive (n+2)  X := by
  simp [canon_II, alive]
  use {0,1}
  simp
  intro hc
  have := hc (show ({1}) ∈ _ by simp)
  simp at this



def isomorphic {n:ℕ} (ob₁ ob₂ : Finset (Fin n) → Finset (Finset (Fin n))) : Prop :=
  ∃ f : Fin n → Fin n, Function.Bijective f ∧
  ∀ X Y, Y ∈ ob₁ X ↔ ({z | f z ∈ Y} : Finset (Fin n)) ∈ ob₂ ({z | f z ∈ X} : Finset (Fin n))

lemma isomorphic_reflexive {n:ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) :
  isomorphic ob ob := by
  use id
  simp


/-- When n (and only when) n is positive, noObligations is nonisomorphic to alive.
(Can be used to subsume the proof that they're not equal!)
-/
lemma not_isomorphic_alive_noObligations {n : ℕ} (hn : n ≠ 0) :
  ¬ isomorphic (alive n) (noObligations n) := by
    unfold isomorphic
    push_neg
    intro f hf
    use univ, univ
    simp
    left
    constructor
    · simp [alive]
      refine nonempty_iff_ne_empty.mp ?_
      refine univ_nonempty_iff.mpr ?_
      refine Fin.pos_iff_nonempty.mp ?_
      omega
    · simp [noObligations]

lemma alive_ne_noObligations (m : ℕ) :
    alive m.succ ≠ noObligations m.succ := by
  intro hc
  apply not_isomorphic_alive_noObligations
  show m.succ ≠ 0
  simp
  rw [hc]
  exact isomorphic_reflexive (noObligations m.succ)

/-- When n is positive, noObligations is nonisomorphic to stayAlive. -/
lemma not_isomorphic_stayAlive_noObligations {n : ℕ} (a : Fin n) :
  ¬ isomorphic (stayAlive a) (noObligations n) := by
    unfold isomorphic
    push_neg
    intro f hf
    use univ, univ
    simp
    left
    constructor
    · simp [stayAlive]
      refine nonempty_iff_ne_empty.mp ?_
      refine univ_nonempty_iff.mpr ?_
      exact Nonempty.intro a
    · simp [noObligations]

lemma stayAlive_ne_noObligations (m : ℕ) (b : Fin m) :
    stayAlive b ≠ noObligations m := by
  intro hc
  apply not_isomorphic_stayAlive_noObligations
  rw [hc]
  apply isomorphic_reflexive


lemma not_isomorphic_stayAlive_alive {n : ℕ} (a b : Fin n) (h: a ≠ b) :
  ¬ isomorphic (stayAlive a) (alive n) := by
  unfold isomorphic
  push_neg
  intro f hf
  use univ, univ \ {a}
  left
  constructor
  · simp [stayAlive]
    constructor
    · refine nonempty_iff_ne_empty.mp ?_
      refine univ_nonempty_iff.mpr ?_
      exact Nonempty.intro a
    · refine Nontrivial.ne_singleton ?_
      refine univ_nontrivial_iff.mpr ?_
      exact nontrivial_of_ne a b h
  · simp [alive]
    intro _
    exact hf.2 a

  lemma stayAlive_ne_alive (m : ℕ) (b : Fin (m+2)) :
      stayAlive b ≠ alive (m+2) := by
    intro hc
    apply not_isomorphic_stayAlive_alive
    show (b : Fin (m+2)) ≠ b+1
    simp
    rw [hc]
    apply isomorphic_reflexive

def embed {n : ℕ} : Finset (Fin n) → Finset (Fin (n+1)) := fun Y =>
  {y | ∃ h : y.1 < n, ⟨y.1,h⟩ ∈ Y}

/-- Model theoretic notion of restriction. -/
def restriction {n : ℕ} (ob : Finset (Fin (n+1)) → Finset (Finset (Fin (n+1)))) :
  Finset (Fin n) → Finset (Finset (Fin n)) := by
  intro Y
  exact {X | embed X ∈ ob (embed Y)}

lemma noObligations_restriction {n : ℕ} :
  restriction (noObligations (n+1)) = noObligations n := by
  unfold restriction noObligations embed
  simp

lemma alive_restriction {n : ℕ} :
  restriction (alive (n+1)) = alive n := by
  unfold restriction alive embed
  simp
  ext Y X
  simp
  constructor
  · intro ⟨⟨x,hx⟩,hhx⟩
    constructor
    · contrapose! hx
      subst hx
      simp
    · intro y hy
      specialize hhx (by
        show ⟨y,by omega⟩ ∈ _
        simp
        tauto)
      simp at hhx
      tauto
  · intro h
    constructor
    · have ⟨y,hy⟩ := nonempty_def.mp $ nonempty_iff_ne_empty.mpr h.1
      use ⟨y,by omega⟩
      simp
      exact hy
    · intro y hy
      simp at hy ⊢
      obtain ⟨h₀,h₁⟩ := hy
      use h₀
      exact h.2 h₁

/-- This implies that a restriction of a model of CJ97
is also a model, which corresponds to CJ97 being a universal theory
in some sense [December 23, 2025].

The characterization implies that in each model `ob` is quantifier-free definable in the language of Boolean
algebras (by defining a single element as an atom in the Boolean algebra) in one of three ways.
Since the first order theory of Boolean algebras is decidable (Tarski) so is the CJ97 theory
of (at least the finite models of) `ob` and Boolean algebra.

-/
lemma stayAlive_alive_restriction {n : ℕ}:
  restriction (stayAlive (Fin.last n)) = alive n := by
  unfold restriction alive stayAlive embed
  ext X Y
  simp
  push_neg
  constructor
  · intro h
    constructor
    · have := h.1
      simp at this
      clear h
      have := nonempty_iff_ne_empty.mp this
      apply nonempty_iff_ne_empty.mpr
      contrapose! this
      subst this
      simp
    · have := h.2
      clear h
      intro x hx
      specialize this (by
        show ⟨x, by omega⟩ ∈ _
        simp
        constructor
        tauto
        intro hc
        have : x.1 = n := Fin.mk.inj_iff.mp hc
        have := x.2
        omega)
      simp at this
      tauto
  · intro h
    constructor
    · have := nonempty_iff_ne_empty.mp h.1
      have ⟨x,hx⟩ : ∃ x, x ∈ X := by
        refine nonempty_def.mp ?_
        exact nonempty_iff_ne_empty.mpr this
      apply nonempty_def.mpr
      use ⟨x.1, by omega⟩
      simp
      constructor
      tauto
      apply h.2
      tauto
    · intro x hx
      simp at hx ⊢
      constructor
      · tauto
      · obtain ⟨⟨h₀₀,h₀₁⟩,h₁⟩ := hx
        use h₀₀
        apply h.2
        tauto

lemma stayAlive_restriction {n : ℕ} (a : Fin n):
  restriction (stayAlive (Fin.castSucc a)) = stayAlive a := by
  unfold restriction stayAlive embed
  simp
  ext Y X
  simp
  constructor
  · push_neg
    intro h
    constructor
    · have ⟨y,hy⟩ := nonempty_def.mp h.1
      refine nonempty_def.mpr ?_
      simp at hy
      obtain ⟨⟨hyn,h₀⟩,⟨_,h₁⟩⟩ := hy
      use ⟨y.1, hyn⟩
      simp
      tauto
    · intro y hy
      have := h.2
      specialize this (by
        show ⟨y.1,by omega⟩ ∈ _
        simp at hy ⊢
        constructor
        tauto
        have := hy.2
        contrapose! this
        exact Fin.castSucc_inj.mp this)
      simp at this ⊢
      tauto
  · intro h
    constructor
    · have ⟨y,hy⟩ := nonempty_def.mp $ nonempty_iff_ne_empty.mpr h.1
      apply nonempty_iff_ne_empty.mp
      apply nonempty_def.mpr
      use ⟨y.1, by omega⟩
      simp at hy ⊢
      tauto
    · intro y hy
      simp at hy ⊢
      obtain ⟨⟨h₀₀,h₀₁⟩,h₁⟩ := hy
      use ⟨h₀₀,h₀₁⟩
      use h₀₀
      apply mem_of_mem_inter_right
      show _ ∈ Y ∩ X
      apply h.2
      simp
      constructor
      · tauto
      · contrapose! h₁
        ext
        simp
        subst h₁
        simp



lemma stayAlive_injective (m : ℕ) (a b : Fin (m+2))
  (h : stayAlive a = stayAlive b) : a = b := by
      by_contra H
      apply stayAlive_ne_alive m b
      ext X Y
      have := @stayAlive_inter (m+2) a b (by simp;tauto) X
      rw [h] at this
      simp at this
      rw [this]

lemma stayAlive_eq_alive (a : Fin 1) : stayAlive a = alive 1 := by
  unfold stayAlive alive
  ext X Y
  simp
  constructor
  · intro h
    constructor
    · have := h.1
      contrapose! this
      rw [this]
      simp
    · intro b hb
      have ⟨c,hc⟩ : ∃ c, c ∈ X ∩ Y := by
        refine nonempty_def.mp ?_
        refine nonempty_iff_ne_empty.mpr ?_
        tauto
      have : c = 0 := by exact Fin.fin_one_eq_zero c
      subst this
      have : b = 0 := Fin.fin_one_eq_zero b
      subst this
      simp at hc
      tauto
  · intro h
    constructor
    · have ⟨c,hc⟩ : ∃ c, c ∈ X := by
        refine nonempty_def.mp ?_
        refine nonempty_iff_ne_empty.mpr ?_
        tauto
      refine nonempty_iff_ne_empty.mp ?_
      refine nonempty_def.mpr ?_
      use c
      simp
      constructor
      tauto
      apply h.2
      tauto
    · intro b hb
      simp at hb ⊢
      constructor
      tauto
      apply h.2
      tauto
open Classical

theorem models_ofCJ_1997_count₀ :
    Finset.card
      {ob | (A5 (U := Fin 0) ob ∧ B5 ob ∧ C5Strong ob ∧ D5 ob ∧ E5 ob)}
      = 1 := by
      refine
        (Fintype.existsUnique_iff_card_one fun x ↦ A5 x ∧ B5 x ∧ C5Strong x ∧ D5 x ∧ E5 x).mp ?_
      use alive 0
      simp
      constructor
      · have := @models_ofCJ_1997_equiv 0 (alive 0)
        apply this.mpr
        tauto
      · intro ob
        have := @models_ofCJ_1997₀ ob
        tauto


theorem models_ofCJ_1997_count₁ :
    Finset.card
      {ob | (A5 (U := Fin 1) ob ∧ B5 ob ∧ C5Strong ob ∧ D5 ob ∧ E5 ob)}
      = 2 := by
      have : ({ob | A5 (U := Fin 1) ob ∧ B5 ob ∧ C5Strong ob ∧ D5 ob ∧ E5 ob} : Finset (Finset (Fin 1) → Finset (Finset (Fin 1))))
        =  ({alive 1, noObligations 1} : Finset (Finset (Fin 1) → Finset (Finset (Fin 1)))) := by
        ext ob
        constructor
        · simp
          intro h b5 c5 d5 e5
          have := @models_ofCJ_1997₁ ob h b5
          cases this with
          | inl h =>
            obtain ⟨a,ha⟩ := h
            subst ha
            have := stayAlive_eq_alive
            left
            apply this
          | inr h =>
            exact h
        · intro h
          simp at h ⊢
          have := @models_ofCJ_1997_equiv 1 ob
          tauto
      have : #{ob | A5 (U := Fin 1) ob ∧ B5 ob ∧ C5Strong ob ∧ D5 ob ∧ E5 ob}
        =  # ({alive 1, noObligations 1} : Finset (Finset (Fin 1) → Finset (Finset (Fin 1)))) := by
        congr
      rw [this]
      exact Eq.symm (Nat.eq_of_beq_eq_true rfl)


def swap {n : ℕ} (a b : Fin n) : Fin n → Fin n :=
fun x => ite (x=a) b (ite (x=b) a x)

lemma swap_involution {n : ℕ} (a b x : Fin n) :
  swap a b (swap a b x) = x := by
    unfold swap
    split_ifs with g₀ g₁ g₂ g₃
    all_goals try rw [g₀,g₁]
    all_goals try tauto

lemma swap_injective {n : ℕ} (a b : Fin n) : Function.Injective $ swap a b := by
    · intro x y h
      have : swap a b (swap a b x) = swap a b (swap a b y) := by rw [h]
      repeat rw [swap_involution a b] at this
      exact this





/-- The `stayAlive` models are all isomorphic in the strong sense. -/
lemma isomorphic_stayAlive {n : ℕ} (a b : Fin n) :
  isomorphic (stayAlive a) (stayAlive b) := by
  use swap a b
  constructor
  · constructor
    · exact swap_injective a b
    · exact Finite.surjective_of_injective $ swap_injective a b
  intro X Y
  constructor
  · intro h
    simp [stayAlive]
    constructor
    · refine nonempty_iff_ne_empty.mp ?_
      refine nonempty_def.mpr ?_
      simp
      simp [stayAlive] at h
      have ⟨k,hk⟩ : ∃ k, k ∈ X ∩ Y := by
        refine nonempty_def.mp ?_
        refine nonempty_iff_ne_empty.mpr ?_
        tauto
      use swap a b k
      rw [swap_involution]
      simp at hk
      exact hk
    · intro u hu
      simp at hu ⊢
      constructor
      · tauto
      · simp [stayAlive] at h
        unfold swap at hu ⊢
        by_cases H : u = a
        · subst H
          simp at *
          apply mem_of_mem_inter_right
          apply h.2
          simp
          tauto
        · rw [if_neg H] at *
          by_cases H : u = b
          · subst H
            simp at hu
          · rw [if_neg H] at hu ⊢
            apply mem_of_mem_inter_right
            apply h.2
            simp
            tauto
  · intro h
    simp [stayAlive] at h ⊢
    constructor
    · have ⟨z,hz⟩ : ∃ z, z ∈ (((({z | swap a b z ∈ X}) : (Finset (Fin n))) ∩ (({z | swap a b z ∈ Y}) : Finset (Fin n))) : (Finset (Fin n))) := by
        refine nonempty_def.mp ?_
        refine nonempty_iff_ne_empty.mpr ?_
        exact h.1
      have := h.1
      refine nonempty_iff_ne_empty.mp ?_
      refine nonempty_def.mpr ?_
      use swap a b z
      simp at *
      exact hz
    · intro u hu
      simp at hu ⊢
      constructor
      · tauto
      · apply mem_of_mem_inter_right
        show _ ∈ X ∩ Y

        have := @h.2 (swap a b u)
        simp at this ⊢
        constructor
        · tauto
        · rw [← swap_involution a b u]
          specialize this (by rw [swap_involution];tauto)
            (by
              unfold swap;rw [if_neg hu.2]
              by_cases H : u = b
              · rw [if_pos H]
                rw [H] at hu
                tauto
              · rw [if_neg H]
                tauto)
          tauto


-- For n≥ 2 there are n+2 models
theorem models_ofCJ_1997_count₂ {m : ℕ} :
    Finset.card
      {ob | (A5 (U := Fin (m+2)) ob ∧ B5 ob ∧ C5Strong ob ∧ D5 ob ∧ E5 ob)}
      = (m+2)+2 := by
  have : Finset.card {noObligations (m+2), alive (m+2)} = 2 := by
    refine card_pair ?_
    exact Ne.symm (alive_ne_noObligations (m + 1))
  have : Finset.card {ob | (∃ a : Fin (m+2), ob = stayAlive a)} = m + 2 := by
    refine card_eq_of_bijective ?_ (fun a ↦ ?_) ?_ ?_
    · intro a ha
      exact stayAlive ⟨a,ha⟩
    · simp
      intro x hx
      subst hx
      use x
      use x.2
    · intro x hx
      simp
    ·
      intro a b ha hb h
      have := @stayAlive_injective m ⟨a,ha⟩ ⟨b,hb⟩ h
      simp at this
      exact this
  have := @models_ofCJ_1997_equiv (m+2)
  have : #{ob : Finset (Fin (m+2)) → Finset (Finset (Fin (m+2))) | A5 ob ∧ B5 ob ∧ C5Strong ob ∧ D5 ob ∧ E5 ob}
    =  #{ob | (∃ a, ob = stayAlive a) ∨ ob = alive (m+2) ∨ ob = noObligations (m+2)} := by
    congr
    ext ob
    specialize this ob
    tauto
  rw [this]
  refine card_eq_of_bijective ?_ (fun ob ↦ ?_) ?_ ?_
  · intro a ha
    by_cases H : a = m + 3
    · exact noObligations (m+2)
    · by_cases H : a = m + 2
      · exact alive (m+2)
      · exact stayAlive ⟨a,by omega⟩
  intro hob
  simp at hob
  cases hob with
  | inl h =>
    obtain ⟨b,hb⟩ := h
    rw [hb]
    use b, (by omega)
    have : b ≠ m + 3 := by omega
    rw [dif_neg this]
    have : b ≠ m + 2 := by omega
    rw [dif_neg this]
  | inr h =>
    cases h with
    | inl h =>
      use m + 2
      subst h
      simp
    | inr h =>
      use m + 3
      subst h
      simp
  intro a ha
  by_cases H : a = m + 3
  · rw [dif_pos H]
    simp
  · rw [dif_neg H]
    by_cases H : a = m + 2
    · rw [dif_pos H]
      simp
    · rw [dif_neg H]
      simp
  intro a b ha hb h
  by_cases Ha : a = m + 3
  · rw [dif_pos Ha] at h
    by_cases Hb : b = m + 3
    · rw [Ha,Hb]
    · rw [dif_neg Hb] at h
      by_cases Hb' : b = m + 2
      · rw [dif_pos Hb'] at h
        exfalso
        revert h
        simp
        have := alive_ne_noObligations (m+1)
        simp at this
        tauto
      · rw [dif_neg Hb'] at h
        have := stayAlive_ne_noObligations (m+2) ⟨b,by omega⟩
        tauto
  · rw [dif_neg Ha] at h
    by_cases Hb : b = m + 3
    · rw [dif_pos Hb] at h
      by_cases Ha : a = m + 2
      · rw [dif_pos Ha] at h
        have := alive_ne_noObligations (m+1)
        simp at this
        tauto
      · rw [dif_neg Ha] at h
        have := stayAlive_ne_noObligations (m+2) ⟨a,by omega⟩
        tauto
    · rw [dif_neg Hb] at h
      by_cases Ha : a = m + 2
      · rw [dif_pos Ha] at h
        by_cases Hb : b = m + 2
        · rw [Ha,Hb]
        · rw [dif_neg Hb] at h
          have := stayAlive_ne_alive m ⟨b,by omega⟩
          tauto
      · rw [dif_neg Ha] at h
        by_cases Hb : b = m + 2
        · rw [dif_pos Hb] at h
          have := stayAlive_ne_alive m ⟨a,by omega⟩
          tauto
        · rw [dif_neg Hb] at h
          have := stayAlive_injective m ⟨a,by omega⟩ ⟨b,by omega⟩ h
          simp at this
          exact this

/-- A "never-three" theorem, a complete characterization of the number of models
on the set `[n]`.

n #
0 1
1 2
2 4
3 5
...
-/
theorem models_ofCJ_1997_count {n : ℕ} :
    Finset.card
      {ob | (A5 (U := Fin n) ob ∧ B5 ob ∧ C5Strong ob ∧ D5 ob ∧ E5 ob)}
      = ite (n<2) (n+1) (n+2) := by
    by_cases H : n = 0
    · subst H
      simp
      exact models_ofCJ_1997_count₀
    · by_cases H : n = 1
      · subst H
        simp
        exact models_ofCJ_1997_count₁
      · have : n ≥ 2 := by omega
        have ⟨m,hm⟩ : ∃ m, n = m + 2 := Nat.exists_eq_add_of_le' this
        subst hm
        simp
        exact models_ofCJ_1997_count₂
