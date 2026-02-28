import Deontic.Basic
import Deontic.Finset
import Deontic.Venn
import Deontic.Canonical
import Deontic.CJ1997characterization
import Deontic.CJ1997corollaries

/-!
After the hard work in `CJ1997characterization` here we draw some abstract corollaries
such as finding the number of models and the models up to isomorphism.
-/

open Finset

open Classical
/--
Feb 25, 2026:
In two separate universes α, β,
a context in `α ⊕ β` is obligatory if both of its parts are.

A strange idea, in order to refute several axioms at once.
-/
noncomputable def join_ob {α β : Type*} [Fintype α] [Fintype β]
  (ob₁ : Finset α → Finset (Finset α))
  (ob₂ : Finset β → Finset (Finset β)) :
  Finset (α ⊕ β) → Finset (Finset (α ⊕ β)) := by
  intro X
  let X' : Finset (α ⊕ β) := {a : α ⊕ β | ∃ x, a = .inl x}
  simp at X'
  let leftSide : Finset (α ⊕ β) → Finset α := fun S => {a | .inl a ∈ S}
  let rightSide : Finset (α ⊕ β) → Finset β := fun S => {a | .inr a ∈ S}
  exact {A | leftSide A ∈ ob₁ (leftSide X)
          ∧ rightSide A ∈ ob₂ (rightSide X)}


noncomputable def prod_ob {α β : Type*} [Fintype α] [Fintype β]
  (ob₁ : Finset α → Finset (Finset α))
  (ob₂ : Finset β → Finset (Finset β)) :
  Finset (α × β) → Finset (Finset (α × β)) := by
  intro X
  exact {A |
    ∃ C : Finset α, ∃ D : Finset β,
      C ∈ ob₁ {a : α | ∃ b : β, (a,b) ∈ X}
    ∧ D ∈ ob₂ {b : β | ∃ a : α, (a,b) ∈ X} ∧
    Aᶜ ⊆ ({a : α × β | a.1 ∉ C ∧ a.2 ∉ D} : Finset (α × β))}

lemma prod_noObligations' {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β] (ob : Finset β → Finset (Finset β)) :
  prod_ob ob (noObligations' α) = (noObligations' (β × α)) := by
  ext X Y
  unfold prod_ob noObligations'
  simp

lemma prod_stayAlive {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β] (a : α) (b : β) :
  prod_ob (stayAlive a)
          (stayAlive b) =
          (stayAlive (a,b)) := by
  ext X Y
  unfold prod_ob stayAlive
  simp
  constructor
  · intro h
    constructor
    · obtain ⟨C,hC⟩ := h
      have h₀ := hC.1.1
      have h₁ := hC.1.2
      have ⟨D,hD⟩ := hC.2
      have h₂ := hD.1.1
      have h₃ := hD.1.2
      have h₄ := hD.2
      clear hD hC
      have ⟨u,hu⟩ : ∃ u, u ∈ ({a | ∃ b, (a, b) ∈ X} : Finset α) ∩ C := by
        clear h₁ h₂ h₃ h₄ D Y
        refine nonempty_def.mp ?_
        convert Finset.nonempty_iff_ne_empty.mpr h₀
      simp at hu
      obtain ⟨v,hv⟩ := hu.1
      suffices ∃ w, w ∈ X ∩ Y by
        exact nonempty_iff_ne_empty.mp this
      use (u,v)
      simp
      constructor
      tauto
      suffices u ∈ C ∨ v ∈ D by
        by_contra H
        have : (u,v) ∈ (Yᶜ : Finset (α × β)) := by
          simp;tauto
        specialize h₄ (by convert this)
        simp at h₄
        tauto
      tauto -- wow
    · obtain ⟨C,hC⟩ := h
      have h₀ := hC.1.1
      have h₁ := hC.1.2
      have h₂ := hC.2
      clear hC
      obtain ⟨D,hD⟩ := h₂
      have h₃ := hD.1.1
      have h₄ := hD.1.2
      have h₅ := hD.2
      intro (u,v) huv
      simp at huv ⊢
      constructor
      tauto
      suffices u ∈ C ∨ v ∈ D by
        by_contra H
        have : (u,v) ∈ (Yᶜ : Finset (α × β)) := by
          simp;tauto
        specialize h₅ (by convert this)
        simp at h₅
        tauto
      by_cases h : u = a
      subst h
      simp_all
      specialize h₄ (by
        show v ∈ _;simp
        constructor
        use u
        tauto
        tauto)
      simp at h₄
      tauto
      specialize h₁ (by
        show u ∈ _
        simp
        constructor
        use v
        tauto
        tauto)
      simp at h₁
      tauto
  intro h
  use {a}ᶜ
  constructor
  · constructor
    · sorry
    · intro j hj;simp at hj ⊢;tauto
  · use {b}ᶜ
    constructor
    · constructor
      · sorry
      · intro j hj;simp at hj ⊢;tauto
    · simp;sorry



noncomputable def joinOb {α β : Type*} [Fintype α] [Fintype β]
  (ob₁ : Finset α → Finset (Finset α))
  (ob₂ : Finset β → Finset (Finset β)) :
  Finset (α ⊕ β) → Finset (Finset (α ⊕ β)) := by
  intro X
  let leftSide : Finset (α ⊕ β) → Finset α := fun S => {a | .inl a ∈ S}
  let rightSide : Finset (α ⊕ β) → Finset β := fun S => {a | .inr a ∈ S}
  exact {A | (leftSide (A ∩ X) ≠ ∅ ∧ leftSide A ∈ ob₁ (leftSide X))
          ∧ (rightSide (A ∩ X) ≠ ∅ ∧ rightSide A ∈ ob₂ (rightSide X))}

-- lemma join_stayAlive_alive' {m n : ℕ} (X Y)
-- (hXY : ¬ ({a | Sum.inl a ∈ X} : Finset (Fin (m+1)))
--        ∩ ({a | Sum.inl a ∈ Y} : Finset (Fin (m+1))) = ∅)
-- (h'' :  ∃ a, Sum.inr a ∈ X) :
--   Y ∈ joinOb (stayAlive (0: Fin (m+1))) (alive₀ (Fin n)) X ↔
--     Y ∈ stayAlive (Sum.inl 0) X := by
--  sorry

noncomputable def join_ob' {α β : Type*} [Fintype α] [Fintype β]
  (ob₁ : Finset α → Finset (Finset α))
  (ob₂ : Finset β → Finset (Finset β)) :
  Finset (α ⊕ β) → Finset (Finset (α ⊕ β)) := by
  intro X
  let leftSide : Finset (α ⊕ β) → Finset α := fun S => {a | .inl a ∈ S}
  let rightSide : Finset (α ⊕ β) → Finset β := fun S => {a | .inr a ∈ S}
  exact {A | (leftSide A ∈ ob₁ (leftSide X))
          ∧  (rightSide A ∈ ob₂ (rightSide X))}

lemma join_ob_A {α β : Type*} [Fintype α] [Fintype β]
  (ob₁ : Finset α → Finset (Finset α))
  (ob₂ : Finset β → Finset (Finset β)) :
  A5 ob₁ → A5 (join_ob' ob₁ ob₂) := by
  intro h X hc
  unfold join_ob' at hc
  simp at hc
  specialize h {a | Sum.inl a ∈ X}
  tauto

lemma join_noObligations' {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β] (ob : Finset β → Finset (Finset β)) :
  join_ob' ob (noObligations' α) = (noObligations' (β ⊕ α)) := by
  ext X Y
  unfold join_ob' noObligations'
  simp

lemma join_alive {m n : ℕ} ( X Y ) (hXY: X ∩ Y ≠ ∅)
(h' : ¬{a | Sum.inl a ∈ X} ∩ {a | Sum.inl a ∈ Y} = ∅)
(h'' :  ∃ a, Sum.inr a ∈ X)
:
  Y ∈ join_ob' (alive₀ (Fin m)) (alive₀ (Fin n)) X ↔
    Y ∈ alive₀ (Fin m ⊕ Fin n) X := by
  by_cases hY : Y = ∅
  · subst Y
    unfold alive₀ join_ob'
    simp
  unfold alive₀ join_ob'
  simp
  constructor
  · intro h
    constructor
    · exact ne_of_apply_ne (fun X ↦ X ∩ Y) hXY
    · have h₀ := h.1.1
      have h₁ := h.1.2
      have h₂ := h.2.1
      have h₃ := h.2.2
      clear h
      intro j hj
      cases j with
      | inl val =>
        simp at h₁ ⊢
        specialize h₁ (by
          show val ∈ _
          simp
          tauto)
        simp at h₁
        tauto
      | inr val =>
        simp at h₃ ⊢
        specialize h₃ (by
          show val ∈ _
          simp
          tauto)
        simp at h₃
        tauto
  · intro h
    constructor
    · constructor
      · contrapose! h'
        ext a
        simp
        intro ha
        exfalso
        apply h' _ ha
      · intro x hx
        simp at hx ⊢
        have := h.2
        apply this
        tauto
    · constructor
      · tauto
      · intro g hg
        simp at hg ⊢
        apply h.2 hg


/- The join of `stayAlive` and `alive` is almost equal
to another `stayAlive`. -/
-- lemma join_stayAlive_alive {m n : ℕ} (X Y) :
--   Y ∈ joinOb (stayAlive (0: Fin (m+1))) (alive₀ (Fin n)) X ↔
--   Y ∈ stayAlive (Sum.inl 0) X := by
--   unfold joinOb stayAlive alive₀
--   simp
--   constructor
--   · intro h
--     have h₀ := h.1.1
--     have h₁ := h.1.2.1
--     have h₂ := h.1.2.2
--     have h₃ := h.2.1
--     have h₄ := h.2.2.1
--     have h₅ := h.2.2.2
--     clear h
--     constructor
--     · sorry -- true
--     · intro j hj
--       cases j with
--       | inl val =>
--         sorry -- true
--       | inr val =>
--         sorry -- true
--   · intro h
--     have h₀ := h.1
--     have h₃ := h.2
--     clear h
--     constructor
--     · constructor
--       · sorry -- false
--       constructor
--       · sorry
--       intro j hj
--       sorry
--     · constructor
--       · sorry
--       constructor
--       · sorry
--       intro j hj
--       sorry

/-- Feb 25, 2026 -/
lemma join_ob_B {α β : Type*} [Fintype α] [Fintype β]
  (ob₁ : Finset α → Finset (Finset α))
  (ob₂ : Finset β → Finset (Finset β))
  (H : ∃ X₁ X₂, X₁ ∩ X₂ ∈ ob₂ X₂) -- mild extra assumption
  (h : B5 (join_ob ob₁ ob₂)) : B5 ob₁ := by
  by_cases H' : ¬ ∃ X₁ X₂, X₁ ∩ X₂ ∈ ob₂ X₂
  · clear H
    push_neg at H'
    intro X Y Z h₀ h₁
    by_cases H'' : ∃ X₁ X₂, X₁ ∩ X₂ ∈ join_ob ob₁ ob₂ X₂
    · unfold join_ob at H''
      simp at H''
      obtain ⟨X₁,X₂,hX⟩ := H''
      specialize H' {a | Sum.inr a ∈ X₁}
        {a | Sum.inr a ∈ X₂}
      exfalso
      apply H'
      convert hX.2 using 1
      compare

    · push_neg at H''
      by_cases G : ∀ X, join_ob ob₁ ob₂ X = ∅
      · unfold join_ob at G
        -- very particular situation: either ob₁ or ob₂ is ∅
        simp at G
        have : (∀ X, ob₁ X = ∅) ∨ ∀ X, ob₂ X = ∅ := by
          by_cases G₁ : ∃ X, ob₁ X ≠ ∅
          · obtain ⟨X₁,hX₁⟩ := G₁
            obtain ⟨Y₁,hY₁⟩ : ∃ Y₁, Y₁ ∈ ob₁ X₁ := by
              refine Finset.nonempty_def.mp ?_
              exact Finset.nonempty_iff_ne_empty.mpr hX₁
            right
            intro X
            by_contra G₂
            obtain ⟨Y,hY⟩ : ∃ Y, Y ∈ ob₂ X := by
              refine Finset.nonempty_def.mp ?_
              exact Finset.nonempty_iff_ne_empty.mpr G₂
            specialize @G {a | ∃ x ∈ X₁, a = .inl x
                             ∨ ∃ x ∈ X, a = .inr x}
              {a | ∃ x ∈ Y₁, a = .inl x ∨
                   ∃ x ∈ Y, a = .inr x}
            simp at G
            specialize G hY₁
            by_cases h₀ : Y₁ = ∅
            · sorry -- violates A5
            · have : ∃ a, a ∈ Y₁ := by
                refine Finset.nonempty_def.mp ?_
                exact Finset.nonempty_iff_ne_empty.mpr h₀
              simp_all

              by_cases H₁ : X₁ = ∅
              · sorry -- violates A5
              · have : ∃ a, a ∈ X₁ := by
                  refine Finset.nonempty_def.mp ?_
                  exact Finset.nonempty_iff_ne_empty.mpr H₁
                simp_all
          · push_neg at G₁
            tauto
        -- could be ruled out by hypothesis
        sorry
      · push_neg at G
        obtain ⟨X₂,hX₂⟩ := G
        obtain ⟨X₁, hX₁⟩ : ∃ X₁, X₁ ∈ join_ob ob₁ ob₂ X₂ :=
          Finset.nonempty_def.mp hX₂
        specialize H'' X₁ X₂
        exfalso
        specialize h X₂ X₁ (X₁ ∩ X₂) (by simp) hX₁
        tauto
  unfold B5
  intro X Y Z h₀ h₁
  unfold join_ob at h
  simp at h
  obtain ⟨X₁,X₂,hX₂⟩ := H

  specialize h {u | (∃ x ∈ X, u = .inl x) ∨ ∃ x ∈ X₂,      u = .inr x}
               {u | (∃ x ∈ Y, u = .inl x) ∨ ∃ x ∈ X₁ ∩ X₂, u = .inr x}
               {u | (∃ x ∈ Z, u = .inl x) ∨ ∃ x ∈ X₁ ∩ X₂, u = .inr x}
               (by
                ext u
                simp
                intro h₀
                constructor
                · intro g
                  cases g with
                  | inl h =>
                    cases h₀ with
                    | inl h₁ =>
                      left
                      -- true!
                      suffices  ∃ x ∈ Z ∩ X, u = Sum.inl x by
                        obtain ⟨x,hx⟩ := this
                        use x
                        simp at hx
                        tauto
                      rw [← h₀]
                      obtain ⟨x₀,hx₀⟩ := h
                      obtain ⟨x₁,hx₁⟩ := h₁
                      have : x₀ = x₁ := by
                        have := Eq.trans hx₀.2.symm hx₁.2
                        apply Sum.inl_injective this
                      subst this
                      simp
                      use x₀
                      tauto
                    | inr h₁ =>
                      obtain ⟨x₀,hx₀⟩ := h
                      obtain ⟨x₁,hx₁⟩ := h₁
                      have := Eq.trans hx₀.2.symm hx₁.2
                      simp at this
                  | inr h =>
                    tauto
                · intro g
                  cases g with
                  | inl h =>
                    cases h₀ with
                    | inl h₁ =>
                      left
                      -- true!
                      suffices  ∃ x ∈ Y ∩ X, u = Sum.inl x by
                        obtain ⟨x,hx⟩ := this
                        use x
                        simp at hx
                        tauto
                      rw [h₀]
                      obtain ⟨x₀,hx₀⟩ := h
                      obtain ⟨x₁,hx₁⟩ := h₁
                      have : x₀ = x₁ := by
                        have := Eq.trans hx₀.2.symm hx₁.2
                        apply Sum.inl_injective this
                      subst this
                      simp
                      use x₀
                      tauto
                    | inr h₁ =>
                      obtain ⟨x₀,hx₀⟩ := h
                      obtain ⟨x₁,hx₁⟩ := h₁
                      have := Eq.trans hx₀.2.symm hx₁.2
                      simp at this
                  | inr h =>
                    tauto)
  simp at h
  specialize h h₁ (by
    convert hX₂ using 1
    compare)
  tauto
