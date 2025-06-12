import Deontic.Basic
import Deontic.Finset
import Deontic.Venn
/-!

## Graded models of Carmo and Jones' systems

We show that the two approaches sketched in [Kjos-Hanssen 2017]
are both consistent with [Carmo Jones 2022].

To incorporate contrary-to-duty obligations we introduce predicates
`A`, `B` for the best and at least second-best worlds with `A ⊆ B`.

If `X ∩ A = ∅` but `X ∩ B ≠ ∅`, the desirable worlds given `X`
are `X ∩ B`.

We prove the following results about which axioms hold in which model.
Since the models without the subscript ₂ are special cases of those
with it, some results follow: these are indicated with (parentheses).

| 5  | `canon`      | `canon_II`      | `canon₂`     | `canon₂_II`      |
| -- | ------------ | --------------- | ------------ | ---------------- |
| a  | (✓           | (✓)             | ✓            | ✓                |
|    |              |                 |`canon₂_A5`   |`canon₂_II_A5`    |
| -- | ------------ | --------------- | ------------ | ---------------- |
| b  | (✓)          | (✓)             | ✓            | ✓                |
|    |              |                 |`canon₂_B5`   |`canon₂_II_B5`    |
| -- | ------------ | --------------- | ------------ | ---------------- |
| c  | (✓)          | (✓)             | ✓            | ✓                |
|    |              |                 |`canon₂_C5`   |`canon₂_II_C5`    |
| -- | ------------ | --------------- | ------------ | ---------------- |
| d  | (✓)          | ×               | ✓            |(×)               |
|    |              |`not_canon_II_D5`|`canon₂_D5`   |                  |
| -- | ------------ | --------------- | ------------ | ---------------- |
| e  | ×            | ✓               |(×)           | ✓                |
|    |`not_canon_E5`|`canon_II_E5`    |              |`canon₂_II_E5`    |
| -- | ------------ | --------------- | ------------ | ---------------- |
| f  | (✓)          | ✓               | ✓            | ×!               |
|    |              |`canon_II_F5`    |`canon₂_F5`   |`not_canon₂_II_F5`|
| -- | ------------ | --------------- | ------------ | ---------------- |
| g  | ✓            | (✓)             | ×!           | ✓                |
|    |`canon_G`     |                 |`not_canon₂_G`|`canon₂_II_G5`    |
| -- | ------------ | --------------- | ------------ | ---------------- |
The counterexamples used are quite simple and include A = {0} ⊆ U = {0,1},
A = {0} ⊆ B = {0,1} = U,
and A = {0} ⊆ B = {0,2} ⊆ U = {0,1,2},
with X = {0, 1}, Y = {0, 1, 2}, Z = {1, 2}.

We study three systems in detail:
* CJ 1997: the models have a unique-bad-world feature. Nevertheless the system has several models.
* CJ 2013: the system implies conditional deontic explosion but not unique-bad-world.
* CJ 2022: the system does not imply unique-bad-world but the brief-marriage paradox.

Perhaps fittingly for papers about contrary-to-duty obligations,
ideally we should avoid the brief-marriage paradox,
but if we cannot we should at least avoid deontic explosion, and if we cannot,
at least avoid unique-bad-world.
-/

open Finset

def canon {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
Finset α → Finset (Finset α) :=
  fun S ↦ ite (S ∩ A = ∅) ∅ ((filter (fun T ↦ S ∩ A ⊆ T)) univ)

/-- The `canon` models, which say that
what is obligatory is to be in one of the still-possible optimal worlds,
satisfy all axioms except E5.
This corresponds to approach (I) in [Kjos-Hanssen 2017]

We make a [CJ 2022] style `canon_II` by letting `ob X = {Y | Y ∩ X = A ∩ X}`.
[Kjos-Hanssen 2017]'s (II) corresponds to:
-/
def canon_II {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
Finset α → Finset (Finset α) :=
  fun X ↦ ite (X ∩ A = ∅) ∅
  ((filter (fun Y ↦ X ∩ Y = X ∩ A)) univ)

def canon_II'' {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
Finset α → Finset (Finset α) :=
  fun X ↦ ite (X ∩ A = ∅) (univ \ {∅})
  ((filter (fun Y ↦ X ∩ Y = X ∩ A)) univ)


lemma canon_II_symm {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) : canon_II A = fun X =>
    ite (X ∩ A = ∅) ∅ (filter (fun Y ↦ X ∩ A = X ∩ Y) univ) := by
  unfold canon_II
  ext x
  by_cases H : x ∩ A = ∅
  · rw [H]
    simp
  · repeat rw [if_neg H]
    simp only [mem_filter, mem_univ, true_and]
    tauto

/-- canon_II does satisfy axiom 5(e). -/
theorem canon_II_E5 {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) : E5 (canon_II A) := by
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
theorem not_canon_E5 :
    ∃ n : ℕ, ∃ A : Finset (Fin n), ¬ E5 (canon A) := by
  use 2; use {0}
  unfold E5 canon
  push_neg
  use univ, {1}, univ
  constructor
  . simp
  . constructor
    . simp
    . simp


theorem many_not_canon_II_D5 {n : ℕ} {A : Finset (Fin n)}
  (h₀ : A ≠ ∅) (h₁ : A ≠ univ) : ¬ D5 (canon_II A) := by
  unfold D5; push_neg
  use A, A, univ
  constructor
  . trivial
  · unfold canon_II
    simp
    repeat rw [if_neg h₀]
    simp
    tauto

theorem many_not_canon_II''_D5 {n : ℕ} {A : Finset (Fin n)}
  (h₀ : A ≠ ∅) (h₁ : A ≠ univ) : ¬ D5 (canon_II'' A) := by
  unfold D5; push_neg
  use A, A, univ
  constructor
  . trivial
  · unfold canon_II''
    simp
    repeat rw [if_neg h₀]
    simp
    tauto


/-- canon_II does not satisfy axiom 5(d). -/
theorem not_canon_II_D5 :
    ∃ n, ∃ A : Finset (Fin n), ¬ D5 (canon_II A) := by
  use 2, {0}
  unfold D5; push_neg
  use {0}, {0}, univ
  constructor
  . trivial
  · unfold canon_II
    simp
    tauto

def canon₂ {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) :
    Finset α → Finset (Finset α) :=
  fun X ↦ ite (X ∩ B = ∅) ∅ (
      ite (X ∩ A = ∅)
      (filter (fun T ↦ X ∩ B ⊆ T) univ)
      (filter (fun T ↦ X ∩ A ⊆ T) univ)
  )

/-- There is some uncertainty about what is obligatory
when no good options are available.
This definition avoids that by packaging it into a set `P`.
-/
def canon₂' {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α)
    (P : Finset <|Finset α):
    Finset α → Finset (Finset α) :=
  fun X ↦ ite (X ∩ B = ∅) P (
      ite (X ∩ A = ∅)
      (filter (fun T ↦ X ∩ B ⊆ T) univ)
      (filter (fun T ↦ X ∩ A ⊆ T) univ)
  )



-- lemma lemma9_1996_ind {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n)))
--     (a : Fin n)
--     (h : ∀ X, a ∈ X → {a} ∈ ob X) -- h says O(A | ⊤) when A={0}
--     (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) :
--     ∀ X, a ∈ X → ob X = {Y | a ∈ Y}.toFinset := by
--   induction n with
--   | zero =>
--     have := a.2
--     simp at this
--   | succ n hn =>
--     intro X haX
--     ext S
--     simp
--     constructor
--     · intro hBX
--       have : {a} ∈ ob X := by
--         apply h
--         tauto
--       have h₀ : S ∩ {a} ∈ ob X := by
--         apply c5 _ _ _ hBX this
--       have : ∅ ∉ ob X := a5 _
--       by_contra H
--       have : S ∩ {a} = ∅ := by
--         ext i
--         simp
--         intro hiB hc
--         subst hc
--         tauto
--       rw [this] at h₀
--       tauto
--     · intro haS
--       let S₀ := S ∩ Finset.filter (fun k => k.1 < n) univ
--       let ob₀ : Finset (Fin n) → Finset (Finset (Fin n)) := fun A =>
--         {C | {k : Fin (n+1) | ∃ hk : k.1 < n, ⟨k.1,hk⟩ ∈ C}.toFinset ∈
--           ob {k : Fin (n+1) | ∃ hk : k.1 < n, ⟨k.1,hk⟩ ∈ A}}
--       have := hn ob₀ (Fin.last n)
--       sorry

theorem canon₂_C5Strong {n : ℕ} (A B : Finset <| Fin n) : C5Strong <| canon₂ A B := by
  unfold canon₂
  intro X Y Z h₀ h₁
  simp at *
  by_cases H : X ∩ B = ∅
  · rw [H] at h₀ h₁ ⊢
    simp at *
  · rw [if_neg H] at h₀ h₁ ⊢
    by_cases H₀ : X ∩ A = ∅
    rw [H₀] at h₀ h₁ ⊢
    simp at *
    intro i hi
    simp
    constructor
    apply h₀
    tauto
    apply h₁
    tauto
    rw [if_neg H₀] at h₀ h₁ ⊢
    simp at *
    intro i hi
    simp
    constructor
    apply h₀
    tauto
    apply h₁
    tauto



lemma hasOne {X : Finset (Fin 2)} (h : 0 ∈ X) :
    X = {0} ∨ X = {0,1} := by
      by_cases H : 1 ∈ X
      right
      ext j
      simp
      fin_cases j
      simp
      tauto
      simp
      tauto
      left
      ext j
      simp
      fin_cases j
      simp
      tauto
      simp
      tauto

lemma hasOne₃general {X : Finset (Fin 3)} {a₀ a₁ a₂ : Fin 3}
    (ha : univ = {a₀,a₁,a₂})
    (h : a₀ ∈ X) :
    X = {a₀} ∨ X = {a₀,a₁} ∨ X = {a₀,a₂} ∨ X = {a₀,a₁,a₂}:= by
      have three (j : Fin 3) : j = a₀ ∨ j = a₁ ∨ j = a₂ := by
        have : j ∈ univ := by simp
        rw [ha] at this
        simp at this
        tauto

      by_cases H₁ : a₁ ∈ X
      by_cases H₂ : a₂ ∈ X
      right
      right
      right
      ext j
      simp
      have hun : X = univ := by
        ext b
        rw [ha]
        simp
        constructor
        intro hb
        have : b ∈ univ := by simp
        rw [ha] at this
        simp at this
        tauto
        intro hb
        cases hb with
        | inl h => subst h;tauto
        | inr h => cases h with
          | inl h => subst h;tauto
          | inr h => subst h;tauto
      fin_cases j <;> (simp; rw [hun,ha]; simp)


      right
      left
      ext j
      simp
      constructor
      intro hj
      cases three j with
      | inl h => tauto
      | inr h => cases h with
        |inl h => subst h;right;rfl
        |inr h => subst h;tauto
      intro h
      cases h with
      | inl h => subst h;tauto
      | inr h => subst h;tauto
      by_cases H₂ : a₂ ∈ X
      right
      right
      left
      ext j
      simp

      cases three j with
      | inl h => subst h;tauto
      | inr h => cases h with
        |inl h =>
          subst h;simp_all;constructor;contrapose! H₁;subst H₁;tauto
          contrapose! H₁;subst H₁;tauto
        |inr h => subst h;tauto

      left
      ext j
      simp
      cases three j with
      | inl h => subst h;tauto
      | inr h => cases h with
        |inl h =>
          subst h;simp_all;contrapose! H₁;subst H₁;tauto
        |inr h => subst h;simp_all;contrapose! H₁;subst H₁;tauto


lemma hasOne₃ {X : Finset (Fin 3)} (h : 0 ∈ X) :
    X = {0} ∨ X = {0,1} ∨ X = {0,2} ∨ X = {0,1,2}:= by
      by_cases H₁ : 1 ∈ X
      by_cases H₂ : 2 ∈ X
      right
      right
      right
      ext j
      simp
      fin_cases j
      simp
      tauto
      simp
      tauto
      simp
      tauto
      right
      left
      ext j
      simp
      fin_cases j
      simp
      tauto
      simp
      tauto
      simp
      tauto
      by_cases H₂ : 2 ∈ X
      right
      right
      left
      ext j
      simp
      fin_cases j
      simp
      tauto
      simp
      tauto
      simp
      tauto
      left
      ext j
      simp
      fin_cases j
      simp
      tauto
      simp
      tauto
      simp
      tauto


  -- let ABC be given with X=A∪B, Y=A, Z=A∪B∪C,
  -- then
  -- This version of D5 is easier to work with here:
  -- have d5'' : ∀ A B C, A ∈ ob (A ∪ B) →
  --     C \ (A ∪ B) ∪ A ∈ ob (A ∪ B ∪ C) := by
  --   intro A B C h₀
  --   let X := A ∪ B
  --   let Y := A
  --   let Z := A ∪ B ∪ C
  --   have := d5 X Y Z (by unfold X Y;simp) h₀
  --     (by unfold X Z;simp;intro i;simp;tauto)
  --   unfold X Y Z at this
  --   convert this using 1
  --   ext;simp;tauto

theorem fixD5 {n : ℕ} {ob : Finset (Fin n) → Finset (Finset (Fin n))}
  (d5 : D5 ob) (A B C : Finset (Fin n)) :
  A ∩ B ∩ C ∈ ob (A ∩ B) → A \ (A ∩ B) ∪ A ∩ B ∩ C ∈ ob A := by
    intro h₀
    let X := A ∩ B
    let Y := A ∩ B ∩ C
    let Z := A
    have := d5 X Y Z (by unfold X Y;intro;simp;tauto) h₀
      (by unfold X Z;simp)
    unfold X Y Z at this
    convert this using 1
open Classical


lemma canon_eq_canon₂ {n : ℕ} {A : Finset (Fin n)} :
  canon A = canon₂ A A := by
    ext X Y
    unfold canon canon₂
    simp




lemma canon₂_eq_canon₂' {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) :
  canon₂ A B = canon₂' A B ∅ := rfl

def canon₂_II {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) :
    Finset α → Finset (Finset α) :=
  fun X ↦ ite (X ∩ B = ∅) ∅ (
      ite (X ∩ A = ∅)
      (filter (fun Y ↦ X ∩ B = X ∩ Y) univ)
      (filter (fun Y ↦ X ∩ A = X ∩ Y) univ)
  )

theorem canon₂_II_C5Strong {n : ℕ} (A B : Finset <| Fin n) : C5Strong <| canon₂_II A B := by
  unfold canon₂_II
  intro X Y Z h₀ h₁
  simp at *
  by_cases H : X ∩ B = ∅
  · rw [H] at h₀ h₁ ⊢
    simp at *
  · rw [if_neg H] at h₀ h₁ ⊢
    by_cases H₀ : X ∩ A = ∅
    rw [H₀] at h₀ h₁ ⊢
    simp at *
    have : X ∩ B = (X ∩ B) ∩ (X ∩ B) := by simp
    rw [this]
    nth_rewrite 1 [h₀]
    rw [h₁]
    ext
    simp
    tauto
    rw [if_neg H₀] at h₀ h₁ ⊢
    simp at *
    have : X ∩ A = (X ∩ A) ∩ (X ∩ A) := by simp
    rw [this]
    nth_rewrite 1 [h₀]
    rw [h₁]
    ext
    simp
    tauto

theorem canon₂_II_subset_canon₂
    {α : Type*} [Fintype α] [DecidableEq α] (A B X : Finset α) :
    canon₂_II A B X ⊆ canon₂ A B X := by
  unfold canon₂_II canon₂
  intro Y
  split_ifs
  tauto
  · simp
    intro h
    rw [h]
    simp
  · simp
    intro h
    rw [h]
    simp

theorem canon_II_is_canon₂_II  {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
    canon_II A = canon₂_II A A := by
  unfold canon_II canon₂_II
  simp
  ext X Y
  aesop

/--
canon₂_II says that only "perfect" scenarios are obligatory,
whereas canon₂ is permissive.
canon₂General captures the idea of being somewhere in between.
For example perhaps
"Be law-abiding or cheat on your taxes" is not obligatory but
"Be law-abiding or speed on the freeway" is obligatory.
Note that
canon₂_II fails F5 and passes E5 and
canon₂ fails E5 and passes F5.
Perhaps some canon₂General can pass both?
Perhas A5 B5 C5 hold for any canon₂General
A5 yes, see below.
B5 no, clearly
C5 no, clearly
what's interesting however is those `ob` that do satisfy
canon₂General and also B5, C5

maybe what we can show is that no model satisfying canon₂General
can satisfy all CJ2022's requirements.
-/

def canon₂General {α : Type*} [Fintype α] [DecidableEq α]
  (ob : Finset α → Finset (Finset α)) :=
  ∃ A B, ∀ X, canon₂_II A B X ⊆ ob X ∧ ob X ⊆ canon₂ A B X

theorem subset_canon₂_A5 {α : Type*} [Fintype α] [DecidableEq α]
  (ob : Finset α → Finset (Finset α)) (P : Finset <| Finset α) (hP : ∅ ∉ P)
  (h : ∃ A B, ∀ X, ob X ⊆ canon₂' A B P X) : A5 ob := by
  obtain ⟨A,B,h₀⟩ := h
  intro X
  specialize h₀ X
  unfold canon₂' at h₀
  by_cases H₀ : X ∩ B = ∅
  · rw [H₀] at h₀
    simp at h₀
    contrapose! hP
    apply h₀ hP
  · repeat rw [if_neg H₀] at h₀
    by_cases H₁ : X ∩ A = ∅
    · rw [H₁] at h₀
      simp at h₀
      intro hc
      have := h₀
      have : ∅ ∈ filter (fun T ↦ X ∩ B ⊆ T) univ := by
        have := this hc
        exact this
      simp at this
      exact H₀ this
    · repeat rw [if_neg H₁] at h₀
      intro hc
      have := h₀
      have : ∅ ∈ filter (fun T ↦ X ∩ A ⊆ T) univ := by
        have := this hc
        exact this
      simp at this
      exact H₁ this

/-- The canon₂_II models satisfy axiom 5(a). -/
theorem canon₂_II_A5  {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : A5 (canon₂_II A B) :=
  subset_canon₂_A5 (canon₂_II A B) ∅ (by simp) ⟨A, B, canon₂_II_subset_canon₂ A B⟩

/-- The canon₂_II models satisfy axiom 5(b). -/
theorem canon₂_II_B5  {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : B5 (canon₂_II A B) := by
  unfold B5 canon₂_II
  intro X Y Z h₀
  split_ifs with h₁ h₂
  aesop

  intro h
  simp at *
  rw [h]
  convert h₀ using 0
  nth_rewrite 1 [inter_comm]
  nth_rewrite 2 [inter_comm]
  tauto
  simp

  intro h
  rw [h]
  convert h₀ using 0
  nth_rewrite 1 [inter_comm]
  nth_rewrite 2 [inter_comm]
  tauto


/-- The canon₂_II models satisfy axiom 5(c). -/
theorem canon₂_II_C5  {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : C5 (canon₂_II A B) := by
  unfold C5 canon₂_II
  intro X Y Z h₀ h₁ h₂
  split_ifs at * with h₃ h₄
  any_goals (simp only [
    not_mem_empty, mem_filter, mem_univ, true_and] at h₀ h₁ ⊢)
    <;> exact eq_inter_inter h₀ h₁

def canon₂'' {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) :
    Finset α → Finset (Finset α) :=
  fun X ↦ ite (X ∩ B = ∅) (univ \ {∅}) (
      ite (X ∩ A = ∅)
      (filter (fun T ↦ X ∩ B ⊆ T) univ)
      (filter (fun T ↦ X ∩ A ⊆ T) univ)
  )

def canon₂''' {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) :
    Finset α → Finset (Finset α) :=
  fun X ↦ ite (X ∩ B = ∅) ({T | T ≠ ∅ ∧ X ⊆ T}.toFinset) (
      ite (X ∩ A = ∅)
      ({T | X ∩ B ⊆ T}.toFinset)
      ({T | X ∩ A ⊆ T}.toFinset)
  )

-- theorem test' {n : ℕ} {A : Finset (Fin n)} :
--     E5 (canon₂''' A A) := by
--   intro X Y Z h₀ h₁ h₂
--   unfold canon₂''' at *
--   by_cases H₀ : X ∩ A = ∅
--   · rw [H₀] at h₁
--     simp at h₁
--     have h₃ : Y ∩ A = ∅ := by
--       apply subset_empty.mp
--       apply subset_trans
--       show Y ∩ A ⊆ X ∩ A
--       exact inter_subset_inter h₀ fun ⦃a⦄ a ↦ a
--       rw [H₀]
--     rw [h₃]
--     simp
--     tauto
--   · repeat rw [if_neg H₀] at h₁
--     by_cases h₃ : Y ∩ A = ∅
--     · rw [h₃]
--       simp at h₁ ⊢
--       -- FAILS!
--       contrapose! h₂
--       rw [h₂]
--       simp
--     · rw [if_neg h₃]
--       by_cases H₁ : Y ∩ A = ∅
--       · rw [H₁]
--         simp
--       · rw [if_neg H₁]
--         simp
--         simp at h₁
--         apply subset_trans
--         show Y ∩ A ⊆ X ∩ A
--         apply inter_subset_inter (by tauto) (by simp)
--         tauto



-- theorem test' {n : ℕ} {A B : Finset (Fin n)} (hAB : A ⊆ B):
--     E5 (canon₂'' A B) := by
--   intro X Y Z h₀ h₁ h₂
--   unfold canon₂'' at *
--   by_cases H₀ : X ∩ A = ∅
--   · rw [H₀] at h₁
--     simp at h₁
--     have h₃ : Y ∩ A = ∅ := by
--       apply subset_empty.mp
--       apply subset_trans
--       show Y ∩ A ⊆ X ∩ A
--       exact inter_subset_inter h₀ fun ⦃a⦄ a ↦ a
--       rw [H₀]
--     rw [h₃]
--     simp
--     by_cases H₁ : Y ∩ B = ∅
--     rw [H₁]
--     simp
--     contrapose! h₂
--     rw [h₂]
--     simp
--     rw [if_neg H₁]
--     simp
--     by_cases H₂ : X ∩ B = ∅
--     · rw [H₂] at h₁
--       simp at h₁
--       exfalso
--       apply H₁
--       apply subset_empty.mp
--       apply subset_trans
--       show Y ∩ B ⊆ X ∩ B
--       exact inter_subset_inter h₀ fun ⦃a⦄ a ↦ a
--       rw [H₂]
--     · rw [if_neg H₂] at h₁
--       simp at h₁
--       apply subset_trans
--       show Y ∩ B ⊆ X ∩ B
--       exact inter_subset_inter h₀ fun ⦃a⦄ a ↦ a
--       exact h₁
--   · rw [if_neg H₀] at h₁
--     by_cases h₃ : Y ∩ A = ∅
--     · rw [h₃]
--       simp
--       have : X ∩ B ≠ ∅ := by
--         contrapose! H₀
--         apply subset_empty.mp
--         apply subset_trans
--         show X ∩ A ⊆ X ∩ B
--         exact inter_subset_inter (fun ⦃a⦄ a ↦ a) hAB
--         rw [H₀]
--       rw [if_neg this] at h₁
--       simp at h₁
--       by_cases H₁ : Y ∩ B = ∅
--       rw [H₁]
--       simp
--       contrapose! h₂
--       rw [h₂]
--       simp

--       rw [if_neg H₁]
--       simp
--       -- FAILS!
--       contrapose! h₂

--       rw [h₂]
--       simp
--     · rw [if_neg h₃]
--       by_cases H₁ : Y ∩ A = ∅
--       · rw [H₁]
--         simp
--       · rw [if_neg H₁]
--         simp
--         simp at h₁
--         apply subset_trans
--         show Y ∩ A ⊆ X ∩ A
--         apply inter_subset_inter (by tauto) (by simp)
--         tauto


recall not_canon_E5
/-- Whereas `canon` failed E5, we now see that just changing what
is required when no good options are available fixes that!
But it's only for A=B so not that important.
And in fact, this means that we have deontic explosion for `canon''`
and so it is perhaps mild evidence that making nothing obligatory when there are no
good options, as in `canon`, is best after all.

HOWEVER the canon₂ and canon₂_II models satisfy the original strong axiom
from my 1996 term paper, which means that my argument from there may be a
devastasting strike against them!?
 -/
theorem test {n : ℕ} {A : Finset (Fin n)} :
    E5 (canon₂'' A A) := by
  intro X Y Z h₀ h₁ h₂
  unfold canon₂'' at *
  by_cases H₀ : X ∩ A = ∅
  · rw [H₀] at h₁
    simp at h₁
    have h₃ : Y ∩ A = ∅ := by
      apply subset_empty.mp
      apply subset_trans
      show Y ∩ A ⊆ X ∩ A
      exact inter_subset_inter h₀ fun ⦃a⦄ a ↦ a
      rw [H₀]
    rw [h₃]
    simp
    tauto
  · rw [if_neg H₀] at h₁
    by_cases h₃ : Y ∩ A = ∅
    · rw [h₃]
      simp
      contrapose! h₂
      rw [h₂]
      simp
    · rw [if_neg h₃]
      by_cases H₁ : Y ∩ A = ∅
      · rw [H₁]
        simp
      · rw [if_neg H₁]
        simp
        simp at h₁
        apply subset_trans
        show Y ∩ A ⊆ X ∩ A
        apply inter_subset_inter (by tauto) (by simp)
        tauto


/-- Mild conditions on `B` work here, that generalize A=B. (June 2, 2025) -/
theorem many_not_canon₂_E5_P {n : ℕ} {A B : Finset (Fin n)}
    (P : Finset <|Finset <| Fin n) (hP : univ ∉ P)
    (h₄ : B ≠ ∅) (h₀ : A ∪ B ≠ univ) :
  ¬ E5 (canon₂' A B P) := by
  have ⟨Y,h₇,h₈,h₉⟩ : ∃ Y, Y ≠ ∅ ∧ Y ∩ B = ∅ ∧ Y ∩ A = ∅ := by
    use (A ∪ B)ᶜ
    constructor
    contrapose! h₀
    exact (compl_eq_empty_iff (A ∪ B)).mp h₀
    constructor
    · ext;simp
    · ext;simp;tauto
  unfold E5 canon₂'
  push_neg
  use univ, Y, univ -- X and Z were univ, Y were Aᶜ
  constructor
  . simp
  . constructor
    . simp
      rw [if_neg h₄]
      by_cases H : A = ∅
      · rw [H]
        simp
      · rw [if_neg H]
        simp
    . simp
      rw [h₉]
      simp
      constructor
      · simp at h₇
        tauto
      rw [h₈]
      simp
      exact hP


/-- Mild conditions on `B` work here, that generalize A=B. (June 2, 2025) -/
theorem many_not_canon₂_E5 {n : ℕ} {A B : Finset (Fin n)}
    (h₄ : B ≠ ∅) (h₀ : A ∪ B ≠ univ) :
  ¬ E5 (canon₂ A B) := by
  rw [canon₂_eq_canon₂']
  refine many_not_canon₂_E5_P ∅ ?_ h₄ h₀
  simp


theorem many_not_canon_E5 {n : ℕ} {A : Finset (Fin n)}
    (h₀ : A ≠ ∅) (h₁ : A ≠ univ):
  ¬ E5 (canon A) := by
  rw [canon_eq_canon₂]
  refine many_not_canon₂_E5 h₀ ?_
  simp
  exact h₁


/-- The canon₂_II models satisfy axiom 5(e) if `A ⊆ B`. -/
theorem canon₂_II_E5 {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Finset α} (h : A ⊆ B) : E5 (canon₂_II A B) := by
  unfold canon₂_II
  intro X Y Z h₀ h₁ h₂
  simp at *
  split_ifs at * with h₃ _ _ h₄ _ _ _ h₅
  any_goals (
    simp only [mem_filter, mem_univ, true_and, not_mem_empty] at h₁ ⊢)
  . exact h₂ <| inter_empty_of_restrict h₀ h₃ h₁
  . exact h₂ <| inter_empty_of_restrict₂ h h₀ h₃ (by rw [h₁])
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
  all_goals (
    simp only [inter_assoc, ne_eq, mem_filter, mem_univ, true_and] at *)
  . exact h₀ ▸ eq_inter_inter_of_inter h₀ h₁
  . rw [inter_comm] at h₃
    apply False.elim <| h₂ <| inter_inter_eq_empty' h₃ h₀ h₁
  · simp at h₁
  . apply False.elim <| h₂ <| inter_inter_eq_empty h₄ h₀
  . exact h₀ ▸ eq_inter_inter_of_inter h₀ h₁








/-- The canon₂ models satisfy axiom 5(a). -/
theorem canon₂_A5  {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : A5 (canon₂ A B) := by
  intro X
  unfold canon₂
  split_ifs with h₀ h₁
  any_goals (simp only [mem_filter, mem_univ, subset_empty,
    true_and,not_mem_empty, not_false_eq_true])
  · exact h₀
  · exact h₁



/-- The canon₂ models satisfy axiom 5(b). -/
theorem canon₂_B5 {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : B5 (canon₂ A B) := by
  unfold B5 canon₂
  intro X Y Z h₀ h₁

  split_ifs with g₀ g₁
  rw [g₀] at h₁
  simp at h₁
  rw [if_neg g₀] at h₁
  rw [g₁] at h₁
  simp at h₁
  simp
  intro i hi
  suffices i ∈ Z ∩ X by simp at this;tauto
  rw [← h₀]
  simp
  constructor
  apply h₁
  tauto
  simp at hi
  tauto
  simp
  rw [if_neg g₀] at h₁
  rw [if_neg g₁] at h₁
  simp at h₁
  intro i hi
  suffices i ∈ Z ∩ X by simp at this;tauto
  rw [← h₀]
  simp
  constructor
  apply h₁
  tauto
  simp at hi
  tauto




/-- The canon₂ models satisfy axiom 5(c). -/
theorem canon₂_C5 {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : C5 (canon₂ A B) := by
  intro X Y Z h₀ h₁ h₂
  unfold canon₂ at *
  split_ifs at * with h₁
  . tauto
  repeat simp at *;exact subset_inter h₀ h₁

/-- The canon₂ models satisfy axiom 5(d). -/
theorem canon₂_D5 {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Finset α} (h : A ⊆ B) : D5 (canon₂ A B) := by
  unfold D5 canon₂
  intro X Y Z _ h₁ h₂
  split_ifs at * with h₃ h₄ h₅ h₆ h₇ h₈
  . simp at h₁
  repeat exact (h₄ <| subset_empty.mp
      <| (inter_subset_inter h₂ (subset_refl _)).trans
      <| subset_empty.mpr h₃).elim
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


theorem theorem10_1996_related : ∃ (ob : Finset (Fin 3) → Finset (Finset (Fin 3))),
    (∀ X, 0 ∈ X → {0} ∈ ob X) ∧
    (A5 ob) ∧ (C5Strong ob) ∧ (B5 ob) ∧ (D5 ob) ∧ ¬ E5 ob := by
  use canon {0}
  constructor
  . intro X hX
    unfold canon
    have : X ∩ {0} ≠ ∅ := by
      intro hc
      have : 0 ∈ X ∩ {0} := by
        simp;tauto
      rw [hc] at this
      simp at this
    rw [if_neg this]
    simp
    tauto
  constructor
  rw [canon_eq_canon₂]
  apply canon₂_A5
  constructor
  rw [canon_eq_canon₂]
  exact canon₂_C5Strong {0} {0}
  constructor
  rw [canon_eq_canon₂]
  exact canon₂_B5 {0} {0}
  constructor
  rw [canon_eq_canon₂]
  exact canon₂_D5 fun ⦃a⦄ a ↦ a
  apply many_not_canon_E5
  simp
  simp
  intro hc
  have : (1 : Fin 3) ∈ univ := by simp
  rw [← hc] at this
  simp at this


  /- what does it say about A,B that such X₀,Y₀,Z₀ exist?
  certainly B not subset of A. But then very broadly,
  If we take X,Y,Z generic w.r.t. A,B then let
  X₀ = X \ A
  Y₀ = univ
  Z₀ = Z ∪ A.

  If we take Y=univ:
  (h₆ : ¬X₀ ∩ Z₀ = ∅)
  (h₀ : X₀ ∩ A = ∅)
  (h₃ : B ≠ ∅)

  (h₈ : ¬X₀ ∩ B ⊆ Z₀)

  (h₅ : A ⊆ Z₀)
  (h₄ : A ≠ ∅)



  -/

/-- Based on the fact that A = {2}, B={1,2},
  X₀={0,1}, Y₀=univ, Z₀={0,2}
  works.
-/
theorem many_not_canon₂_G {n : ℕ} {A B : Finset (Fin (n + 3))}
  (h₄' : A ≠ ∅)
  (h₀' : A ∪ B ≠ univ)
  (h₁' : B \ A ≠ ∅) :
  ¬ G5 (canon₂ A B) := by

  have h₃' : B ≠ ∅ := by
    contrapose! h₁'
    rw [h₁']
    simp
  have h₂ : ¬ B \ A ⊆ (A ∪ B)ᶜ := by
    contrapose! h₁'
    ext i
    simp
    intro hi
    by_contra H
    have : i ∈ B \ A := by simp;tauto
    have := h₁' this
    simp at this
    exact this.2 hi
  have h₁ : (A ∪ B)ᶜ \ A ≠ ∅ := by
    contrapose! h₀'
    ext i
    simp
    by_contra H
    simp at H
    have : i ∈ (∅ : Finset (Fin (n+3))) := by
      rw [← h₀']
      simp
      tauto
    simp at this
  let Z := (A ∪ B)ᶜ
  have h₈ : ¬(univ \ A) ∩ B ⊆ Z ∪ A := by
    contrapose! h₂
    intro i hi
    have : i ∈ univ \ A ∩ B := by simp at hi ⊢;tauto
    have := h₂ this
    simp at this
    cases this with
    | inl h => unfold Z at h;tauto
    | inr h => simp at this;tauto
  have h₆ : (univ \ A) ∩ (Z ∪ A) ≠ ∅ := by
    have ⟨z,hz⟩ : ∃ z, z ∈ Z \ A := by
      unfold Z
      refine Nonempty.exists_mem ?_
      exact nonempty_iff_ne_empty.mpr h₁
    intro hc
    have : z ∈ (∅ : Finset (Fin (n+3))) := by
      rw [← hc]
      simp
      simp at hz
      tauto
    simp at this
  let Y₀ :=  (univ : Finset (Fin (n+3)))
  let X₀ := univ \ A
  let Z₀ := Z ∪ A
  have h₆ : ¬X₀ ∩ (Y₀ ∩ Z₀) = ∅ := by
    unfold X₀ Y₀ Z₀
    simp
    tauto
  have h₃ : Y₀ ∩ B ≠ ∅ := by
    unfold Y₀
    simp
    tauto
  have h₈ : ¬X₀ ∩ B ⊆ Z₀ := by
    unfold X₀ Z₀
    tauto
  have h₅ : Y₀ ∩ A ⊆ Z₀ := by
    unfold Z₀
    intro;simp;tauto
  have h₀ : X₀ ∩ A = ∅ := by
    unfold X₀
    simp
  have h₂' : X₀ ∩ B ⊆ Y₀ := by
    unfold Y₀
    simp
  have h₄ : Y₀ ∩ A ≠ ∅ := by
    unfold Y₀
    simp;tauto
  have h₇ : ¬X₀ ∩ B ⊆ Y₀ ∩ Z₀ := by
    contrapose! h₈
    apply subset_trans h₈
    simp
  have h₁ : X₀ ∩ B ≠ ∅ := by
    contrapose! h₇
    rw [h₇]
    simp
  . unfold G5
    push_neg
    use X₀, Y₀, Z₀
    simp
    constructor
    unfold canon₂
    split_ifs with h₀
    . simp only [not_mem_empty]
      exact h₁ h₀
    . simp
      exact h₂'
    constructor
    unfold canon₂
    split_ifs with g₀
    . exfalso; exact h₃ g₀
    . simp;exact h₅
    . constructor
      · exact h₆
      · unfold canon₂
        rw [if_neg h₁]
        rw [h₀]
        simp
        exact h₇


theorem infinitely_many_not_canon₂_G {n : ℕ}:
    ∃ (A B : Finset (Fin (n + 3))), A ⊆ B ∧ ¬ G5 (canon₂ A B) := by
  use {2}, {1,2}
  have : {0, 1} ∩ {2} = (∅ : Finset (Fin (n+3))):= by
    ext a;simp
    intro h
    cases h with
    | inl h => subst h;exact ne_of_beq_false rfl
    | inr h => subst h;exact ne_of_beq_false rfl
  constructor
  . simp
  . unfold G5
    push_neg
    use {0, 1}, univ, {0, 2}
    simp
    constructor
    unfold canon₂
    split_ifs with h₀
    . simp only [not_mem_empty]
      exact ne_of_beq_false rfl h₀
    . simp at *

    constructor
    unfold canon₂
    split_ifs with g₀ g₁
    . simp at g₀
    . simp at g₁
    . simp
    · unfold canon₂
      simp
      rw [this]
      simp
      exact ne_of_beq_false rfl


/-- canon₂ models do not satisfy Axiom 5(g).
 Since canon₂_II does satisfy 5(g) (see `canon₂_II_G5`)
 5(g) belongs firmly in the II category. -/
theorem not_canon₂_G:
    ∃ n:ℕ, ∃ (A B : Finset (Fin n)), A ⊆ B ∧ ¬ G5 (canon₂ A B) := by
  use 3, {2},
         {1,2}
  constructor
  . trivial
  . unfold G5
    push_neg
    use {0, 1}, univ, {0, 2}
    simp
    constructor
    unfold canon₂
    split_ifs with h₀ h₁
    . simp only [not_mem_empty]
      exact ne_of_beq_false rfl h₀
    . simp at *
    . contrapose h₁; simp

    constructor
    unfold canon₂
    split_ifs with g₀ g₁
    . simp at g₀
    . simp at g₁
    . simp
    · unfold canon₂
      simp


/-- The canon₂ models satisfy axiom 5(f). -/
lemma canon₂_F5 {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : F5 (canon₂ A B) := by
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
def CJ_all_2022 {α : Type*} [Fintype α] [DecidableEq α]
    (ob : Finset α → Finset (Finset α)) :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧ D5 ob ∧ E5 ob ∧ F5 ob ∧ G5 ob

def CJ_noE_2022 {α : Type*} [Fintype α] [DecidableEq α]
    (ob : Finset α → Finset (Finset α)) :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧ D5 ob ∧ F5 ob ∧ G5 ob

/-- This could also be called CJ_2022. -/
def CJ_noD_2022 {α : Type*} [Fintype α] [DecidableEq α]
    (ob : Finset α → Finset (Finset α)) :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧ E5 ob ∧ F5 ob ∧ G5 ob

def CJ_noDF_2022 {α : Type*} [Fintype α] [DecidableEq α]
    (ob : Finset α → Finset (Finset α)) :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧ E5 ob ∧ G5 ob

def CJ_noEG_2022 {α : Type*} [Fintype α] [DecidableEq α]
    (ob : Finset α → Finset (Finset α)) :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧ D5 ob ∧ F5 ob

theorem CJ_no_DF_canon₂_II {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Finset α} (h : A ⊆ B) : CJ_noDF_2022 (canon₂_II A B) := by
  use canon₂_II_A5 _ _, canon₂_II_B5 _ _, canon₂_II_C5 _ _,
      canon₂_II_E5 h,   canon₂_II_G5 _ _

theorem CJ_no_EG_canon₂ {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Finset α} (h : A ⊆ B) : CJ_noEG_2022 (canon₂ A B) := by
  use canon₂_A5 _ _, canon₂_B5 _ _, canon₂_C5 _ _,
      canon₂_D5 h,   canon₂_F5 _ _

/--
A modest generalization of `canon_II_F5`.
-/
theorem generalize_F5_canon_II {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Finset α}
    (hBA :  B ⊆ A) :
    F5 (canon₂_II A B) := by
  unfold canon₂_II
  intro X Y Z h₀ h₁
  simp at h₀ h₁ ⊢
  by_cases H₀ : Y ∩ B = ∅
  · rw [H₀] at h₀
    simp at h₀
  · rw [if_neg H₀] at h₀
    by_cases H₁ : Y ∩ A = ∅
    · rw [H₁] at h₀
      simp at h₀
      have : (Y ∪ Z) ∩ B ≠ ∅ := by
        contrapose! H₀
        apply subset_empty.mp
        apply subset_trans
        show Y ∩ B ⊆ (Y ∪ Z) ∩ B
        intro;simp;tauto
        rw [H₀]
      rw [if_neg this]
      by_cases H₂ : Z ∩ A = ∅
      · have :  (Y ∪ Z) ∩ A = ∅ := by
          repeat rw [union_inter_distrib_right]
          rw [H₁, H₂]
          simp
        rw [this]
        simp
        rw [H₂] at h₁
        simp at h₁
        by_cases H₃ : Z ∩ B = ∅
        · rw [H₃] at h₁
          simp at h₁
        · rw [if_neg H₃] at h₁
          simp at h₁
          repeat rw [union_inter_distrib_right]
          rw [h₀, h₁]
      · have : (Y ∪ Z) ∩ A ≠ ∅ := by
          contrapose! H₂
          apply subset_empty.mp
          apply subset_trans
          show Z ∩ A ⊆ (Y ∪ Z) ∩ A
          intro;simp;tauto
          rw [H₂]
        rw [if_neg this]
        simp
        by_cases H₃ : Z ∩ B = ∅
        · rw [H₃] at h₁
          simp at h₁
        · rw [if_neg H₃, if_neg H₂] at h₁
          simp at h₁
          repeat rw [union_inter_distrib_right]
          rw [H₁]
          simp
          rw [← h₁]
          rw [← h₀]
          simp
          exfalso
          apply H₀
          apply subset_empty.mp
          rw [← H₁]
          exact inter_subset_inter (fun ⦃a⦄ a ↦ a) hBA
    · rw [if_neg H₁] at h₀
      simp at h₀
      have :  (Y ∪ Z) ∩ B ≠ ∅ := by
        contrapose! H₀
        apply subset_empty.mp
        apply subset_trans
        show Y ∩ B ⊆ (Y ∪ Z) ∩ B
        intro;simp;tauto
        rw [H₀]
      rw [if_neg this]
      have : (Y ∪ Z) ∩ A ≠ ∅ := by
          contrapose! H₁
          apply subset_empty.mp
          apply subset_trans
          show Y ∩ A ⊆ (Y ∪ Z) ∩ A
          intro;simp;tauto
          rw [H₁]
      rw [if_neg this]
      simp
      by_cases H₂ : Z ∩ B = ∅
      · rw [H₂] at h₁
        simp at h₁
      · rw [if_neg H₂] at h₁
        by_cases H₃ : Z ∩ A = ∅
        · exfalso
          apply H₂
          apply subset_empty.mp
          apply subset_trans
          show Z ∩ B ⊆ Z ∩ A
          exact inter_subset_inter (fun ⦃a⦄ a ↦ a) hBA
          rw [H₃]
        · rw [if_neg H₃] at h₁
          simp at h₁
          repeat rw [union_inter_distrib_right]
          rw [h₀, ← h₁]

theorem canon_II_F5  {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) : F5 (canon_II A) := by
  have := @generalize_F5_canon_II α _ _ A A (by simp)
  convert this using 1
  exact canon_II_is_canon₂_II A

-- theorem canon_II_F5  {α : Type*} [Fintype α] [DecidableEq α]
--     (A : Finset α) : F5 (canon_II A) := by
--   -- must prove directly since F fails for canon₂_II !
--     unfold F5 canon_II
--     intro _ _ _ h₀ h₁
--     split_ifs at * with h₂ h₃ h₄ h₅
--     repeat exact h₀
--     · exact h₁
--     · simp only [mem_filter, mem_univ,
--         true_and, not_mem_empty] at h₀ h₁ ⊢
--       rw [union_inter_distrib_right, union_eq_empty] at h₂
--       exact h₃ h₂.1
--     repeat simp at h₀
--     · simp at h₁
--     · simp at *;
--       rw [union_inter_distrib_right,h₀,h₁,union_inter_distrib_right]

theorem CJ_noD_canon_II {α : Type*} [Fintype α] [DecidableEq α]
    {A : Finset α} : CJ_noD_2022 (canon_II A) := by
  rw [canon_II_symm]
  have := canon₂_II_A5 A A
  have := canon₂_II_B5 A A
  have := canon₂_II_C5 A A
  have := canon_II_E5 A
  have := canon_II_F5 A
  have := canon₂_II_G5 A A
  rw [canon_II_symm] at *
  unfold canon₂_II at *
  simp only [ite_self] at *
  repeat use (by tauto)


theorem canon_G {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
    G5 (canon A) := by
  unfold canon G5
  intro X Y Z h₀ h₁ h₂
  simp only at *
  split_ifs at *
  any_goals (simp only [not_mem_empty] at *)
  simp only [mem_filter, mem_univ, true_and, mem_inter] at h₀ h₁ ⊢
  exact subset_inter_within h₀ h₁

theorem CJ_noE_canon {α : Type*} [Fintype α] [DecidableEq α]
    {A : Finset α} : CJ_noE_2022 (canon A) := by
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
theorem CJ_all_canon_univ {α : Type*} [Fintype α] [DecidableEq α] :
    CJ_all_2022 (canon (univ: Finset α)) := by
  have R := (@coincidence α _ _) ▸ @canon_II_E5 α _ _ univ
  have Q := @CJ_noE_canon α _ _ univ
  unfold CJ_noE_2022 at Q
  unfold CJ_all_2022
  tauto


-- open Classical

/-- Like `observation_5_2` but with Finset instead of Set. -/
def observation_5_2' := fun (X : Finset (Fin 4)) =>
    ite (X ∩ {0,1} = ∅) ({Y | Y ∩ X = {3}} : Finset (Finset (Fin 4)))
      ({Y | Y ∩ X ⊇ {0,1} ∩ X} : Finset (Finset (Fin 4)))



theorem observation_5_2_subset_canon₂ (X : Finset (Fin 4)) :
    canon₂ {0, 1} ({0,1,3} : Finset (Fin 4)) X ⊇ observation_5_2' X := by
  intro Y
  unfold canon₂ observation_5_2'
  intro h
  by_cases H₀ : X ∩ {0, 1, 3} = ∅
  · rw [H₀]
    simp
    have H₁ : X ∩ {0,1} = ∅ := by
      have : X ∩ {0, 1, 3} = X ∩ {0, 1} ∪ X ∩ {3} :=
        inter_union_distrib_left X {0,1} {3}
      rw [this] at H₀
      aesop
    rw [H₁] at h
    simp at h
    have : 3 ∈ ({3} : Finset (Fin 4)) := by aesop
    rw [← h] at this
    simp at this
    have : 3 ∈ X ∩ {0, 1, 3} := by simp;tauto
    rw [H₀] at this
    simp at this
  · rw [if_neg H₀]
    by_cases H₁ :  X ∩ {0, 1} = ∅
    · rw [H₁] at h ⊢
      simp at h ⊢
      have : X ∩ {0, 1, 3} = X ∩ {0, 1} ∪ X ∩ {3} := inter_union_distrib_left X {0,1} {3}
      rw [this] at H₀ ⊢
      rw [H₁] at H₀ ⊢
      simp at H₀ ⊢
      intro i hi
      have : i = 3 := by aesop
      subst this
      suffices 3 ∈ Y ∩ X by simp at this;aesop
      rw [h]
      simp
    · rw [if_neg H₁] at h ⊢
      simp at h ⊢
      apply subset_trans
      show X ∩ {0,1} ⊆ Y ∩ X
      nth_rewrite 1 [inter_comm]
      exact h
      aesop

theorem canon₂_II_subset_observation_5_2 (X : Finset (Fin 4)) :
    canon₂_II {0, 1} ({0,1,3} : Finset (Fin 4)) X ⊆ observation_5_2' X := by
  intro Y
  unfold canon₂_II observation_5_2'
  intro h
  by_cases H₀ : X ∩ {0, 1} = ∅
  · rw [H₀]
    simp
    by_cases H₁ : X ∩ {0, 1, 3} = ∅
    · rw [H₁] at h
      simp at h
    · rw [if_neg H₁, H₀] at h
      simp at h
      have : X ∩ {0, 1, 3} = X ∩ {0, 1} ∪ X ∩ {3} :=
        inter_union_distrib_left X {0,1} {3}
      rw [this, H₀] at h
      simp at h
      rw [this] at H₁
      rw [H₀] at H₁
      simp at H₁
      rw [inter_comm]
      rw [← h]
      simp
      contrapose! H₁
      ext i;simp; intro hi hc;subst hc;tauto
  · rw [if_neg H₀] at h ⊢
    have : X ∩ {0, 1, 3} ≠ ∅ := by aesop
    rw [if_neg this] at h
    simp at h ⊢
    rw [inter_comm]
    rw [← h]
    intro a h₀
    rw [inter_comm]
    exact h₀

recall canon₂General
/-- The utility of the definition `canon₂General` may seem questionable
but it is hereby demonstrated: -/
theorem canon₂General_observation_5_2 :
    canon₂General observation_5_2' := by
  unfold canon₂General
  use {0, 1}, ({0,1,3} : Finset (Fin 4))
  intro X
  constructor
  exact canon₂_II_subset_observation_5_2 X
  exact observation_5_2_subset_canon₂ X

theorem observation_5_2_not_subset_canon₂_II :  ∃ (X : Finset (Fin 4)),
    ¬ canon₂_II {0, 1} ({0,1,3} : Finset (Fin 4)) X ⊇ observation_5_2' X := by
  use univ
  intro hc
  unfold canon₂_II observation_5_2' at hc
  simp at hc
  specialize hc (by
    simp
    show (Finset.univ : Finset (Fin 4)) ⊇ {0,1}
    simp
  )
  simp at hc
  have : 2 ∈ ({0,1} : Finset (Fin 4)) := by aesop
  simp at this

theorem canon₂_not_subset_observation_5_2 :  ∃ (X : Finset (Fin 4)),
    ¬ canon₂ {0, 1} ({0,1,3} : Finset (Fin 4)) X ⊆ observation_5_2' X := by
  use {2,3}
  intro hc
  have : {2,3} ∈ canon₂ ({0, 1} : Finset (Fin 4)) {0, 1, 3} {2, 3} := by
    unfold canon₂
    simp
  specialize hc this
  unfold observation_5_2' at hc
  simp at hc

/-- We see that their model is not canon₂ because
 Y ∩ X ⊇ {3} is not the same as Y ∩ X = {3}. 2 may or may not be in. -/
theorem observation_5_2_ne_canon₂ :
  canon₂ {0, 1} ({0,1,3} : Finset (Fin 4)) ≠ observation_5_2' := by
  have := canon₂_not_subset_observation_5_2
  intro hc
  revert this
  simp
  rw [hc]
  simp


example : {0,1,2} ∈ canon₂ ({0,1} : Finset (Fin 4)) {0,1,3} univ := by
  unfold canon₂
  simp

example : {0,1,2} ∈ observation_5_2' univ := by
  unfold observation_5_2'
  simp

/-- We might think that `obs52_fails_E5` above uses stronger versions of E5
than were used in [Kjos-Hanssen 2017], but we can improve it as follows:
-/
example (ob : Finset (Fin 4) → Finset (Finset (Fin 4)))
    (h : ∀ (X : Finset (Fin 4)), ob X ⊆ canon₂ {0,1} {0,1,3} X)
    (H : {0,1,2} ∈ ob univ) :
    ¬ E5weak ob := by
  unfold E5weak
  push_neg
  use {2}, {0,1,2}
  simp
  constructor
  · exact H
  · unfold canon₂ at h
    intro hc
    have := h {2} hc
    simp at this
example : ¬ E5 (canon₂ {0, 1} ({0,1,3} : Finset (Fin 4))) := by
  unfold E5
  push_neg
  use {0,2}, {2}, {2,0}
  unfold canon₂
  simp


/-- For the most part, 5(e) does hold in canon₂ models. -/
theorem many_not_E5_canon₂ {n : ℕ} {A B : Finset (Fin n)}
   (h₀ : A ∩ B ≠ ∅) (h₁ : B ≠ univ) :
    ¬ E5 (@canon₂ (Fin n) _ _ A B) := by
  have ⟨a₀,ha₀⟩ : ∃ a₀, a₀ ∈ A ∩ B := by
    refine Nonempty.exists_mem ?_
    exact nonempty_iff_ne_empty.mpr h₀
  have ha : a₀ ∈ A := by simp at ha₀;tauto
  have h₀ : a₀ ∈ B := by simp at ha₀;tauto
  have ⟨a₂, h₂⟩ : ∃ a₂, a₂ ∉ B := by
    contrapose! h₁
    ext i
    simp
    apply h₁
  have h₃ : {a₂} ∩ B = ∅ := by ext x;simp;intro h;subst h;tauto
  have H₀ : {a₀, a₂} ∩ B ≠ ∅ := by
    have : a₀ ∈ {a₀,a₂} ∩ B := by simp;tauto
    exact ne_empty_of_mem this
  have H₁ : {a₀, a₂} ∩ A ≠ ∅ := by
    have : a₀ ∈ {a₀,a₂} ∩ A := by simp;tauto
    exact ne_empty_of_mem this
  unfold E5
  push_neg
  use {a₀,a₂}, {a₂}, {a₀, a₂}
  unfold canon₂
  simp
  constructor
  · rw [if_neg H₀]
    rw [if_neg H₁]
    simp
  · rw [h₃]
    tauto


/-- F5 fails for certain `ob` that are close to `canon₂_II`. -/
theorem similar_to_canon₂_II_often_fails_F5 {n : ℕ} {a₀ a₁ : Fin n} {A B : Finset (Fin n)}
    (h₀ : a₀ ∈ B) (h₁ : a₁ ∈ B) (h₂ : a₀ ∈ A) (h₃ : a₁ ∉ A)
    (ob : Finset (Fin n) → Finset (Finset (Fin n)))
    (hc₀ : canon₂_II A B {a₀} ⊆ ob {a₀})
    (hc₀' : canon₂_II A B {a₁} ⊆ ob {a₁})
    (hc₁₂ : ob ({a₀} ∪ {a₁}) ⊆ canon₂_II A B ({a₀} ∪ {a₁}))
    -- hc₁₂ does not hold for canon₂ or observation_5_2' so we have no common explanation
    : ¬ F5 ob := by
  have h₄ := ne_empty_of_mem <| mem_inter_of_mem (mem_singleton.mpr rfl) h₂
  have h₅ := singleton_inter_of_not_mem h₃
  have h₆ := ne_empty_of_mem <| mem_inter_of_mem (mem_singleton.mpr rfl) h₀
  have h₇ := ne_empty_of_mem <| mem_inter_of_mem (mem_singleton.mpr rfl) h₁
  have g₀ : a₀ ∈ ({a₀} ∪ {a₁}) ∩ B := by simp;aesop
  have g₁ : a₀ ∈ ({a₀} ∪ {a₁}) ∩ A := by simp;aesop
  have g₂ : a₁ ∈ ({a₀, a₁} : Finset (Fin n)) := by aesop
  have g₃ : {a₀} ∩ ({a₁} : Finset (Fin n)) = ∅ := by aesop
  have g₄ : ¬ ({a₀} ∪ {a₁}) ∩ B = ∅ := fun hc => not_mem_empty _ (hc ▸ g₀)
  have g₅ : ¬ ({a₀} ∪ {a₁}) ∩ A = ∅ := fun hc => not_mem_empty _ (hc ▸ g₁)
  unfold F5
  push_neg
  use {a₀,a₁}, {a₀}, {a₁}
  constructor
  · unfold canon₂_II at *
    rw [if_neg h₄] at *
    rw [if_neg h₆] at *
    simp at *
    rw [g₃] at *
    simp_all only [singleton_inter_of_mem, singleton_ne_empty, not_false_eq_true, singleton_inter_of_not_mem,
      ↓reduceIte]
    apply hc₀
    simp_all only [singleton_inter_of_mem, singleton_ne_empty, ↓reduceIte, mem_filter, mem_univ, mem_singleton,
      inter_insert_of_mem, true_and]
    ext a : 1
    simp_all only [mem_singleton, mem_insert, mem_inter, iff_self_or, implies_true]
  · constructor
    · unfold canon₂_II at *
      rw [if_neg h₇] at *
      rw [h₅] at *
      simp at *
      aesop
    · unfold canon₂_II at *
      simp at *
      intro hc
      have q := hc₁₂ hc
      simp at q
      have : a₁ ∉ A := by exact h₃
      have : a₁ ∈ ({a₀, a₁} : Finset (Fin n)) := by simp
      rw [if_neg g₄, if_neg g₅] at q
      simp at q
      rw [← q] at this
      simp at this
      tauto

/-- Generically, F5 fails for canon₂_II.
Specifically canon₂_II {0} univ does not,
although canon₂_II {0} {0} does, over Fin 2.
-/
theorem not_canon₂_II_F5 {n : ℕ} {A B : Finset (Fin n)}
  (h : A ∩ B ≠ ∅) (h' : B \ A ≠ ∅) :
  ¬ F5 (canon₂_II A B) := by
  have ⟨a₀,ha₀⟩ : ∃ a₀, a₀ ∈ A ∩ B := by
    refine Nonempty.exists_mem ?_;exact nonempty_iff_ne_empty.mpr h
  have ⟨a₁,ha₁⟩ : ∃ a₁, a₁ ∈ B \ A := by
    refine Nonempty.exists_mem ?_;exact nonempty_iff_ne_empty.mpr h'
  have h₁ : a₁ ∈ B := by simp at ha₁; tauto
  have h₃ : a₁ ∉ A := by simp at ha₁; tauto
  have h₀ : a₀ ∈ B := by simp at ha₀;tauto
  have h₂ : a₀ ∈ A := by simp at ha₀;tauto
  apply similar_to_canon₂_II_often_fails_F5 h₀ h₁ h₂ h₃ <;>
  exact fun ⦃a⦄ a ↦ a

/-- A weaker form of `not_canon₂_II_F5`. -/
theorem canon₂_II_often_fails_F5 {n : ℕ} (A B : Finset (Fin n))
  (hA : A ≠ ∅) (hA' : A ≠ B) (h₁ : A ⊆ B):
    ¬ F5 (canon₂_II A B) := by
  apply not_canon₂_II_F5
  contrapose! hA
  ext i;simp
  by_contra H
  have : i ∈ A ∩ B := by simp;constructor;tauto;apply h₁;tauto
  rw [hA] at this
  simp at this
  contrapose! hA'
  apply subset_antisymm
  tauto
  intro i hi
  by_contra H
  have : i ∈ B \ A := by simp;constructor;tauto;tauto
  rw [hA'] at this
  simp at this



section KjosHanssen2017
open Classical

/--THEOREM 1.2
The main result of [Kjos-Hanssen 2017].
 Adapted from `rj-mike-final.lean` Math 654 final project Fall 2020.
-/
theorem cj1_2 {U : Type*} [Fintype U] {A B : Finset U}
    {ob : Finset U → Finset (Finset U)} (hg : weakly_mutually_generic A B)
    (b5 : B5 ob) (d5 : D5 ob) (e5w : E5weak ob) (hu₀ : A ∈ ob univ) : B ∈ ob Aᶜ := by
  have e5₀ : A                   ∈ ob (A ∪ Bᶜ) := e5w (A ∪ Bᶜ) A hu₀ (gen₁₁ hg)
  have hu₁ : univ \ (A ∪ Bᶜ) ∪ A ∈ ob univ     := d5 (A ∪ Bᶜ) A univ subset_union_left e5₀ (subset_univ _)
  have hu₂ : A ∪ B               ∈ ob univ     := by convert hu₁ using 1; ext;simp;tauto
  have e5₁ : A ∪ B               ∈ ob Aᶜ       := e5w Aᶜ (A ∪ B) hu₂ (gen₀₀ hg)
  exact (b5 Aᶜ (A ∪ B) B (differenceCap A B).symm) e5₁

/-- The weak form of E5 proves weak conditional explosion.
Should also be true if we remove both occurrences of "weak".
-/
theorem may30_2025 {U : Type*} [Fintype U] {ob : Finset U → Finset (Finset U)}
    (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5w : E5weak ob) :
    CXweak ob := by
  intro A B hu₀ hgen
  have e5₀ : A                   ∈ ob (A ∪ Bᶜ) := e5w (A ∪ Bᶜ) A hu₀ (by
    have : A ≠ ∅ := fun hc => a5 univ <| hc ▸ hu₀
    contrapose! this
    rw [← this]
    ext;simp)
  have hu₁ : univ \ (A ∪ Bᶜ) ∪ A ∈ ob univ     := d5 (A ∪ Bᶜ) A univ subset_union_left e5₀ (subset_univ _)
  have hu₂ : A ∪ B               ∈ ob univ     := by convert hu₁ using 1; ext;simp;tauto
  have e5₁ : A ∪ B               ∈ ob Aᶜ       := e5w Aᶜ (A ∪ B) hu₂ (by
    contrapose! hgen
    rw [← hgen]
    ext;simp;tauto)
  exact (b5 Aᶜ (A ∪ B) B (differenceCap A B).symm) e5₁

/-- Assuming axioms A5, B5, if A ∈ ob C then A ∩ C ≠ ∅. -/
theorem ab_ob {U : Type*} [Fintype U]
    {ob : Finset U → Finset (Finset U)} (a5 : A5 ob)
    (b5 : B5 ob)  (A C : Finset U) (hu₀ : A ∈ ob C)  :
    A ∩ C ≠ ∅ := fun hc => a5 _ <| (b5 C A ∅ (hc ▸ (empty_inter C).symm)) hu₀



/-- The axioms A5, B5, D5, E5 imply conditional deontic explosion.
(Separately we prove CJ 2022's conjecture that A5, B5, C5, E5, F5, G5 do not.)
-/
theorem conditional_explosion {U : Type*} [Fintype U] {ob : Finset U → Finset (Finset U)}
    (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob) :
    CX ob := by
  intro A B C hu₀ hgen
  have e5₀ : A ∈ ob ((A ∪ Bᶜ) ∩ C) := e5 C ((A ∪ Bᶜ) ∩ C) A (by simp) hu₀ (by
    have : A ∩ C ≠ ∅ := ab_ob a5 b5 _ _ hu₀
    contrapose! this
    rw [← this]
    ext;simp;tauto)
  have hu₂ : C ∩ (A ∪ B) ∈ ob C := by
    have := d5 ((A ∪ Bᶜ) ∩ C) (A ∩ C) C (inter_subset_inter (by simp) (by simp))
      ((b5 ((A ∪ Bᶜ) ∩ C) A (A ∩ C) (by ext;simp)) e5₀) (by intro;simp)
    convert this using 1
    ext;simp;tauto
  exact (b5 (Aᶜ ∩ C) (C ∩ (A ∪ B)) B (by ext;simp;tauto)) <|
    e5 C (Aᶜ ∩ C) (C ∩ (A ∪ B)) (by simp) hu₂ (by
      contrapose! hgen
      rw [← hgen]
      ext;simp;tauto)


-- easily prove that no canon₂ or canon₂_II model can satisfy all CJ 2022 want?
end KjosHanssen2017


theorem e5Needed : ∃ ob : Finset (Fin 3) → Finset (Finset (Fin 3)),
    B5 ob ∧ D5 ob ∧ ¬ CX ob := by
  use canon₂ {0} {0,1}
  constructor
  exact canon₂_B5 {0} {0, 1}
  constructor
  apply canon₂_D5
  simp
  unfold CX
  push_neg
  use {0}, {2}, univ
  constructor
  · unfold canon₂
    simp
  · constructor
    · simp
    · unfold canon₂
      simp

theorem e5Needed₂ :
    ∃ ob : Finset (Fin 2) → Finset (Finset (Fin 2)),
    B5 ob ∧ D5 ob ∧ ¬ CX ob := by
  use canon₂ {0} {0}
  constructor
  exact canon₂_B5 {0} {0}
  constructor
  · apply canon₂_D5
    simp
  · simp [CX, canon₂]
    push_neg
    use {0}, {1}, univ
    simp

/-- Over `Fin 0`, we don't need B5
to get CX. -/
theorem b5Needed₀ (ob : Finset (Fin 0) → Finset (Finset (Fin 0))) : CX ob := by
  cases all_are_my ob with
  | inl h =>
    subst h
    unfold CX my₀ at *
    simp_all
  | inr h =>
    subst h
    unfold CX my₁ at *
    simp_all


/-- Over `Fin 1`, we don't need B5
to get CX. -/
theorem b5Needed₁ (ob : Finset (Fin 1) → Finset (Finset (Fin 1)))
    (a5 : A5 ob) : CX ob := by
  intro A B C h₀ h₁
  by_cases H : B = ∅
  · subst H
    simp at h₁
  · have : B = {0} := nonemptyFin1 H
    subst this
    have : A ≠ ∅ := by
      intro hc
      subst hc
      revert h₀
      simp
      apply a5
    have : A = {0} := nonemptyFin1 this
    subst this
    simp at h₁

/-- A minimal ob given the constraints
    (h₀ : {0} ∈ ob {1})
    (h₁ : {1} ∉ ob {1})
 found in `nonCXcondition`
 It satisfies A5, D5, E5, (and C5 and F5 and G5) but not CX (and hence not B5).
It clarifies the key role played by B5 in deriving CX.
 -/
def obNonB5  : Finset (Fin 2) → Finset (Finset (Fin 2)) := fun X =>
  ite (X = {1}) {{0}} ∅

theorem obNonB5Facts :
  (¬ CX obNonB5) ∧ A5 obNonB5 ∧ C5 obNonB5 ∧ D5 obNonB5 ∧ E5 obNonB5 ∧ F5 obNonB5 ∧ G5 obNonB5 := by
  have : ¬ CX obNonB5 := by
    unfold CX obNonB5
    intro hc
    specialize hc {0} {1} {1}
    simp at hc
  have : C5 obNonB5 := by
    intro A B C h₀ h₁ h₂
    unfold obNonB5 at *
    by_cases H : A = {1}
    · subst H
      simp at *
      subst h₀ h₁
      simp
    rw [if_neg H] at h₀
    simp at h₀
  have : A5 obNonB5 := by
    intro A
    unfold obNonB5
    by_cases H : A = {1}
    subst H
    simp
    intro hc
    have : 0 ∈ ({0} : Finset (Fin 2)) := by aesop
    rw [← hc] at this
    simp at this
    rw [if_neg H]
    simp
  have : D5 obNonB5 := by
    intro X Y Z h₀ h₁ h₂
    have : X = {1} := by
      unfold obNonB5 at *
      by_contra H
      rw [if_neg H] at h₁
      simp at h₁
    subst this
    have : Y = {0} := by
      unfold obNonB5 at *
      simp at h₁
      exact h₁
    subst this
    exfalso
    simp at h₀
  have : E5 obNonB5 := by
    intro X Y Z h₀ h₁ h₂
    have : X = {1} := by
      unfold obNonB5 at *
      by_contra H
      rw [if_neg H] at h₁
      simp at h₁
    subst this
    have : Z = {0} := by
      unfold obNonB5 at *
      simp at h₁
      exact h₁
    subst this
    exfalso
    aesop
  have : F5 obNonB5 := by
    intro A B C h₀ h₁
    unfold obNonB5 at *
    by_cases H : B = {1}
    · subst H
      simp at h₀
      subst h₀
      simp
      by_cases H₀ : C = {1}
      · subst H₀
        simp
      · simp_all
    · rw [if_neg H] at h₀
      simp at h₀
  have : G5 obNonB5 := by
    intro A B C h₀ h₁ h₂
    unfold obNonB5 at *
    by_cases H : B = {1}
    · subst H
      simp at h₁
      subst h₁
      simp at h₂
    · rw [if_neg H] at h₁
      simp at h₁
  tauto

theorem nonCXcondition (ob : Finset (Fin 2) → Finset (Finset (Fin 2)))
    (h₀ : {0} ∈ ob {1})
    (h₁ : {1} ∉ ob {1})
    : ¬ CX ob := by
  intro hc
  unfold CX at hc
  specialize hc {0} {1} {1} h₀ (by simp)
  simp at hc
  tauto

recall b5Needed₁
/--
[KH2017] showed that B5 ∧ D5 ∧ E5 |= CX.
This shows that B5 is needed.
A5 fails too here, as it must when `n=1` by `b5Needed₁`.
-/
theorem b5Needed : ∃ (ob : Finset (Fin 1) → Finset (Finset (Fin 1))),
    D5 ob ∧ E5 ob ∧ ¬ CX ob ∧ ¬ A5 ob := by
  use fun A => ite (A = ∅) {{0}} {∅}
  constructor
  intro X Y Z h₀ h₁ h₂
  simp at *
  by_cases H : X = ∅
  subst H
  simp
  by_cases H₀ : Z = ∅
  · aesop
  · rw [if_neg H₀]
    exfalso
    simp at h₁
    rw [h₁] at h₀
    simp at h₀
  by_cases H₀ : Z = ∅
  subst H₀
  simp
  exfalso
  apply H
  exact subset_empty.mp h₂
  · rw [if_neg H₀]
    rw [if_neg H] at h₁
    simp at h₁
    subst h₁
    rw [nonemptyFin1 H, nonemptyFin1 H₀]
    simp
  · constructor
    · intro X Y Z h₀ h₁ h₂
      simp at h₁ ⊢
      by_cases H : Y = ∅
      · subst H
        simp at h₂
      · rw [if_neg H]
        by_cases H₀ : X = ∅
        · subst H₀
          exfalso
          apply H <| subset_empty.mp h₀
        · convert h₁ using 1
          rw [if_neg H₀]
    · constructor
      unfold CX
      push_neg
      simp
      use ∅, {0}, {0}
      simp
      unfold A5
      simp
      use {0}
      simp

/-- `ob` is the type of model that was sought but not found in
[CJ 2022, Observation 5.2]. The concept is a bit obsolete given the limited
deontic explosion in that system. -/
def adequate {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) : Prop :=
  A5 ob ∧ B5 ob ∧ C5 ob ∧ E5 ob ∧ F5 ob ∧ G5 ob ∧ ¬ CX ob


/-- `canon₂_II A B` avoids deontic explosion in a general setting:
A type of genericity that includes the case `A = B`. -/
theorem canon₂_II_not_CX {n : ℕ} {A B : Finset (Fin n)}
    (hA : A ≠ ∅) (hB : B ≠ ∅) (h₂ : Bᶜ ∩ Aᶜ ≠ ∅) :
    ¬CX (canon₂_II A B) := by
  unfold CX canon₂_II
  push_neg
  use A, Bᶜ, univ -- this proof is intuitive
  simp
  rw [if_neg hB, if_neg hA]
  simp
  constructor
  · exact h₂
  · have : Aᶜ ∩ A = ∅ := by ext;simp
    rw [this]
    simp
    by_cases H : Aᶜ ∩ B = ∅
    · rw [if_pos H]
      simp
    · rw [if_neg H]
      simp
      apply in_neither h₂



theorem canon_II_not_CX {n : ℕ} {A : Finset (Fin n)} (hA : A ≠ ∅)
    (hA' : A ≠ univ) :
  ¬CX (canon₂_II A A) := canon₂_II_not_CX hA hA (by simp; exact hA')

recall not_canon₂_II_F5
/-- `canon_II` generally is adequate (but it does not involve
contrary-to-duty obligations).
For most A and B, `canon₂_II A B` is not adequate, by `not_canon₂_II_F5`,
and `canon₂ A B` is not adequate since by `many_not_canon₂_E5`,
E5 does not hold for it.
 -/
theorem infinitely_many_adequate {n : ℕ} {A : Finset (Fin n)}
    (hA : A ≠ ∅) (hA' : A ≠ univ) : adequate (canon₂_II A A) :=
  ⟨canon₂_II_A5 A A, canon₂_II_B5 A A, canon₂_II_C5 A A,
   canon₂_II_E5 (by simp), canon_II_is_canon₂_II (A := A) ▸ canon_II_F5 A,
   canon₂_II_G5 A A, canon_II_not_CX hA hA'⟩


recall generalize_F5_canon_II
/-- To show that `generalize_F5_canon_II` is not trivial. -/
theorem injective_canon₂_II {n : ℕ} {A B : Finset (Fin n)}
    (hBA : canon₂_II A B = canon_II A) : B = A := by
  unfold canon₂_II canon_II at hBA
  have hf := congrFun hBA Aᶜ
  simp at hf
  by_cases H₀ : Aᶜ ∩ B = ∅
  · by_cases H₁ : Bᶜ ∩ A = ∅
    · exact eq_of_sdiff_empty H₀ H₁
    · have hf := congrFun hBA Bᶜ
      have : Bᶜ ∩ B = ∅ := by ext;simp
      rw [this] at hf
      simp at hf
      rw [if_neg H₁] at hf
      exfalso
      apply some_like_given hf
  · rw [if_neg H₀] at hf
    have : Aᶜ ∩ A = ∅ := by ext;simp
    rw [this] at hf
    simp at hf
    exfalso
    have : fun Y ↦ Aᶜ ∩ Y = Aᶜ ∩ B
         = fun Y ↦ Aᶜ ∩ B = Aᶜ ∩ Y := by aesop
    simp_rw [← this] at hf
    apply some_like_given hf.symm

/-- This is the closest canon₂_II analogue of observation_5_2. -/
def modified_obs52 := canon₂_II (α := Fin 4) {0,1} {0,1,3}
lemma not_CX_modified_obs52 : ¬ CX modified_obs52 := by
  apply canon₂_II_not_CX
  · simp
  · simp
  · intro hc
    have : 2 ∈ (∅ : Finset (Fin 4)) := by
      rw [← hc]
      simp
    simp at this

/-- A weaker form of canon₂_II_not_CX. -/
theorem canon₂_II_not_CX_of_mutually_generic
    {n : ℕ} {A B : Finset (Fin n)}
    (hm : mutually_generic A B) :
    ¬ CX (canon₂_II A B) := by
  unfold mutually_generic at hm
  have hA : A ≠ ∅ := by
    contrapose! hm
    subst hm
    simp
  have hB : B ≠ ∅ := by
    contrapose! hm
    subst hm
    simp
  exact canon₂_II_not_CX hA hB
    (by
    have := hm.2.2.2
    contrapose! this
    rw [← this]
    simp
    ext;simp;tauto)
