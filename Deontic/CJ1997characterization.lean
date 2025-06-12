import Deontic.Basic
import Deontic.Finset
import Deontic.Venn
import Deontic.Canonical
-- import Deontic.canon3

/-!

# The system of Carmo and Jones 1997

`ob_of_small_good`
--> `ob_of_small_good_pair`
--> `no_small_good_of_ob`
--> `no_small_good_CJ97₀` --> `no_small_good_CJ97` --> `le_one_CJ97` --> `unique_bad_world`
                                                                                        |
                                                                                        v
                                                                                  `all_or_almost'`
`alive_properties` (used @ end)
`stayAlive_properties` (used @ end)



            `all_or_almost'`    `getUniv` <--- `agree_on_exclusion`               `almost_stayAlive`
                             \       |             /         |                          |
                              \ >    v            /          |                          v
`trivial_ob_of_nontrivial` --> `getStayAlive` <- /           |                   ``le_one_of_large_of_ob``
                                      |                      |                          |
                                      v                      v                          v
              `univ_ob_univ` --->  [`models_ofCJ_1997`]  <- `getAlive` <--- `le_one_CJ97`
-/

open Finset

/- A family of deontic models in which the only obligation is to avoid
the dreaded world `e`. -/
def stayAlive (n : ℕ) (e : Fin n) : Finset (Fin n) → Finset (Finset (Fin n)) :=
  fun X => {Y | X ∩ Y ≠ ∅ ∧ X ∩ Y ⊇ X \ {e}}

/-- A version of stayAlive where `e` is missing,
or if you will, e = n ∉ Fin n.
 -/
def alive (n : ℕ) : Finset (Fin n) → Finset (Finset (Fin n)) :=
  fun X => {Y | X ≠ ∅ ∧ Y ⊇ X }

theorem alive_properties {n : ℕ} :
    A5 (alive n) ∧ B5 (alive n) ∧ C5Strong (alive n)
    ∧ D5 (alive n) ∧ E5 (alive n) := by
  unfold alive
  constructor
  · simp [A5]
  constructor
  · intro X Y Z h₀ h₁
    simp at *
    constructor
    exact h₁.1
    rw [← inter_eq_right.mpr h₁.2, h₀]
    exact inter_subset_left
  constructor
  · intro X Y Z h₀ h₁
    simp at *
    exact ⟨h₀.1, subset_inter h₀.2 h₁.2⟩
  constructor
  · intro X Y Z h₀ h₁ h₂
    simp at *
    constructor
    · have := h₁.1
      contrapose! this
      subst this
      exact subset_empty.mp h₂
    rw [subset_antisymm h₁.2 h₀]
    simp
  intro X Y Z h₀ h₁ h₂
  simp at *
  constructor
  · intro hc
    rw [hc] at h₂
    simp at h₂
  · exact subset_trans h₀ h₁.2


/-- This shows that the system studied in
"A new approach to contrary-to-duty obligations" (1997)
in 1996 has infinitely many models.
June 4, 2025.
 -/
theorem stayAlive_properties {n : ℕ} (e : Fin n) :
    A5 (stayAlive n e) ∧ B5 (stayAlive n e) ∧ C5Strong (stayAlive n e)
    ∧ D5 (stayAlive n e) ∧ E5 (stayAlive n e) := by
  unfold stayAlive
  constructor
  · intro X
    simp
  constructor
  · intro X Y Z h₀ h₁
    simp at *
    rw [inter_comm, ← h₀, inter_comm]
    exact h₁
  constructor
  · intro X Y Z h₀ h₁
    simp at *
    constructor
    · by_cases H : X \ {e} = ∅
      · have : X = {e} := by
          simp at H
          cases H with
          | inl h => subst h;simp_all
          | inr h => tauto
        subst this
        intro hc
        have : e ∈ {e} ∩ (Y ∩ Z) := by
          simp;exact ⟨(venn_singleton _ _).mpr h₀.1, (venn_singleton _ _).mpr h₁.1⟩
        rw [hc] at this
        simp at this
      · rw [show X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z) by ext;simp;tauto]
        contrapose! H
        exact subset_empty.mp $ H ▸ subset_inter h₀.2 h₁.2
    · rw [show X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z) by ext;simp;tauto]
      exact subset_inter h₀.2 h₁.2
  -- D5
  constructor
  · intro X Y Z h₀ h₁ h₂
    simp at *
    constructor
    · have := h₁.1
      contrapose! this
      apply subset_empty.mp
      rw [← this]
      intro;simp;tauto
    apply subset_inter
    · simp
    · intro i hi
      simp at hi ⊢
      by_cases H : i ∈ X
      · right
        suffices i ∈ X ∩ Y by simp at this;tauto
        apply h₁.2
        simp
        tauto
      · left
        tauto
  -- E5
  intro X Y Z h₀ h₁ h₂
  simp at *
  constructor
  · tauto
  · intro i hi
    simp at hi ⊢
    constructor
    · tauto
    · suffices i ∈ X ∩ Z by simp at this;tauto
      apply h₁.2
      simp
      exact ⟨h₀ hi.1, hi.2⟩


section lemma9_1996


lemma ob_of_small_good
  {n : ℕ} {ob : Finset (Fin n) → Finset (Finset (Fin n))} {A : Finset (Fin n)} (d5 : D5 ob)
  {a₁ a₂ : Fin n} (ha₁₂ : a₁ ≠ a₂)
    (h : ∀ X, A ⊆ X → A ∈ ob X) :
    A ∪ {a₂} ∈ ob (A ∪ {a₁, a₂}) := by
    convert fixD5 d5 (A ∪ {a₁, a₂}) (A ∪ {a₁}) A (by
      convert h (A ∪ {a₁}) (by simp) using 1
      congr
      ext b
      simp
      constructor
      · intro h
        cases h with
        | inl h => exact .inr h
        | inr h => exact h.2
      · intro h
        cases h with
        | inl h => simp_all
        | inr h => exact .inl h
      simp
      intro i hi
      simp
      right
      simp_all
      ) using 1
    ext j; simp;
    constructor
    · intro h
      cases h with
      | inl h =>
        simp_all
      | inr h =>
        simp_all
        by_cases H : a₂ ∈ A
        simp_all
        simp_all
        tauto
    · tauto

lemma ob_of_small_good_pair
  {n : ℕ} {ob : Finset (Fin n) → Finset (Finset (Fin n))} {A : Finset (Fin n)}
  {a₁ a₂ : Fin n} (ha₁₂ : a₁ ≠ a₂)
    (h : ∀ X, A ⊆ X → A ∈ ob X) (d5 : D5 ob) :
    A ∪ {a₁} ∈ ob (A ∪ {a₁, a₂}) ∧
    A ∪ {a₂} ∈ ob (A ∪ {a₁, a₂}) := ⟨by
      convert ob_of_small_good d5 ha₁₂.symm h using 2
      rw [pair_comm],
      ob_of_small_good d5 ha₁₂ h
      ⟩

end lemma9_1996


theorem no_small_good_of_ob {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))} {A : Finset (Fin n)}
    {a₁ a₂ : Fin n} (ha₀ : a₁ ∉ A) (ha₁ : a₂ ∉ A) (ha₂ : a₁ ≠ a₂)
    (hcorr : {a₁, a₂} ∈ ob {a₁, a₂})
    (a5 : A5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob) :
    ¬ (∀ X, A ⊆ X → A ∈ ob X) := by
  intro h
  have hl := ob_of_small_good_pair ha₂ h d5
  let Z₁ := A ∪ {a₁}
  let Z₂ := A ∪ {a₂}
  have h₁ : Z₁ ∈ ob {a₁, a₂} := e5 (A ∪ {a₁, a₂}) {a₁, a₂} Z₁ (by simp;intro i;simp;tauto) hl.1 (by
    intro H
    have : a₁ ∈ {a₁, a₂} ∩ Z₁ := by simp [Z₁]
    rw [H] at this
    simp at this)
  have h₂ : Z₂ ∈ ob {a₁, a₂} := e5 (A ∪ {a₁, a₂}) {a₁, a₂} Z₂ (by simp;intro i;simp;tauto) hl.2 (by
    intro H
    have : a₂ ∈ {a₁, a₂} ∩ Z₂ := by simp [Z₂]
    rw [H] at this
    simp at this)

  have h₃ : {a₁} ∈ ob {a₁, a₂} := by
    convert c5 {a₁, a₂} Z₁ {a₁, a₂} h₁ hcorr using 1
    ext b
    simp [Z₁]
    intro h₀ h₁
    rw [h₁] at h₀
    cases h₀ <;> tauto
  have h₄ : {a₂} ∈ ob {a₁, a₂} := by
    convert c5 {a₁, a₂} Z₂ {a₁, a₂} h₂ hcorr using 1
    ext b;simp [Z₂]
    constructor
    intro h₀
    rw [h₀]
    simp
    intro h₀
    simp at h₀
    cases and_or_right.mpr h₀ with
    | inl h => simp_all
    | inr h => tauto
  have : ∅ ∈ ob {a₁, a₂} := by
    convert c5 {a₁, a₂} {a₁} {a₂} h₃ h₄ using 1
    ext b
    simp
    exact fun h => h ▸ ha₂
  exact a5 _ this

lemma no_small_good_CJ97₀
    {n : ℕ} {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    {A : Finset <| Fin n} {a₁ a₂ : Fin n} (ha' : a₁ ∉ A ∧ a₂ ∉ A ∧ a₁ ≠ a₂) :
    ¬ ∀ X, A ⊆ X → A ∈ ob X := by
  intro h
  have cx : CX ob := by
    convert conditional_explosion a5 (by convert b5) (by convert d5) (by convert e5)
  have : {a₁, a₂} ∈ ob {a₁, a₂} := by
    specialize cx A {a₁,a₂} (A ∪ {a₁,a₂}) (by apply h;simp;intro i hi;simp;tauto)
      (ne_empty_of_mem (by simp;tauto))
    convert cx using 2
    simp
    ext b;simp
    constructor
    intro h
    cases h with
    | inl h => subst h;tauto
    | inr h => rw [h];tauto
    intro h
    have := h.2
    cases this with
    | inl h => subst h;left;rfl
    | inr h => cases h with
      | inl h => tauto
      | inr h => right;tauto
  exact no_small_good_of_ob ha'.1 ha'.2.1 ha'.2.2 this a5 c5 d5 e5 h



theorem almost_stayAlive {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob)
    (hBC : ∃ B C, Finset.card (C \ B) ≥ 2 ∧ B ⊆ C ∧ B ∈ ob C)
    :
    ¬ ∀ A, Finset.card A ≤ n-2 → ∃ X, A ⊆ X ∧ A ∉ ob X := by
  push_neg
  obtain ⟨B,C,hB⟩ : ∃ B C, Finset.card (C \ B) ≥ 2 ∧ B ⊆ C ∧ B ∈ ob C := hBC
  have := @d5 C B univ
  have h : ∃ A ∈ ob univ, #A ≤ n-2 := by
    use univ \ C ∪ B
    constructor
    apply this
    tauto
    tauto
    simp
    have : Disjoint (univ \ C) B := by
      intro D hD₀ hD₁
      simp at hD₀
      intro i hi
      have h₁ := hD₀ hi
      simp at h₁
      exfalso
      exact h₁ $ hB.2.1 $ hD₁ hi
    have : #(univ \ C ∪ B) = #(univ \ C) + #B := card_union_of_disjoint this
    rw [this]
    have : #(univ \ C) = #(univ : Finset (Fin n)) - #C := by
      refine card_sdiff ?_
      simp
    rw [this]
    simp
    have : #(C \ B) = #C - #B := by
      refine card_sdiff ?_
      tauto
    rw [this] at hB
    have : #C ≥ 2 + #B := by omega
    have : n - #C + #B
         = n + #B - #C := by
          refine Eq.symm (Nat.sub_add_comm ?_)
          exact card_finset_fin_le C
    rw [this]
    omega

  obtain ⟨A,hA⟩ := h
  use A
  constructor
  tauto
  intro X hX
  unfold E5 at e5
  have hn : A ≠ ∅ := by
    intro hc
    subst hc
    exact a5 _ hA.1
  exact e5 univ X A (by simp) hA.1 (by
    have : A = A ∩ X := by
      have := (@inter_eq_left (Fin n) _ A X).mpr hX
      tauto
    rw [inter_comm, ← this]
    tauto)


theorem trivial_ob_of_nontrivial {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob) {X Y : Finset (Fin n)}
    {a : Fin n} (ha : a ∈ X) (hX : X \ {a} ∈ ob X) (haY : a ∉ Y)
    (hY : Y ≠ ∅) : Y ∈ ob Y := by
  have h₀ := d5 X (X \ {a}) (X ∪ Y) (by simp) hX (by simp)
  have h₁ := e5 (X ∪ Y) Y ((X ∪ Y) \ X ∪ X \ {a}) (by simp) h₀
    (by
      have ⟨y,hy⟩ : ∃ y, y ∈ Y := Nonempty.exists_mem $ nonempty_iff_ne_empty.mpr hY
      have : y ∈ Y ∩ ((X ∪ Y) \ X ∪ X \ {a}) := by
        simp
        by_cases H : y ∈ X
        · simp_all
          intro hc
          subst hc
          exact haY hy
        · tauto
      exact ne_empty_of_mem this
    )
  convert b5 Y ((X ∪ Y) \ X ∪ X \ {a}) (((X ∪ Y) \ X ∪ X \ {a}) ∩ Y) (by simp) h₁ using 2
  ext i;simp
  intro hi
  by_cases H : i ∈ X
  · right
    constructor
    tauto
    intro hc
    subst hc
    simp_all
  · left
    tauto


theorem agree_on_exclusion {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob) {X Y : Finset (Fin n)}
    {a : Fin n} (ha : a ∈ X) (h : X \ {a} ∈ ob X) (haY : Y \ {a} ≠ ∅) :
    Y \ {a} ∈ ob Y := by
  have : (X ∪ Y) \ {a} ∈ ob (X ∪ Y) := by
    convert d5 X (X \ {a}) (X ∪ Y) (by simp) h (by simp) using 1
    apply union_sdiff_singleton <;> tauto
  have : (X ∪ Y) \ {a} ∈ ob Y := e5 (X ∪ Y) Y ((X ∪ Y) \ {a}) (by simp) this (by
      contrapose! haY
      rw [← haY]
      ext;simp;tauto)
  exact b5 Y ((X ∪ Y) \ {a}) (Y \ {a}) (by ext;simp;tauto) this

theorem agree_on_inclusion {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob) {X Y : Finset (Fin n)}
    (hX : X ∈ ob X) (hY : Y ≠ ∅) : Y ∈ ob Y := by
  have : X ∪ Y ∈ ob (X ∪ Y) := by
    convert d5 (Z := X ∪ Y) X X (by simp) hX (by simp) using 1
    ext;simp;tauto
  have := e5 (X ∪ Y) Y (X ∪ Y) (by simp) this (by
    simp
    exact hY)
  exact b5 Y (X ∪ Y) Y (by simp) this

theorem getUniv {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
    (X Y : Finset (Fin n)) (a : Fin n)
    (hY : Y \ {a} ≠ ∅) (hh : X ∩ Y = {a})
    (h : X \ {a} ∈ ob X) : X ∈ ob X := by
  have ha : a ∈ X ∩ Y := by rw [hh];simp
  have : Y \ {a} ∈ ob Y := by
    simp at ha
    exact agree_on_exclusion b5 d5 e5 ha.1 h hY
  have : Y \ {a} ∈ ob (Y \ {a}) := e5 (Y) (Y \ {a}) (Y \ {a}) (by simp) this
      (by
        simp
        constructor
        · contrapose! hY
          subst hY
          simp
        · intro hc
          subst hc
          simp at this
          exact a5 _ this)
  exact agree_on_inclusion b5 d5 e5
    this (by
      contrapose! hh;subst hh;intro hc;simp at hc;revert hc;simp
      exact fun a ↦ a5 ∅ h)


lemma ob_forbidden {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob)
    (ob_forbidden₀ : ∀ X, ∀ a ∈ X, X \ {a} ∈ ob X → {a} ∈ ob {a}) :
              ∀ X, ∀ a ∈ X, X \ {a} ∈ ob X → ob {a} = {Y | a ∈ Y}.toFinset := by
  intro X a ha ha'
  specialize ob_forbidden₀ X a ha ha'
  apply subset_antisymm
  · intro Y hY
    simp
    by_contra H
    have h₀ : Y ∩ {a} ∈ ob {a} := by apply c5 <;> tauto
    have h₁ : Y ∩ {a} = ∅ := subset_empty.mp fun i hi => by
      exfalso
      simp at hi
      exact H $ hi.2.symm ▸ hi.1
    exact a5 _ $ h₁ ▸ h₀
  · intro Y hY
    simp at hY
    exact b5 {a} (Y ∩ {a}) Y (by simp) (by
      have : Y ∩ {a} = {a} := by
        apply subset_antisymm <;> (simp;tauto)
      rw [this]
      tauto)

lemma ob_forbidden_self {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
    (adHoc : ∀ a : Fin n, univ \ {a} ∈ ob univ →  univ ∈ ob univ)
    (X : Finset (Fin n)) (a : Fin n) (ha : a ∈ X)
    (ha' : X \ {a} ∈ ob X) :
    {a} ∈ ob {a} := by
  have := adHoc a (by
    have := d5 X (X \ {a}) (univ) (by simp) ha' (by simp)
    convert this using 1
    apply subset_antisymm
    · intro i hi
      simp at hi ⊢
      tauto
    · intro i hi
      simp at hi ⊢
      cases hi with
      | inl h =>
        contrapose! h
        exact h ▸ ha
      | inr h => tauto)
  have : univ ∈ ob {a} := e5 univ {a} univ (by simp) this (by simp)
  exact b5 {a} univ {a} (by simp) this

lemma univ_ob_univ {n : ℕ}
    {ob : Finset (Fin (n+1)) → Finset (Finset (Fin (n+1)))}
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob) (a : Fin (n+1))
    (ha : univ \ {a} ∈ ob univ) :  univ ∈ ob univ := by
  have : univ \ {a} ∈ ob (univ \ {a}) :=
    e5 univ  (univ \ {a}) (univ \ {a}) (by simp) ha (by
      simp
      constructor
      · exact nonempty_iff_ne_empty.mp univ_nonempty
      · intro hc
        rw [hc] at ha
        simp at ha
        exact a5 _ ha
    )
  have := d5 (univ \ {a}) (univ \ {a}) univ (by simp) this (by simp)
  convert this using 2
  simp

/-- This cannot be formulated in terms of `Fin n`
but requires `Fin (n+1)`. -/
theorem le_one_of_large_of_ob {n : ℕ}
    {ob : Finset (Fin (n+1)) → Finset (Finset (Fin (n+1)))}
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob)
    (large_of_ob:  ∀ A, (∀ X, A ⊆ X → A ∈ ob X) → #A ≥ n) :
                   ∀ B C, B ⊆ C → B ∈ ob C → #(C \ B) ≤ 1 := by
  intro B C hBC ho
  have hn (m : ℕ) : n = m + 1 → ∀ A, Finset.card A ≤ m → ∃ X, A ⊆ X ∧ A ∉ ob X := by
    intro hm A hA
    by_contra H
    push_neg at H
    specialize large_of_ob A H
    omega
  have h_a (m : ℕ) : n = m + 1 → ¬ (∃ B C, #(C \ B) ≥ 2 ∧ B ⊆ C ∧ B ∈ ob C) := by
    intro hm hc
    apply almost_stayAlive a5 d5 e5 hc
    simp_rw [hm]
    simp
    apply hn
    exact hm
  push_neg at h_a
  by_cases H : ∃ m, n = m + 1

  obtain ⟨m,hm⟩ := H
  specialize h_a m hm B C
  by_contra H
  simp at H
  exact h_a H hBC ho

  have : n = 0 := by
    cases n with
    | zero => rfl
    | succ n => exfalso;push_neg at H;specialize H n;simp at H
  subst this
  have : #(C \ B) ≤ #(univ : Finset (Fin 1)) := by
    apply card_le_card
    apply subset_univ
  apply le_trans this
  simp


lemma no_small_good_CJ97 {n : ℕ}
    {ob : Finset (Fin (n+2)) → Finset (Finset (Fin (n+2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob) :
    ∀ A, Finset.card A ≤ n → ∃ X, A ⊆ X ∧ A ∉ ob X := fun A hA => by
  have ⟨a₁,a₂,ha'⟩: ∃ a₁ a₂, a₁ ∉ A ∧ a₂ ∉ A ∧ a₁ ≠ a₂ := by
    by_contra H
    push_neg at H
    have : A ≠ univ := by
      intro hc
      subst hc
      simp at hA
    have ⟨a₁, ha₁⟩ : ∃ a₁, a₁ ∉ A := by
      contrapose! this
      exact Eq.symm (Mathlib.Meta.Finset.univ_eq_elems A this)
    specialize H a₁
    have H' : ∀ a₂ ∉ A, a₁ = a₂ := by aesop
    have : A ∪ {a₁} = univ := by
      ext i;simp
      by_cases H : i ∈ A
      tauto
      specialize H' _ H
      tauto
    have : # (univ : Finset (Fin (n+2))) = #A + 1 := by
      rw [← this]
      exact (@card_eq_succ (Fin (n+2)) (A ∪ {a₁}) #A _).mpr (by
        use a₁, A
        simp
        constructor
        tauto
        ext;simp;tauto)
    simp at this
    omega
  by_contra hc
  push_neg at hc
  exact no_small_good_CJ97₀ a5 b5 c5 d5 e5 ha' hc

theorem le_one_CJ97 {n : ℕ}
    {ob : Finset (Fin (n+2)) → Finset (Finset (Fin (n+2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    {B C : Finset (Fin (n+2))}
    (h₀ : B ⊆ C) (h₁ : B ∈ ob C) : #(C \ B) ≤ 1 := by
  have hn := no_small_good_CJ97 a5 b5 c5 d5 e5
  have large_of_ob:  ∀ A, (∀ X, A ⊆ X → A ∈ ob X) → #A ≥ n+1 := by
    intro A
    contrapose!
    specialize hn A
    convert hn using 1
    exact Nat.lt_add_one_iff
  exact le_one_of_large_of_ob a5 d5 e5 large_of_ob _ _ h₀ h₁


theorem unique_bad_world {n : ℕ}
    {ob : Finset (Fin (n+2)) → Finset (Finset (Fin (n+2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    {X Y : Finset (Fin (n+2))}
    {a b : Fin (n+2)} (ha : a ∈ X) (hb : b ∈ Y)
    (hoa : X \ {a} ∈ ob X)
    (hob : Y \ {b} ∈ ob Y) : a = b := by
  have h₁ : (X ∪ Y) \ {a} ∈ ob (X ∪ Y) := by
    convert d5 X (X \ {a}) (X ∪ Y) (by simp) hoa (by simp) using 1
    apply union_diff_singleton ; tauto
  have h₃ : (X ∪ Y) \ {b} ∈ ob (X ∪ Y) := by
    convert d5 Y (Y \ {b}) (X ∪ Y) (by simp) hob (by simp) using 1
    convert union_diff_singleton Y X hb using 2
    · exact union_comm X Y
    · nth_rewrite 1 [union_comm]
      rfl
  have : #({a,b}) ≤ 1 := by
    convert le_one_CJ97 a5 b5 c5 d5 e5 (by intro;simp;tauto) $ c5 _ _ _ h₁ h₃ using 2
    apply pair_venn <;> tauto
  cases Nat.eq_or_lt_of_le this with
  | inl h =>
    simp at h
    have ⟨c,hc⟩ := card_eq_one.mp h
    have g₀ := subset_of_eq hc (show a ∈ {a,b} by simp)
    have g₁ := subset_of_eq hc (show b ∈ {a,b} by simp)
    simp at g₀ g₁
    simp_all
  | inr h => simp at h


lemma getAlive {n : ℕ} {ob : Finset (Fin (n + 2)) → Finset (Finset (Fin (n + 2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    (H₀ : ∃ Y X, X ∈ ob Y)
    (H₁ : ∀ (a : Fin (n + 2)) (Y X : Finset (Fin (n + 2))), a ∈ X ∩ Y → X \ {a} ∉ ob Y) :
    ob = alive (n + 2) := by
  ext X Y
  unfold alive
  simp
  constructor
  · intro h
    constructor
    · intro hc
      subst hc
      have := b5 ∅ Y ∅ (by simp) h
      exact a5 _ this
    · by_contra H
      have ⟨a,ha⟩ : ∃ a, a ∈ X \ Y := Nonempty.exists_mem $ sdiff_nonempty.mpr H
      have h₀ : X ∩ Y = X \ {a} := by
        ext i
        constructor
        · intro hi
          simp at hi ⊢
          constructor
          · tauto
          · intro hc
            subst hc
            simp at ha
            tauto
        · intro hi
          simp at hi ⊢
          constructor
          · tauto
          · by_contra H₀
            have : X ∩ Y ∈ ob X := b5 X Y (X ∩ Y) (by ext;simp) h
            have := le_one_CJ97 (B := X ∩ Y) (C := X) a5 b5 c5 d5 e5 (by simp) this
            apply two_in_sdiff <;> tauto
      have h₁ : X ∩ Y ∈ ob X := b5 X Y (X ∩ Y) (by ext;simp) h
      specialize H₁ a X X
      rw [h₀] at h₁
      simp at ha H₁
      tauto
  intro h
  obtain ⟨Y',X',h'⟩ := H₀
  have h₀ : Y' ∈ ob Y' := by
    have := le_one_CJ97 a5 b5 c5 d5 e5 (by simp)
      (b5 Y' X' (X' ∩ Y') (by simp) h')
    have :  #(Y' \ X') ≤ 1 := by
      convert this using 2
      simp
    have :  #(Y' \ X') = 1 ∨ #(Y' \ X') = 0 :=  Or.symm ((fun {n} ↦ Nat.le_one_iff_eq_zero_or_eq_one.mp) this)
    cases this with
    | inl h =>
      have ⟨a,ha⟩: ∃ a, Y' \ X' = {a} := card_eq_one.mp h
      specialize H₁ a
      have h : X' ∩ Y' = Y' \ {a} := by
        ext i
        simp
        constructor
        · intro hi
          constructor
          tauto
          intro hc
          subst hc
          have : i ∈ Y' \ X' := by
            rw [ha]
            simp
          simp at this
          tauto
        · intro hi
          constructor
          · have := hi.2
            contrapose! this
            have : i ∈ Y' \ X' := by simp;tauto
            rw [ha] at this
            simp at this
            tauto
          · tauto
      have : X' ∩ Y' ∈ ob Y' := by
        exact b5 Y' X' (X' ∩ Y') (by simp) h'
      rw [h] at this
      specialize H₁ Y' Y' (by
        have : a ∈ ({a} : Finset (Fin (n+2))) := by simp
        rw [← ha] at this
        simp at this ⊢
        tauto)
      tauto
    | inr h =>
      have : Y' \ X' = ∅ := card_eq_zero.mp h
      have : Y' ⊆ X' := sdiff_eq_empty_iff_subset.mp this
      have : X' ∩ Y' = Y' := inter_eq_right.mpr this
      nth_rewrite 2 [← this]
      exact b5 Y' X' (X' ∩ Y') (by simp) h'
  have h₁ : X ∈ ob X := agree_on_inclusion b5 d5 e5 h₀ h.1
  have h₂ : X = X ∩ Y := by
    have := inter_eq_right.mpr h.2
    rw [← this]
    ext;simp;tauto
  nth_rewrite 2 [h₂] at h₁
  exact b5 X (X ∩ Y) Y (by simp) h₁





theorem all_or_almost' {n : ℕ} {ob : Finset (Fin (n + 2)) → Finset (Finset (Fin (n + 2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    {a : Fin (n + 2)} {X' X Y : Finset (Fin (n + 2))}
    (haX' : a ∈ X') (haX : X \ {a} ≠ ∅)
    (imp : X' \ {a} ∈ ob X') (h' : X ∩ Y ∈ ob X) :
    X ∩ Y = X ∨ X ∩ Y = X \ {a} := by
  have : #(X \ (X ∩ Y)) ≤ 1 := le_one_CJ97 a5 b5 c5 d5 e5 (by simp) h'
  cases Nat.eq_or_lt_of_le this with
  | inl h =>
    right
    have ⟨b,hb⟩ : ∃ b, X \ (X ∩ Y) = {b} := card_eq_one.mp h
    have h₅ : (X \ {a}) ∩ (X \ {b}) = X \ {a,b} := by ext i;simp;tauto
    have : a = b := by
      have h₀ : X ∩ Y = X \ {b} := by
        rw [← hb]
        ext;simp
      have q₀ : X \ {b} ∈ ob X := h₀ ▸ h'
      have h₁ : X \ {a} ∈ ob X := agree_on_exclusion b5 d5 e5 haX' imp haX
      have h₂ : (X \ {a}) ∩ (X \ {b}) ∈ ob X := c5 _ _ _ h₁ (h₀ ▸ h')
      have h₃ : #(X \ ((X \ {a}) ∩ (X \ {b}))) ≤ 1 := le_one_CJ97 a5 b5 c5 d5 e5
        (by rw [h₅];simp) h₂
      by_cases Q : a ∈ X
      · have h₄ : {a,b} ⊆ X \ ((X \ {a}) ∩ (X \ {b})) := by
          rw [h₅]
          simp
          intro i hi
          simp_all
        simp at this
        by_contra H
        have := card_pair H ▸ card_le_card h₄
        omega
      · have h₄ : b ∈ X := by aesop
        have : a ≠ b := fun hc => Q (hc ▸ h₄)
        exfalso
        exact this $ unique_bad_world a5 b5 c5 d5 e5 haX' h₄ imp q₀
    subst this
    rw [← hb]
    ext;simp
  | inr h =>
    left
    apply subset_antisymm
    · simp
    · intro i hi
      by_contra H
      have : i ∈ X \ (X ∩ Y) := by
        simp at H ⊢
        tauto
      rw [card_eq_zero.mp $ Nat.lt_one_iff.mp h] at this
      simp at this



theorem getStayAlive {n : ℕ} {ob : Finset (Fin (n + 2)) → Finset (Finset (Fin (n + 2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    (adHoc : ∀ (a : Fin (n + 2)), univ \ {a} ∈ ob univ → univ ∈ ob univ)
    (H₀ : ∃ Y X, X ∈ ob Y)
    {a : Fin (n+2)}
    {Y' X' : Finset (Fin (n+2))}
    (H₁ : a ∈ X' ∩ Y' ∧ (X' ∩ Y') \ {a} ∈ ob Y') : ob = stayAlive (n + 2) a := by
  have adHoc₂ : ∀ X, ∀ a ∈ X, X \ {a} ∈ ob X →
      ob {a} = {Y | a ∈ Y}.toFinset := ob_forbidden a5 b5 c5 $ ob_forbidden_self b5 d5 e5 adHoc
  have imp : (X' ∩ Y') \ {a} ∈ ob (X' ∩ Y') := e5 Y' (X' ∩ Y') ((X' ∩ Y') \ {a}) (by simp) H₁.2
      (by
      intro hc
      have : (X' ∩ Y') \ {a} = ∅ := by
        convert hc using 1
        ext;simp;tauto
      rw [this] at H₁
      exact a5 _ H₁.2)
  rw [funext_iff]
  intro X
  have hag := @agree_on_exclusion (n+2) ob b5 d5 e5
    (X' ∩ Y') X a H₁.1 (e5 Y' (X' ∩ Y') ( (X' ∩ Y') \ {a})
      (by simp) H₁.2 (by
        intro hc
        have : (X' ∩ Y') \ {a} = ∅ := by
          convert hc using 1
          ext;simp;tauto
        rw [this] at H₁
        exact a5 _ H₁.2
        ))
  by_cases G : X = {a}
  · subst G
    simp [stayAlive]
    have := adHoc₂ (X' ∩ Y') a H₁.1 imp
    rw [this]
    simp
    congr
    ext Y
    apply venn_singleton
  · ext Y
    simp [stayAlive]
    constructor
    · intro h
      have h' : X ∩ Y ∈ ob X := b5 X Y (X ∩ Y) (by ext;simp) h
      constructor
      · intro hc
        rw [hc] at h'
        exact a5 _ h'
      · by_cases H₂ : X \ {a} = ∅
        · rw [H₂]
          simp
        · have h₀ : X \ {a} ∈ ob (X \ {a}) := by
            have := agree_on_exclusion b5 d5 e5 H₁.1 imp H₂
            exact e5 (X) (X \ {a}) (X \ {a}) (by simp) this
              (by simp;simp_all)
          have q₀ : X ∩ Y = X
                ∨ X ∩ Y = X \ {a} := by
            apply all_or_almost' <;> tauto
          cases q₀ with
          | inl h =>
            rw [h]
            simp
          | inr h =>
            rw [h]
    · intro h
      have hX : X ≠ ∅ := by
        have := h.1
        contrapose! this
        rw [this]
        simp
      suffices X ∩ Y ∈ ob X by exact b5 X (X ∩ Y) Y (by simp) this

      have ht (H₀) := trivial_ob_of_nontrivial b5 d5 e5 H₁.1 imp H₀ hX
      cases all_or_almost h.2 with
      | inl h₀ =>
        rw [h₀]
        by_cases H₀ : a ∈ X
        · have h₀ : X \ {a} ∈ ob X := by
            apply hag
            contrapose! G
            exact subset_antisymm (sdiff_eq_empty_iff_subset.mp G) $ singleton_subset_iff.mpr H₀
          by_cases H₁ : X = univ
          · subst H₁
            apply adHoc a
            exact h₀
          · exact getUniv a5 b5 d5 e5 X ({a} ∪ Xᶜ) a (by
              contrapose! H₁
              simp at H₁
              cases H₁ with
              | inl h => exact h
              | inr h =>
                have : a ∈ Xᶜ := by
                  rw [h]
                  simp
                simp at this
                exfalso; exact this H₀) (by
                rw [inter_union_distrib_left]
                simp
                exact H₀) h₀
        · exact ht H₀
      | inr h' =>
        rw [h']
        by_cases H₀ : a ∈ X
        · exact agree_on_exclusion b5 d5 e5 H₁.1 imp (h' ▸ h.1)
        · have : X = X \ {a} := sdiff_singleton_eq_erase a X ▸ (Finset.erase_eq_of_not_mem H₀).symm
          rw [← this]
          exact ht H₀


/--
June 11, 2025
Only three models of CJ 1997 for a given `n`.
-/
theorem models_ofCJ_1997 {n : ℕ}
    (ob : Finset (Fin (n+2)) → Finset (Finset (Fin (n+2))))
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob):
  (∃ a, ob = stayAlive (n+2) a) ∨ ob = @alive (n+2) ∨ ob = fun _ => ∅ := by
  by_cases H₀ : ∃ Y X, X ∈ ob Y
  · by_cases H₁ : ∃ a Y X, a ∈ X ∩ Y ∧ (X ∩ Y) \ {a} ∈ ob Y
    · obtain ⟨a,Y,X,H₁⟩ := H₁
      left
      use a
      exact getStayAlive a5 b5 c5 d5 e5 (univ_ob_univ a5 d5 e5) H₀ H₁
    · right
      left
      push_neg at H₁
      exact getAlive a5 b5 c5 d5 e5 H₀ (by
        intro a Y X h hc
        have : (X ∩ Y) \ {a} ∈ ob Y :=  b5 Y (X \ {a}) ( (X ∩ Y) \ {a})
            (by ext;simp;tauto) hc
        by_cases H₂ : a ∈ Y
        · specialize H₁ a Y X (by simp;tauto)
          tauto
        · simp at h
          tauto)
  · push_neg at H₀
    right
    right
    rw [funext_iff]
    intro X
    specialize H₀ X
    rw [Finset.ext_iff]
    simp
    tauto



-- Over `Fin 0` two of the alternatives in `models_ofCJ_1997` both hold.
theorem models_ofCJ_1997₀ (ob : Finset (Fin 0) → Finset (Finset (Fin 0)))
    (a5 : A5 ob):
  ob = @alive 0 ∧ ob = fun _ => ∅ := by
  constructor
  · ext X Y
    rw [eq_empty_of_isEmpty Y, eq_empty_of_isEmpty X]
    simp [alive]
    exact a5 _
  · ext X Y
    simp
    rw [eq_empty_of_isEmpty Y]
    exact a5 _

lemma setsFin1 (X : Finset (Fin 1)) (h₀ : X ≠ {0}) : X = ∅ := by
  ext i
  simp
  contrapose! h₀
  have : i = 0 := Fin.fin_one_eq_zero i
  subst this
  ext j
  have : j = 0 := Fin.fin_one_eq_zero j
  subst this
  simp_all


/-- first two alternatives are actually the same -/
theorem models_ofCJ_1997₁
    (ob : Finset (Fin 1) → Finset (Finset (Fin 1)))
    (a5 : A5 ob) (b5 : B5 ob):
  (∃ a, ob = stayAlive 1 a) ∨ ob = @alive 1 ∨ ob = fun _ => ∅ := by
  by_cases H₁ : {0} ∈ ob {0}
  · right
    left
    rw [funext_iff]
    intro X
    simp [alive]
    ext Y
    simp
    by_cases h : X = {0}
    · by_cases h₀ : Y = {0}
      · rw [h,h₀]
        tauto
      · rw [setsFin1 _ h₀]
        simp
        exact a5 _
    · rw [setsFin1 _ h]
      simp
      exact fun hc => a5 _ $ b5 ∅ Y ∅ (by simp) hc
  · right
    right
    rw [funext_iff]
    intro X
    by_cases h : X = {0}
    · ext Y
      simp
      by_cases h₀ : Y = {0}
      · exact h₀ ▸ h ▸ H₁
      · rw [setsFin1 _ h₀]
        exact a5 _
    · rw [setsFin1 _ h]
      ext X
      simp
      intro hc
      exact a5 _ $ b5 ∅ X ∅ (by simp) hc


theorem models_ofCJ_1997_full {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob):
  (∃ a, ob = stayAlive n a) ∨ ob = alive n ∨ ob = fun _ => ∅ := by
  cases n with
  | zero =>
    have := models_ofCJ_1997₀ ob
    tauto
  | succ n =>
    cases n with
    | zero =>
      have := models_ofCJ_1997₁ ob
      tauto
    | succ n =>
      have := models_ofCJ_1997 ob
      tauto

/-- `stayAlive` arg the ``largest'' models of CJ97. -/
example {n : ℕ} (a : Fin n) (X : Finset (Fin n)) :
  alive n X ⊆ stayAlive n a X := by
  simp [alive, stayAlive]
  intro Y h₀
  simp at h₀ ⊢
  rw [inter_eq_left.mpr h₀.2]
  constructor
  · exact h₀.1
  · simp

/-- `stayAlive` is the only nontrivial model of CJ97. -/
example  {n : ℕ}
    (ob : Finset (Fin n) → Finset (Finset (Fin n)))
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    (h : ∃ Y, ∃ X ⊂ Y, X ∈ ob Y) : ∃ a, ob = stayAlive n a := by
  cases models_ofCJ_1997_full a5 b5 c5 d5 e5 with
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
      simp at h

theorem models_ofCJ_1997_equiv {n : ℕ}
    (ob : Finset (Fin n) → Finset (Finset (Fin n))) :
    (A5 ob ∧ B5 ob ∧ C5Strong ob ∧ D5 ob ∧ E5 ob) ↔
    ((∃ a, ob = stayAlive n a) ∨ ob = alive n ∨ ob = fun _ => ∅) := by
  constructor
  · intro h
    apply models_ofCJ_1997_full <;> tauto
  · intro h
    cases h with
    | inl h =>
      obtain ⟨a,ha⟩ := h
      have := @stayAlive_properties n a
      rw [ha]
      tauto
    | inr h =>
      cases h with
      | inl h =>
        rw [h]
        have := @alive_properties n
        tauto
      | inr h =>
        rw [h,A5,B5,C5Strong,D5,E5]
        simp
