import Deontic.Basic
import Deontic.Finset
import Deontic.Venn
import Deontic.Canonical
-- import Deontic.canon3

/-!

# The system of Carmo and Jones 1997

-/

open Finset

/- A family of deontic models in which the only obligation is to avoid
the dreaded world `e`. -/
def stayAlive {n : ℕ} (e : Fin n) : Finset (Fin n) → Finset (Finset (Fin n)) :=
  fun X => {Y | X ∩ Y ≠ ∅ ∧ X \ {e} ⊆ X ∩ Y}


def stayAlive' {n : ℕ} (e : Fin n) : Finset (Fin n) → Finset (Finset (Fin n)) :=
  fun X => {Y | X ∩ Y ≠ ∅ ∧ X \ {e} ⊆ Y}

lemma stayAlive_eq_stayAlive' {n : ℕ} (e : Fin n) : stayAlive e = stayAlive' e := by
  ext X Y
  simp [stayAlive, stayAlive']
  intro h
  constructor
  · intro h
    apply subset_trans h
    simp
  · intro h x hx
    simp
    constructor
    simp at hx
    tauto
    apply h hx

/-- A version of stayAlive where `e` is missing,
or if you will, e = n ∉ Fin n.
 -/
def alive (n : ℕ) : Finset (Fin n) → Finset (Finset (Fin n)) :=
  fun X => {Y | X ≠ ∅ ∧ Y ⊇ X }


theorem alive_properties (n : ℕ) :
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
    A5 (stayAlive e) ∧ B5 (stayAlive e) ∧ C5Strong (stayAlive e)
    ∧ D5 (stayAlive e) ∧ E5 (stayAlive e) := by
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
      · rw [show X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z) by compare]
        contrapose! H
        exact subset_empty.mp $ H ▸ subset_inter h₀.2 h₁.2
    · rw [show X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z) by compare]
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


def small₂ {n : ℕ} (A : Finset (Fin n)) :=
    2 ≤ #Aᶜ

/-- A convenient companion lemma for `card_le_one`. -/
lemma card_ge_two {k : ℕ} (A : Finset (Fin k)) :
    2 ≤ #A ↔ ∃ a ∈ A, ∃ b ∈ A, a ≠ b := by
  suffices (¬ (2 ≤ #A)) ↔ ¬ (∃ a ∈ A, ∃ b ∈ A, a ≠ b) by
    constructor
    intro h
    by_contra H
    tauto
    intro h
    by_contra H
    revert h
    simp only [imp_false]
    rw [← this]
    tauto
  push_neg
  rw [← card_le_one]
  omega


/-- `A` is a conditional cosubsingleton within `B`. -/
def ccss {n : ℕ} (B A : Finset (Fin n)) :=
    A ⊆ B → #(B \ A) ≤ 1

/-- `A` is a cocos in `B` if it's not a subset of `B`, or else is
a cosubsingleton of B.
-/
def cocos {n : ℕ} (B : Finset (Fin n)) : Finset (Finset (Fin n)) :=
    {A | A ⊆ B → #(B \ A) ≤ 1}

/-- Although `alive` and `cocos` are the same type of thing,
they are quite different.
However, `alive ⊆ cocos` so `alive` is `covering`;
and indeed `stayAlive` and `noObligations` are too by our main theorem.
-/
lemma alive_ne_cocos : alive 1 ≠ @cocos 1 := by
    unfold alive cocos
    intro hc
    have h₀ := congrFun hc
    specialize h₀ ({0} : Finset (Fin 1))
    have : (∅ : Finset (Fin 1)) ∈ (({Y | {(0:Fin 1)} ≠ (∅:Finset (Fin 1)) ∧ Y ⊇ {0}}) : Finset (Finset (Fin 1)))
        := by rw [h₀];simp
    simp at this


/-- `A` is relatively obligatory given `B`.
`A ∈ ifsub ob B`
means that A ∈ ob B, if it should happen that `A ⊆ B`.
-/
def ifsub {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n)))
    : Finset (Fin n) → Finset (Finset (Fin n)) :=
    fun B => {A | A ⊆ B → A ∈ ob B}

lemma ifsub_apply  {n : ℕ} {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    {A B : Finset (Fin n)} (h : A ∈ ifsub ob B) (h₀ : A ⊆ B) : A ∈ ob B := by
  simp [ifsub] at h;tauto

/-- `ob` has the `drop_at_most_one` property
if whenever a subset is obligatory, it is a relative cosubsingleton
  -/
def covering {n : ℕ}
    (ob : Finset (Fin n) → Finset (Finset (Fin n))) :=
    ∀ C, ∀ B, B ∈ ob C → B ∈ cocos C

lemma covering_def {n : ℕ}
    (ob : Finset (Fin n) → Finset (Finset (Fin n))) :
    covering ob ↔
    ∀ C, ob C ⊆ cocos C := by tauto

/-- A context `A` is *inter_ifsub obligatory* if `A` is obligatory in any larger context.
 -/
def inter_ifsub {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) (A : Finset (Fin n)) :=
    ∀ X, A ∈ ifsub ob X

def cosubsingleton {n : ℕ} (A : Finset (Fin n)) :=
    #Aᶜ ≤ 1

lemma cosubsingleton_eq_ccss_univ {n : ℕ} (A : Finset (Fin n)) :
    cosubsingleton A ↔ ccss univ A := by
  simp [cosubsingleton, ccss]
  tauto


/-- Not only is `a` "bad" but there is an obligation that singles it out. -/
def bad {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) (a : Fin n) :=
    ∃ X, a ∈ X ∧ X \ {a} ∈ ob X

def quasibad {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) (a : Fin n) := ∃ X Y, a ∈ X \ Y ∧ Y ∈ ob X


/-- The model according to which there are no obligations at all. -/
def noObligations (n : ℕ) : Finset (Fin n) → Finset (Finset (Fin n)) :=
  fun _ => ∅


lemma diff_diff {n : ℕ}
    {X Y : Finset (Fin n)} : X ∩ Y = Y \ (Y \ X) := by
  compare


section CJ97
variable {k : ℕ} {ob : Finset (Fin k) → Finset (Finset (Fin k))}

/-- Putting the commonly combined axioms 5(b)(d)(e) into a structure. -/
structure BDE where
    (b5 : B5 ob)
    (d5 : D5 ob)
    (e5 : E5 ob)
/--
If we add two worlds to a inter_ifsub set, then each one is preferable to
the other.
-/
lemma insert_single_ob_pair {A : Finset (Fin k)} (d5 : D5 ob)
  {a₁ a₂ : Fin k} (ha₁₂ : a₁ ≠ a₂)
    (h : inter_ifsub ob A) :
    A ∪ {a₂} ∈ ob (A ∪ {a₁, a₂}) := by
    convert fixD5 d5 (A ∪ {a₁, a₂}) (A ∪ {a₁}) A (by
      unfold inter_ifsub ifsub at h
      simp at h
      have := h (A ∪ {a₁}) (by simp)
      convert this using 1 <;> compare
      ) using 1
    ext j; simp;
    constructor
    · intro h
      cases h with
      | inl h => subst h; tauto
      | inr h => tauto
    · tauto

theorem single_ob_pair₁
    (c5 : C5 ob) (d5 : D5 ob) (e5 : E5 ob)
    {A : Finset (Fin k)} {a₁ a₂ : Fin k} (ha₂ : a₁ ≠ a₂)
    (ha₁ : a₂ ∉ A) (hcorr : {a₁, a₂} ∈ ob {a₁, a₂}) (h : inter_ifsub ob A) :
    {a₁} ∈ ob {a₁, a₂} := by
  let Z₁ := A ∪ {a₁}
  have h₁ : Z₁ ∈ ob {a₁, a₂} := e5 (A ∪ {a₁, a₂}) {a₁, a₂} Z₁ (by simp)
    (pair_comm a₁ a₂ ▸ insert_single_ob_pair d5 ha₂.symm h) $ ne_empty_of_mem <| by
    show a₁ ∈ _; simp [Z₁]
  have : {a₁} = Z₁ ∩ {a₁, a₂} := by
    ext b
    simp [Z₁]
    intro h₀ h₁
    rw [h₁] at h₀
    tauto
  have help₁ :  {a₁, a₂} ∩ Z₁ ∩ {a₁, a₂} ≠ ∅ := by
    rw [inter_comm]
    simp
    rw [inter_comm]
    rw [← this]
    simp
  exact this ▸ (c5 {a₁, a₂} Z₁ {a₁, a₂} h₁ hcorr help₁)

/-- A weaker version using the weaker C5 axiom.-/
theorem single_ob_pair
    (c5 : C5 ob) (d5 : D5 ob) (e5 : E5 ob)
    {A : Finset (Fin k)} {a₁ a₂ : Fin k} (ha₂ : a₁ ≠ a₂) (ha₀ : a₁ ∉ A)
    (ha₁ : a₂ ∉ A) (hcorr : {a₁, a₂} ∈ ob {a₁, a₂}) (h : inter_ifsub ob A) :
    ({a₁} ∈ ob {a₁, a₂} ∧ {a₂} ∈ ob {a₁, a₂}) := by
  have : ({a₁, a₂} : Finset (Fin k)) = {a₂, a₁} := by compare
  constructor
  · exact single_ob_pair₁ c5 d5 e5 ha₂ ha₁ hcorr h
  · exact this ▸ single_ob_pair₁ c5 d5 e5 (Ne.intro ha₂.symm) ha₀ (this ▸ hcorr) h

lemma C5_of_C5Strong
    (c5 : C5Strong ob) : C5 ob := by
  intro _ _ _ h₀ h₁ _
  apply c5 _ _ _ h₀ h₁

structure ACDE where
    (a : A5 ob) (c : C5Strong ob) (d : D5 ob) (e : E5 ob)

/-- If `A` is missing a self-obligatory pair
then `A` is not inter_ifsub.
A key use of the (too) strong version C5Strong.
 -/
theorem semiglobal_holds (f : @ACDE k ob)
    {A : Finset (Fin k)}
    {a₁ a₂ : Fin k} (ha₂ : a₁ ≠ a₂)
    (ha₀ : a₁ ∉ A) (ha₁ : a₂ ∉ A)
    (h : inter_ifsub ob A) :
    ¬ {a₁, a₂} ∈ ob {a₁, a₂} := by
  intro hcorr
  have ⟨h₃,h₄⟩:= @single_ob_pair k ob (C5_of_C5Strong f.c) f.d f.e A a₁ a₂ ha₂ ha₀ ha₁
    hcorr h
  have : ∅ ∈ ob {a₁, a₂} := by
    convert f.c {a₁, a₂} {a₁} {a₂} h₃ h₄ using 1
    ext b
    simp
    exact fun h => h ▸ ha₂
  exact f.a _ this

structure ADE where
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob)

structure ABCDE where
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)


/-- If `A` is small₂ (missing a pair of worlds)
then `A` is not inter_ifsub. -/
lemma global_holds_specific (t : @ABCDE k ob)
    {A : Finset $ Fin k} {a₁ a₂ : Fin k} (h₁ : a₁ ∉ A) (h₂ : a₂ ∉ A)
    (h₁₂ : a₁ ≠ a₂) :
    ¬ inter_ifsub ob A := by
  intro h
  apply semiglobal_holds ⟨t.a5, t.c5, t.d5, t.e5⟩ h₁₂ h₁ h₂ h
  have cx : CX ob := by
    convert conditional_explosion t.a5 (by convert t.b5)
        (by convert t.d5) (by convert t.e5)

  specialize cx A {a₁,a₂} (A ∪ {a₁,a₂}) (by
        unfold inter_ifsub ifsub at h
        simp only [mem_filter, mem_univ, true_and] at h
        apply h _ subset_union_left)
      (ne_empty_of_mem (by simp;tauto))
  convert cx using 2
  ext b
  simp
  constructor
  · intro h
    cases h with
    | inl h => subst h;tauto
    | inr h => subst h;tauto
  · tauto

theorem obSelfSdiff_of_bad (t : @BDE k ob)
    {a : Fin k} (hbad : bad ob a)
    {Y : Finset (Fin k)} (han : Y \ {a} ≠ ∅) :
    Y \ {a} ∈ ob Y := by
  have ⟨X,ha,h⟩ := hbad
  have : (X ∪ Y) \ {a} ∈ ob (X ∪ Y) := by
    convert t.d5 _ _ (X ∪ Y) (by simp) h (by simp) using 1
    exact union_sdiff_singleton ha
  have : (X ∪ Y) \ {a} ∈ ob Y := t.e5 (X ∪ Y) Y ((X ∪ Y) \ {a}) (by simp) this (by
      contrapose! han
      rw [← han]
      compare)
  exact t.b5 _ _ _ (by compare) this

theorem obSelf_of_obSelf (t : @BDE k ob)
    {X Y : Finset (Fin k)}
    (hX : X ∈ ob X) (hY : Y ≠ ∅) : Y ∈ ob Y := by
  have : X ∪ Y ∈ ob (X ∪ Y) := by
    convert t.d5 (Z := X ∪ Y) X X (by simp) hX (by simp) using 1
    compare
  exact t.b5 _ _ _ (by simp) $ t.e5 _ Y _ subset_union_right this (by compare)

lemma obSelf_univ
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob) (a : Fin k)
    (ha : univ \ {a} ∈ ob univ) : univ ∈ ob univ := by
  by_cases H : k = 0
  · subst H;have := a.2; simp at this
  have ⟨n,hn⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero H
  subst hn
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

lemma sdiff_union_sdiff (A B C : Finset (Fin k)) :
    A \ C ⊆ A \ B ∪ B \ C := by
      intro i hi
      simp at hi ⊢
      tauto

lemma diff_ne {a : Fin k} {X : Finset (Fin k)}
    (ha : X ≠ {a}) (he : X ≠ ∅) : X \ {a} ≠ ∅ := by simp;tauto

lemma sdiff_union_sdiff_eq
{a : Fin k} {X : Finset (Fin k)}
(ha : a ∈ X) : univ \ {a} = univ \ X ∪ X \ {a} := by
    apply subset_antisymm
    · apply sdiff_union_sdiff
    · intro i hi
      simp at hi ⊢
      cases hi with
        | inl h => exact fun hc => h $ hc ▸ ha
        | inr h => exact h.2




/--
If every everywhere-inter_ifsub set is a cosubsingleton of `univ` then
every somewhere-inter_ifsub set is a cosubsingleton there.
Because we can just union up with the relative complement.

This version is "theoretical" in that it is not so easy to apply
but has a beautiful logical structure.
 -/
theorem local_of_global_theoretical
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob)
    (h : ∀ A, ((∀ B, A ∈ ifsub ob B) → ∀ B, ccss B A))
    -- of course, `∀ B, ccss B A ↔ cosubsingleton A`, but it looks neater this way
    {A B : Finset (Fin k)} (hBC₁ : A ∈ ifsub ob B) : ccss B A := by
  unfold ccss
  by_contra hBC
  simp only [Classical.not_imp] at hBC
  have : 2 ≤ #((univ : Finset (Fin k))) := by
    apply le_trans
    show 2 ≤ #(B \ A)
    omega
    apply card_le_card
    simp
  have : ∃ m, k = m + 2 := by
    refine Nat.exists_eq_add_of_le' ?_
    convert this
    simp
  have hBC₀ := hBC.1
  have hBC₂ := hBC.2
  let U := univ \ B ∪ A -- the key step
  have hU₁ : inter_ifsub ob U := by
      have h₁ : (univ \ B ∪ A) ∈ ob univ := @d5 B A univ hBC₀
            (ifsub_apply hBC₁ hBC₀) (by simp)
      intro X
      unfold ifsub
      simp
      intro hX
      exact e5 _ _ _ (subset_univ _) h₁ $
        (inter_eq_right.mpr hX).symm ▸ fun hc => a5 univ $ hc ▸ h₁
  specialize h U hU₁ univ (by simp)
  unfold U at h
  have : univ \ (univ \ B ∪ A) = B \ A := by compare
  rw [this] at h
  omega


/-- A trivial consequence of `local_of_global_theoretical`.  -/
theorem local_of_global'
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob) {B C : Finset (Fin k)}
    (hBC₀:  #(C \ B) ≥ 2)
    (hBC₁ : B ⊆ C)
    (hBC₂ : B ∈ ob C) :
     ∃ A, #Aᶜ ≥ 2 ∧ inter_ifsub ob A := by
  have := fun a ↦ Not.imp a $ @local_of_global_theoretical k ob a5 d5 e5
  specialize this (by
    push_neg
    use B, C
    unfold ifsub
    constructor
    · simp
      exact fun _ => hBC₂
    · unfold ccss
      push_neg
      constructor
      exact hBC₁
      omega)
  push_neg at this
  obtain ⟨A,hA⟩ := this
  use A
  have ⟨U,hU⟩ := hA.2
  unfold ccss at hU
  simp only [Classical.not_imp] at hU
  refine ⟨?_, hA.1⟩
  calc 2 ≤ #(U \ A) := by omega
       _ ≤ _        := by apply card_le_card;intro;simp


/--
Given that no small₂ set is inter_ifsub (which is not automatic here since
we don't assume B5 and C5),
an obligatory set cannot be more than 1 world away from its larger context.

  If every universally inter_ifsub set is cosubsingle
  then every somewhere inter_ifsub set is there-cosubsingle.
-/
theorem local_of_global
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob)
    (large_of_ob: ∀ A, inter_ifsub ob A → cosubsingleton A) :
                   covering ob := by
  by_cases H : k ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp H with (h | h)
    all_goals try
        subst h
        unfold covering cocos
        intro C B hBC
        simp_rw [card_le_one]
        simp
        try exact Unique.uniq instUniqueOfIsEmpty B
  · have ⟨m,hm⟩ : ∃ m, k = m + 2 := Nat.exists_eq_add_of_le' (by simp at H; exact H)
    subst hm
    intro B C ho
    simp [cocos]
    intro hBC
    by_contra H
    have ⟨A,hA⟩ := local_of_global' a5 d5 e5 (B := C) (C := B) (by omega) hBC ho
    specialize large_of_ob A hA.2
    unfold cosubsingleton at large_of_ob
    omega

/-- If `A` is small₂ then `A` is not inter_ifsub.
This is just some set-wrangling on top of `global_holds_specific`.
-/
lemma global_holds (t : @ABCDE k ob)
    (A : Finset (Fin k)) (hs : small₂ A) :
    ¬ inter_ifsub ob A := by
  unfold small₂ at hs
  rw [card_ge_two] at hs
  simp at hs
  have ⟨_,h₁,_,h₂,h₁₂⟩:= hs
  exact global_holds_specific t h₁ h₂ h₁₂

/-- A direct consequence of `global_holds` and `local_of_global`. -/
theorem local_holds (t : @ABCDE k ob) :
    covering ob := by
  by_cases H : k ≤ 1
  · have : k = 0 ∨ k = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp H
    rcases this with (h | h)
    all_goals
        subst h
        unfold covering cocos
        intro C B h₀
        simp only [mem_filter, mem_univ, true_and]
        rw [card_le_one]
        simp
  · have ⟨n, hn⟩ : ∃ n, k = n + 2 := by
        simp at H
        exact Nat.exists_eq_add_of_le' H
    subst hn
    unfold covering cocos
    by_contra H
    push_neg at H
    simp only [mem_filter, mem_univ, true_and, Classical.not_imp] at H
    obtain ⟨B,C,h₀,h₁,h₂⟩ := H
    have (A) (hA : inter_ifsub ob A) : cosubsingleton A := by
        contrapose! hA
        apply global_holds t A
        unfold small₂
        rw [card_ge_two]
        unfold cosubsingleton at hA
        rw [card_le_one] at hA
        push_neg at hA
        exact hA
    have := local_of_global t.a5 t.d5 t.e5 this _ _ h₀
    unfold cocos at this
    simp at this
    specialize this h₁
    omega

/-- Allow `B` and `C` to be implicit in `local_holds`. -/
def local_holds_apply (t : @ABCDE k ob)
    {B C : Finset (Fin k)} := local_holds t B C

/-- An obvious consequence of `B5`. -/
lemma obSelf_of_ob_of_subset
    (b5 : B5 ob)
    {X Y : Finset (Fin k)} (hd : Y ⊆ X)
    (h : X ∈ ob Y) : Y ∈ ob Y := by
  nth_rewrite 2 [← inter_eq_right.mpr hd]
  exact b5 Y X (X ∩ Y) (by simp) h


lemma not_ob_of_almost
    (H₁ : ∀ a, ¬ quasibad ob a)
    {X Y : Finset (Fin k)}
    (h₀ : #(Y \ X) = 1) : X ∉ ob Y := fun hc => by
  unfold quasibad at H₁
  push_neg at H₁
  have ⟨a,ha⟩: ∃ a, Y \ X = {a} := card_eq_one.mp h₀
  exact H₁ a Y X (singleton_subset_iff.mp $ by rw [← ha]) hc

lemma obSelf_of_ob_of_almost_subset
  (b5 : B5 ob)
  (H₁ : ∀ a, ¬ quasibad ob a)
  {X Y : Finset (Fin k)}
  (h : X ∈ ob Y)
  (hd : #(Y \ X) ≤ 1)
  : Y ∈ ob Y := by
    cases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with
    | inl h₀ =>
      exact obSelf_of_ob_of_subset b5
        (sdiff_eq_empty_iff_subset.mp $ card_eq_zero.mp h₀) h
    | inr h₀ => exact False.elim $ not_ob_of_almost H₁ h₀ h

theorem at_most_one_quasibad {k : ℕ} {ob : Finset (Fin k) → Finset (Finset (Fin k))}
    (t : @ABCDE k ob)
    {X Y : Finset (Fin k)} (h : Y ∈ ob X)
    {a : Fin k} (ha : a ∈ X \ Y) : X ∩ Y = X \ {a} := by
    apply subset_antisymm
    · intro i hi
      simp at ha hi ⊢
      exact ⟨hi.1, fun hc => ha.2 $ hc ▸ hi.2⟩
    · intro i hi
      simp at hi ⊢
      constructor
      · exact hi.1
      · by_contra H₀
        apply two_in_sdiff' _ _ _ _ ha hi.1 hi.2 H₀
        have := local_holds_apply t (t.b5 _ _ (X ∩ Y) (by compare) h) --inter_subset_left
        unfold cocos at this
        simp at this
        exact this

/-
The implications are
bad →[∅] quasibad →[ABCDE5] bad
-/
lemma bad_of_quasibad (t : @ABCDE k ob)
    (a : Fin k) (h : quasibad ob a) : bad ob a := by
    obtain ⟨U,V,hUV⟩ := h
    use U
    constructor
    · rw [mem_sdiff] at hUV
      exact hUV.1.1
    · rw [← at_most_one_quasibad t hUV.2 hUV.1]
      apply t.b5 U V (U ∩ V)
      compare

lemma sub_alive  (a5 : A5 ob) (b5 : B5 ob)
    (H₁ : ∀ a, ¬ quasibad ob a) : ∀ Y, ob Y ⊆ alive k Y := by
    intro X Y h
    simp [alive]
    constructor
    · exact fun hc => a5 _ $ b5 _ _ _ (by simp) $ hc ▸ h
    · by_contra H
      unfold quasibad at H₁
      push_neg at H₁
      have ⟨a,ha⟩ : ∃ a, a ∈ X \ Y := Nonempty.exists_mem $ sdiff_nonempty.mpr H
      specialize H₁ a X Y
      tauto

lemma alive_sub (t : @ABCDE k ob) (H₀ : ob ≠ noObligations k)
    (H₁ : ∀ a, ¬ quasibad ob a) : ∀ Y, alive k Y ⊆ ob Y := by
  intro X Y h₂
  simp [alive] at h₂
  have H₀ : ∃ Y X, X ∈ ob Y := by
    contrapose! H₀
    ext Y X
    simp [noObligations]
    apply H₀
  obtain ⟨Y',X',h'⟩ := H₀
  have := local_holds_apply t (t.b5 _ _ (X' ∩ Y') (by simp) h')
  simp [cocos] at this
  have := obSelf_of_ob_of_almost_subset t.b5 H₁ h' this
  exact t.b5 X X Y (by compare) $ obSelf_of_obSelf ⟨t.b5, t.d5, t.e5⟩
    this
    h₂.1

lemma alive_of_no_quasibad (t : @ABCDE k ob) (H₀ : ob ≠ noObligations k)
    (H₁ : ∀ a, ¬ quasibad ob a) : ob = alive k := (Set.eqOn_univ _ _).mp fun Y _ => by
  apply subset_antisymm
  apply sub_alive t.a5 t.b5 H₁
  apply alive_sub t H₀ H₁


theorem unique_bad (t : @ABCDE k ob) -- maybe five.d instead of t.d5?
    {a b : Fin k} (ha : bad ob a) (hb : bad ob b) : a = b := by
  obtain ⟨X,_, hoa⟩ := ha
  obtain ⟨Y,_, hob⟩ := hb
  have h₁ : (X ∪ Y) \ {a} ∈ ob (X ∪ Y) := by
    convert t.d5 _ _ (X ∪ Y) (by simp) hoa (by simp) using 1
    apply union_diff_singleton ; tauto
  have h₂ : (X ∪ Y) \ {b} ∈ ob (X ∪ Y) := by
    convert t.d5 _ _ (X ∪ Y) (by simp) hob (by simp) using 1
    rw [union_comm]
    apply union_diff_singleton ; tauto
  have : #({a,b}) ≤ 1 := by
    have := local_holds_apply t (t.c5 _ _ _ h₁ h₂)
    unfold cocos at this
    simp at this
    specialize this (subset_trans inter_subset_union $ union_subset sdiff_subset sdiff_subset)
    convert this using 2
    apply pair_venn <;> tauto
  rw [card_le_one] at this
  simp at this
  tauto

theorem bad_cosubsingleton_of_ob (t : @ABCDE k ob)
    {a : Fin k}
    (hbad : bad ob a)
    {X Y : Finset (Fin k)}
    (h' : X ∩ Y ∈ ob X) : -- or just Y ∈ ob X
    X ∩ Y = X ∨ X ∩ Y = X \ {a} := by
  obtain ⟨X',haX',imp⟩ := hbad
  have := local_holds_apply t h'
  unfold cocos at this
  simp only [mem_filter, mem_univ, inter_subset_left, forall_const,
    true_and] at this

  cases Nat.eq_or_lt_of_le this with
  | inl h =>
    right
    have ⟨b,hb⟩ : ∃ b, X \ (X ∩ Y) = {b} := card_eq_one.mp h
    have hbX : X ∩ Y = X \ {b} := by
      rw [← hb, ← diff_diff]
      compare
    have : b ∈ X := by
      apply singleton_subset_iff.mp
      rw [← hb]
      simp
    have ha : bad ob a := by use X'
    have hb : bad ob b :=⟨X,this, hbX ▸ h'⟩
    exact unique_bad t ha hb ▸ hbX
  | inr h =>
    simp at h
    exact .inl $ subset_antisymm inter_subset_left $ subset_inter (subset_refl _) h

theorem obSelf_of_obSelfSdiff (t : @BDE k ob)
    {X : Finset (Fin k)} {a : Fin k}
    (h : X \ {a} ∈ ob X) (han : X \ {a} ≠ ∅) : X ∈ ob X := by
  have haX : X ≠ ∅ := by contrapose! han;subst han;simp
  apply obSelf_of_obSelf t _ haX
  show X \ {a} ∈ ob (X \ {a})
  exact t.e5 X (X \ {a}) (X \ {a}) (by simp) h (by
    rw [inter_self]
    exact han
  )

/-- If `X` contains an element `b≠a` where `a` is a given bad world,
then `X` is self-obligatory. -/
lemma obSelf_of_bad.nonsingle (t : @BDE k ob)
    {a : Fin k} (hbad : bad ob a) {X : Finset (Fin k)}
    (ha : X ≠ {a})
    (he : X ≠ ∅) : X ∈ ob X :=
    obSelf_of_obSelfSdiff t (han := diff_ne ha he) $
    obSelfSdiff_of_bad t hbad (han := diff_ne ha he)

/-- Bad singletons are self-obligatory. Proved from first
principles. -/
lemma obSelf_of_bad.single (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
    {a : Fin k} (hbad : bad ob a) : {a} ∈ ob {a} := b5 _ univ _ (by simp) <| by
  apply e5 _ _ _ (subset_univ _)
  apply obSelf_univ a5 d5 e5 a
  obtain ⟨X,ha,ha'⟩ := hbad
  rw [sdiff_union_sdiff_eq ha]
  apply d5 _ _ _ sdiff_subset ha' (subset_univ _)
  simp

theorem obSelf_of_bad
    (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
    (hbad : ∃ a, bad ob a) {X : Finset (Fin k)}
    (he : X ≠ ∅) : X ∈ ob X := by
  obtain ⟨a,hbad⟩ := hbad
  by_cases ha : X = {a}
  · exact ha ▸ obSelf_of_bad.single a5 b5 d5 e5 hbad
  · exact      obSelf_of_bad.nonsingle ⟨b5, d5, e5⟩ hbad ha he

theorem sub_stayAlive_of_bad (t : @ABCDE k ob)
    {a : Fin k} (hbad : bad ob a) : ∀ Y, ob Y ⊆ stayAlive a Y:= by
    intro X Y
    simp [stayAlive]
    · intro h
      have h' : X ∩ Y ∈ ob X := t.b5 X Y (X ∩ Y) (by compare) h
      -- this line is unnecessary if we generalize lemma below
      constructor
      · exact fun hc => t.a5 _ <| hc ▸ h'
      · cases bad_cosubsingleton_of_ob t hbad h' with
          | inl h => rw [h]; simp
          | inr h => rw [h]


theorem stayAlive_sub_of_bad
    (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
    {a : Fin k} (hbad : bad ob a) :
    ∀ Y, stayAlive a Y ⊆ ob Y := fun X Y h => b5 _ (X ∩ Y) _ (by simp) $ by
    simp [stayAlive] at h
    cases all_or_almost h.2 with
      | inl h₀ =>
            rw [h₀]
            exact obSelf_of_bad a5 b5 d5 e5 ⟨a, hbad⟩ fun hc => by simp [hc] at h
      | inr h₀ => exact h₀ ▸ obSelfSdiff_of_bad ⟨b5, d5, e5⟩ hbad (Y := X) $ h₀ ▸ h.1


theorem stayAlive_of_bad (t : @ABCDE k ob)
    {a : Fin k} (hbad : bad ob a) : ob = stayAlive a :=
        (Set.eqOn_univ _ _).mp fun Y _ => subset_antisymm
        (sub_stayAlive_of_bad t hbad Y)
        (stayAlive_sub_of_bad t.a5 t.b5 t.d5 t.e5 hbad Y)

/--
There are only three models of CJ 1997 for a given `n ≥ 1`:
`stayAlive`, `alive`, `noObligations`.
-/
theorem models_ofCJ_1997 (t : @ABCDE k ob) : --June 11, 2025
  (∃ a, ob = stayAlive a) ∨ ob = alive k ∨ ob = noObligations k := by
  by_cases H₀ : ob = noObligations k
  · exact .inr $ .inr H₀
  · by_cases H₁ : ∃ a, quasibad ob a
    · left
      obtain ⟨a,H₁⟩ := H₁
      use a
      exact stayAlive_of_bad t (bad_of_quasibad t a H₁)
    · push_neg at H₁
      exact .inr $ .inl $ alive_of_no_quasibad t H₀ H₁
      -- see how much we can eliminate semi-bad completely

end CJ97


-- Over `Fin 0` two of the alternatives in `models_ofCJ_1997` both hold.
theorem models_ofCJ_1997₀ (ob : Finset (Fin 0) → Finset (Finset (Fin 0)))
    (a5 : A5 ob):
  ob = @alive 0 ∧ ob = noObligations 0 := by
  constructor
  · ext X Y
    rw [eq_empty_of_isEmpty Y, eq_empty_of_isEmpty X]
    simp [alive]
    exact a5 _
  · ext X Y
    simp [noObligations]
    exact eq_empty_of_isEmpty Y ▸ a5 _

lemma setsFin1 (X : Finset (Fin 1)) (h₀ : X ≠ {0}) : X = ∅ := by
  ext i
  rw [Fin.fin_one_eq_zero i]
  contrapose! h₀
  ext j
  rw [Fin.fin_one_eq_zero j]
  compare

/-- An exhaustive list of models of `A5 ∧ B5` over `Fin 1`.
The first two alternatives are actually the same -/
theorem models_ofCJ_1997₁
    (ob : Finset (Fin 1) → Finset (Finset (Fin 1)))
    (a5 : A5 ob) (b5 : B5 ob):
  (∃ a, ob = stayAlive a) ∨ ob = alive 1 ∨ ob = noObligations 1 := by
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
      simp [noObligations]
      by_cases h₀ : Y = {0}
      · exact h₀ ▸ h ▸ H₁
      · rw [setsFin1 _ h₀]
        exact a5 _
    · rw [setsFin1 _ h]
      ext X
      simp [noObligations]
      intro hc
      exact a5 _ $ b5 ∅ X ∅ (by simp) hc

theorem models_ofCJ_1997_equiv {n : ℕ}
    (ob : Finset (Fin n) → Finset (Finset (Fin n))) :
    (A5 ob ∧ B5 ob ∧ C5Strong ob ∧ D5 ob ∧ E5 ob) ↔
    ((∃ a, ob = stayAlive a) ∨ ob = alive n ∨ ob = noObligations n) := by
  constructor
  · intro h
    apply models_ofCJ_1997
    refine { a5 := h.1, b5 := h.2.1, c5 := h.2.2.1, d5 := h.2.2.2.1, e5 := h.2.2.2.2 }
  · intro h
    cases h with
    | inl h =>
      obtain ⟨a,ha⟩ := h
      exact ha ▸ stayAlive_properties a
    | inr h =>
      cases h with
      | inl h =>
        exact h ▸ alive_properties n
      | inr h =>
        rw [h,A5,B5,C5Strong,D5,E5]
        simp [noObligations]
