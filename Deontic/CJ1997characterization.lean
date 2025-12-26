import Deontic.Basic
import Deontic.Finset
import Deontic.Venn
import Deontic.Canonical
-- import Deontic.canon3

/-!

# The system of Carmo and Jones 1997

`alive_properties` (used @ end)
`stayAlive_properties` (used @ end)
Theorems that use all of [abcde5] are indicated in [brackets].

`prefer_either_of_good` [d5]
--> `not_good_of_disjoint_selfob_pair` [acde5]
--> [`not_good_of_small₂_specific`] --> [`not_good_of_small₂`]
                                        |
                                        v
            [`unique_bad_world`] <- [`drop_at_most_one_CJ97`]
                    |
                    v
            [`all_or_almost'`] `obSelf` [abde5] <--- `obSelf_sdiff`     `drop_at_most_one_of_no_good_small₂`
                             \       |             /         |[bde5]                    |[ade]
                              \/     v            /          |                          v
`trivial_ob_of_nontrivial` -->[`getStayAlive`]<- /           |                  `drop_at_most_one_of_no_small₂_good`
      [bde]                           |                      |                          |[ade]
                                      v                      v                          v
              `univ_ob_univ` --->  [`models_ofCJ_1997`]  <- [`getAlive`] <--- [`drop_at_most_one_CJ97`]
                  [ade5]
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


section lemma9_1996




def small₂ {n : ℕ} (A : Finset (Fin n)) :=
    2 ≤ #Aᶜ

/-- `A` is a conditional cosubsingleton within `B`. -/
def ccss {n : ℕ} (B A : Finset (Fin n)) :=
    A ⊆ B → #(B \ A) ≤ 1

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

/-- A context `A` is *good* if `A` is obligatory in any larger context.
 -/
def good {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) (A : Finset (Fin n)) :=
    ∀ X, A ∈ ifsub ob X


def cosubsingleton {n : ℕ} (A : Finset (Fin n)) :=
    #Aᶜ ≤ 1

lemma cosubsingleton_eq_ccss_univ {n : ℕ} (A : Finset (Fin n)) :
    cosubsingleton A ↔ ccss univ A := by
  simp [cosubsingleton, ccss]
  tauto


/--
If we add two worlds to a good set, then each one is preferable to
the other.
-/
lemma prefer_either_of_good
  {n : ℕ} {ob : Finset (Fin n) → Finset (Finset (Fin n))} {A : Finset (Fin n)} (d5 : D5 ob)
  {a₁ a₂ : Fin n} (ha₁₂ : a₁ ≠ a₂)
    (h : good ob A) :
    A ∪ {a₂} ∈ ob (A ∪ {a₁, a₂}) := by
    convert fixD5 d5 (A ∪ {a₁, a₂}) (A ∪ {a₁}) A (by
      unfold good ifsub at h
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

end lemma9_1996

/-- If `A` is missing a self-obligatory pair
then `A` is not good.
 -/
theorem not_good_of_disjoint_selfob_pair {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))} {A : Finset (Fin n)}
    {a₁ a₂ : Fin n} (ha₀ : a₁ ∉ A) (ha₁ : a₂ ∉ A) (ha₂ : a₁ ≠ a₂)
    (hcorr : {a₁, a₂} ∈ ob {a₁, a₂})
    (a5 : A5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob) :
    ¬ good ob A := by
  intro h
  let Z₁ := A ∪ {a₁}
  let Z₂ := A ∪ {a₂}
  have h₁ : Z₁ ∈ ob {a₁, a₂} := e5 (A ∪ {a₁, a₂}) {a₁, a₂} Z₁ (by simp)
    (pair_comm a₁ a₂ ▸ prefer_either_of_good d5 ha₂.symm h) $ ne_empty_of_mem <| by
    show a₁ ∈ _; simp [Z₁]
  have h₂ : Z₂ ∈ ob {a₁, a₂} := e5 (A ∪ {a₁, a₂}) {a₁, a₂} Z₂ (by simp)
    (prefer_either_of_good d5 ha₂ h) $ ne_empty_of_mem <| by
    show a₂ ∈ _; simp [Z₂]
  have : {a₁} = Z₁ ∩ {a₁, a₂} := by
    ext b
    simp [Z₁]
    intro h₀ h₁
    rw [h₁] at h₀
    tauto
  have h₃ : {a₁} ∈ ob {a₁, a₂} := this ▸ c5 {a₁, a₂} Z₁ {a₁, a₂} h₁ hcorr
  have : {a₂} = Z₂ ∩ {a₁, a₂} := by
    ext b;simp [Z₂]
    intro h₁ h₀
    cases h₀ with
    | inl h => subst h;tauto
    | inr h => subst h;tauto
  have h₄ : {a₂} ∈ ob {a₁, a₂} := by
    have hh := c5 {a₁, a₂} Z₂ {a₁, a₂} h₂ hcorr
    rw [← this] at hh
    exact hh
  have : ∅ ∈ ob {a₁, a₂} := by
    convert c5 {a₁, a₂} {a₁} {a₂} h₃ h₄ using 1
    ext b
    simp
    exact fun h => h ▸ ha₂
  exact a5 _ this

/-- If `A` is small₂ (missing a pair of worlds)
then `A` is not good. -/
lemma not_good_of_small₂_specific
    {n : ℕ} {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    {A : Finset <| Fin n} {a₁ a₂ : Fin n} (ha' : a₁ ∉ A ∧ a₂ ∉ A ∧ a₁ ≠ a₂) :
    ¬ good ob A := by
  intro h
  have cx : CX ob := by
    convert conditional_explosion a5 (by convert b5) (by convert d5) (by convert e5)
  have : {a₁, a₂} ∈ ob {a₁, a₂} := by
    specialize cx A {a₁,a₂} (A ∪ {a₁,a₂}) (by unfold good ifsub at h;simp at h;apply h;simp;intro i hi;simp;tauto)
      (ne_empty_of_mem (by simp;tauto))
    convert cx using 2
    simp
    ext b;simp
    constructor
    intro h
    cases h with
    | inl h => subst h;tauto
    | inr h => rw [h];tauto
    tauto
  exact not_good_of_disjoint_selfob_pair ha'.1 ha'.2.1 ha'.2.2 this a5 c5 d5 e5 h

lemma sdiff_two {n : ℕ}
    {B C : Finset (Fin n)} (hBC₀ : #(C \ B) ≥ 2) (hBC₁ : B ⊆ C) :
    #(univ \ C ∪ B) ≤ n - 2 := by
    have : Disjoint (univ \ C) B := fun D hD₀ hD₁ i hi => False.elim $ by
      have h₁ := hD₀ hi
      rw [mem_sdiff] at h₁
      exact h₁.2 $ hBC₁ $ hD₁ hi
    rw [card_sdiff] at hBC₀
    rw [card_union_of_disjoint this, card_sdiff,
      card_univ, Fintype.card_fin, ← Nat.sub_add_comm]
    · simp
      suffices #B ≤ #C - 2 by omega
      suffices 2 ≤ #C - #B by omega
      have : B ∩ C = B := by compare
      rw [this] at hBC₀
      exact hBC₀
    have : n = #(Finset.univ : Finset (Fin n)) := by simp
    simp_rw [this]
    apply Finset.card_le_card;simp

/-- `ob` has the `drop_at_most_one` property
if whenever a subset is obligatory, it is a relative cosubsingleton
  -/
def drop_at_most_one {n : ℕ}
    (ob : Finset (Fin n) → Finset (Finset (Fin n))) :=
    ∀ B C, B ⊆ C → B ∈ ob C → #(C \ B) ≤ 1

def covering {n : ℕ}
    (ob : Finset (Fin n) → Finset (Finset (Fin n))) :=
    ∀ B C, B ∈ ob C → B ⊆ C → #(C \ B) ≤ 1

lemma drop_at_most_one_eq_covering_of_ob {n : ℕ}
    (ob : Finset (Fin n) → Finset (Finset (Fin n))) :
    drop_at_most_one ob ↔ covering ob := by
  simp [drop_at_most_one, covering]
  tauto




/-- A context `Y` is obligatory given itself, provided
that `∃ a ∉ Y, ∃ X, a ∈ X ∧ X \ {a} ∈ ob X`.
-/
theorem trivial_ob_of_nontrivial {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob) {X Y : Finset (Fin n)}
    {a : Fin n} (ha : a ∈ X) (hX : X \ {a} ∈ ob X) (haY : a ∉ Y)
    (hY : Y ≠ ∅) : Y ∈ ob Y := by
  have : Y ⊆ Y ∩ ((X ∪ Y) \ X ∪ X \ {a}) := by
    intro y hy
    simp
    constructor
    exact hy
    by_cases H : y ∈ X
    · right
      simp_all
      intro hc
      subst hc
      exact haY hy
    · tauto
  have g₀ : Y ∩ ((X ∪ Y) \ X ∪ X \ {a}) ≠ ∅ := by
    contrapose! hY
    apply subset_empty.mp
    apply subset_trans this
    rw [hY]
  have g₁ : Y = ((X ∪ Y) \ X ∪ X \ {a}) ∩ Y := by
    ext i;simp
    intro hi
    by_cases H : i ∈ X
    · exact .inr ⟨H, fun hc => haY $ hc ▸ hi⟩
    · exact .inl ⟨.inr hi, H⟩
  have h₀ := d5 _ _ (X ∪ Y) sdiff_subset hX subset_union_left
  have h₁ := e5 _ _ _ subset_union_right h₀ g₀
  have h₂ := b5 _ _ (((X ∪ Y) \ X ∪ X \ {a}) ∩ Y)
    (by simp) h₁
  convert h₂


theorem obSelf_sdiff {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob) {X Y : Finset (Fin n)}
    {a : Fin n} (ha : a ∈ X) (h : X \ {a} ∈ ob X) (haY : Y \ {a} ≠ ∅) :
    Y \ {a} ∈ ob Y := by
  have : (X ∪ Y) \ {a} ∈ ob (X ∪ Y) := by
    convert d5 _ _ (X ∪ Y) (by simp) h (by simp) using 1
    exact union_sdiff_singleton ha haY
  have : (X ∪ Y) \ {a} ∈ ob Y := e5 (X ∪ Y) Y ((X ∪ Y) \ {a}) (by simp) this (by
      contrapose! haY
      rw [← haY]
      compare)
  exact b5 _ _ _ (by compare) this

theorem obSelf_transfer {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob) {X Y : Finset (Fin n)}
    (hX : X ∈ ob X) (hY : Y ≠ ∅) : Y ∈ ob Y := by
  have : X ∪ Y ∈ ob (X ∪ Y) := by
    convert d5 (Z := X ∪ Y) X X (by simp) hX (by simp) using 1
    compare
  exact b5 _ _ _ (by simp) $ e5 _ Y _ subset_union_right this (by compare)

theorem obSelf {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
    (X Y : Finset (Fin n)) (a : Fin n)
    (hY : Y \ {a} ≠ ∅) (hh : X ∩ Y = {a})
    (h : X \ {a} ∈ ob X) : X ∈ ob X := by
  have ha : a ∈ X ∩ Y := by rw [hh];simp
  simp at ha
  have h₀ : Y \ {a} ∈ ob Y := obSelf_sdiff b5 d5 e5 ha.1 h hY
  have : Y \ {a} ∈ ob (Y \ {a}) := e5 _ _ _ sdiff_subset h₀
      ((inter_self (Y \ {a})).symm ▸ fun hc => a5 Y $ hc ▸ h₀)
  exact obSelf_transfer b5 d5 e5
    this
    $ ne_empty_of_mem ha.1


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
    (ha : univ \ {a} ∈ ob univ) : univ ∈ ob univ := by
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

lemma large_iff_cosubsingleton {n : ℕ} (A : Finset (Fin (n+1))) :
    cosubsingleton A ↔  #A ≥ n := by
    unfold cosubsingleton
    have : #Aᶜ = #(univ \ A) := by congr
    rw [this]
    have : #(univ \ A) = #((univ : Finset (Fin (n+1)))) - #A := by
        refine card_sdiff_of_subset ?_
        simp
    rw [this]
    have : #((univ : Finset (Fin (n+1)))) = n+1 := card_fin (n + 1)
    rw [this]
    omega

/-- A beautiful way to look at a key part of this file.
If every everywhere-good set is a cosubsingleton of `univ` then
every somewhere-good set is a cosubsingleton there.
Because we can just union up with the relative complement.
 -/
theorem global_to_local {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob)
    (h : ∀ A, ((∀ B, A ∈ ifsub ob B) → ∀ B, ccss B A))
    -- of course, `∀ B, ccss B A ↔ cosubsingleton A`, but it looks neater this way
    {A B : Finset (Fin n)} (hBC₁ : A ∈ ifsub ob B) : ccss B A := by
  unfold ccss
  by_contra hBC
  simp at hBC
  have : 2 ≤ #((univ : Finset (Fin (n)))) := by
    apply le_trans
    show 2 ≤ #(B \ A)
    omega
    apply card_le_card
    simp
  have : ∃ m, n = m + 2 := by
    refine Nat.exists_eq_add_of_le' ?_
    convert this
    simp
  have hBC₀ := hBC.1
  have hBC₂ := hBC.2
  let U := univ \ B ∪ A -- the key step
  have hU : #U ≤ n - 2 ∧ good ob U := by
    constructor
    · apply sdiff_two _ hBC₀
      omega
    · have h₁ : (univ \ B ∪ A) ∈ ob univ := @d5 B A univ hBC₀
            (ifsub_apply hBC₁ hBC₀) (by simp)
      intro X
      unfold ifsub
      simp
      intro hX
      exact e5 _ _ _ (subset_univ _) h₁ $
        (inter_eq_right.mpr hX).symm ▸ fun hc => a5 univ $ hc ▸ h₁
  specialize h U hU.2 univ (by simp)
  rw [@card_sdiff_of_subset (Fin n) U univ _ (by simp), card_fin] at h
  omega

theorem drop_at_most_one_of_no_good_small₂USINGBEAUTY {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob) {B C : Finset (Fin n)}
    (hBC₀:  Finset.card (C \ B) ≥ 2)
    (hBC₁ : B ⊆ C)
    (hBC₂ : B ∈ ob C) :
     ∃ A, #A ≤ n - 2 ∧ good ob A := by
  have := @global_to_local n ob a5 d5 e5
  have :
    ¬ (∀ {A B : Finset (Fin n)}, A ∈ ifsub ob B → ccss B A)
   → ¬ (∀ (A : Finset (Fin n)), (∀ (B : Finset (Fin n)), A ∈ ifsub ob B) → ∀ (B : Finset (Fin n)), ccss B A)
   := by tauto
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

  push_neg at hU
  constructor
  have : 2 ≤ #((univ : Finset (Fin (n)))) := by
    apply le_trans
    show 2 ≤ #(U \ A)
    omega
    apply card_le_card
    simp
  have : ∃ m, n = m + 2 := by
    refine Nat.exists_eq_add_of_le' ?_
    convert this
    simp
  have : #(U \ A) = #U - #A := by
    refine card_sdiff_of_subset hU.1
  rw [this] at hU
  have : #U ≤ #((univ : Finset (Fin (n)))) := by
    apply card_le_card
    simp
  have : #((univ : Finset (Fin (n)))) = n := by exact card_fin n
  omega
  intro B --hAB
  have := hA.1
  specialize this B
  unfold ifsub at this
  tauto



/--
Given that no small₂ set is good (which is not automatic here since
we don't assume B5 and C5),
an obligatory set cannot be more than 1 world away from its larger context.

(This cannot be formulated in terms of `Fin n`
but requires `Fin (n+1)`.) -/
theorem drop_at_most_one_of_no_small₂_good {n : ℕ}
    {ob : Finset (Fin (n+1)) → Finset (Finset (Fin (n+1)))}
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob)
    (large_of_ob: ∀ A, good ob A → cosubsingleton A) :
                   covering ob := by
  -- if every universally good set is cosubsingle
  -- then every somewhere good set is there-cosubsingle
  simp_rw [large_iff_cosubsingleton] at large_of_ob
  rw [← drop_at_most_one_eq_covering_of_ob]
  intro B C hBC ho
  unfold good at large_of_ob
  have hn (m : ℕ) (hm : n = m + 1) : ∀ A, #A ≤ m → ¬ good ob A := by
    intro A hA
    by_contra H
    unfold good at H
    specialize large_of_ob A H
    omega
  unfold good at hn
  have h_a (m : ℕ) : n = m + 1 → ¬ (∃ B C, #(C \ B) ≥ 2 ∧ B ⊆ C ∧ B ∈ ob C) := by
    intro hm hc
    obtain ⟨B,C,hBC⟩ := hc
    have := drop_at_most_one_of_no_good_small₂USINGBEAUTY a5 d5 e5 hBC.1 hBC.2.1 hBC.2.2
    revert this
    simp_rw [hm]
    simp
    apply hn
    exact hm
  push_neg at h_a
  by_cases H : ∃ m, n = m + 1
  · obtain ⟨m,hm⟩ := H
    specialize h_a m hm B C
    by_contra H
    simp at H
    exact h_a H hBC ho
  · have : n = 0 := by
        contrapose! H
        exact Nat.exists_eq_succ_of_ne_zero H
    subst this
    exact card_le_card $ subset_univ (C \ B)

/-- If `A` is small₂ then `A` is not good. -/
lemma not_good_of_small₂ {n : ℕ}
    {ob : Finset (Fin (n+2)) → Finset (Finset (Fin (n+2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    (A : Finset (Fin (n + 2))) (hs : small₂ A) :
    ¬ good ob A := by
  have hA : #A ≤ n := by
    unfold small₂ at hs
    have : #Aᶜ = #(univ \ A) := by congr
    rw [this] at hs
    have : #(univ \ A) = #((univ : Finset (Fin (n+2)))) - #A := by
        refine card_sdiff_of_subset ?_
        simp
    rw [this] at hs
    have : #((univ : Finset (Fin (n+2)))) = n+2 := card_fin (n + 2)
    rw [this] at hs
    omega
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
        tauto)
    simp at this
    omega
  exact not_good_of_small₂_specific a5 b5 c5 d5 e5 ha'



theorem drop_at_most_one_CJ97_FUTURE {n : ℕ}
    {ob : Finset (Fin (n+2)) → Finset (Finset (Fin (n+2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob) :
    drop_at_most_one ob := by
  unfold drop_at_most_one
  by_contra H
  push_neg at H
  obtain ⟨B,C,h₀,h₁,h₂⟩ := H

  have large_of_ob: ∀ A, good ob A → #A ≥ n+1 := by
    have hn := not_good_of_small₂ a5 b5 c5 d5 e5
    intro A hA
    contrapose! hA
    exact hn _ $ Nat.lt_add_one_iff.mp (by
            have : #Aᶜ = #(univ \ A) := by congr
            rw [this]
            have : #(univ \ A) = #((univ : Finset (Fin (n+2)))) - #A := by
                refine card_sdiff_of_subset ?_
                simp
            rw [this]
            have : #((univ : Finset (Fin (n+2)))) = n+2 := card_fin (n + 2)
            rw [this]
            omega
    )
  have := drop_at_most_one_of_no_small₂_good a5 d5 e5 (by
    have := large_of_ob
    simp_rw [← large_iff_cosubsingleton] at this
    exact this
  ) _ _ h₁ h₀
  omega

/-- Allow `B` and `C` to be implicit in `drop_at_most_one_CJ97`. -/
def drop_at_most_one_CJ97_apply {n : ℕ}
    {ob : Finset (Fin (n+2)) → Finset (Finset (Fin (n+2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    {B C : Finset (Fin (n+2))}
     :=
  drop_at_most_one_CJ97_FUTURE a5 b5 c5 d5 e5 B C



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
    convert drop_at_most_one_CJ97_apply a5 b5 c5 d5 e5 (by intro;simp;tauto) $ c5 _ _ _ h₁ h₃ using 2
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


lemma diff_diff {n : ℕ}
    {X Y : Finset (Fin (n + 2))} : X ∩ Y = Y \ (Y \ X) := by
  compare

lemma b5_transfer {n : ℕ} {ob : Finset (Fin (n + 2)) → Finset (Finset (Fin (n + 2)))}
  (b5 : B5 ob)
  (H₁ : ∀ (a : Fin (n + 2)) (X Y : Finset (Fin (n + 2))), a ∈ X ∩ Y → X \ {a} ∉ ob Y)
  {X Y : Finset (Fin (n + 2))} (hd : #(Y \ X) ≤ 1) -- actually =0, by H₁
  (h : X ∈ ob Y) : Y ∈ ob Y := by
    cases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with
    | inl h₀ =>
      have : X ∩ Y = Y :=
        inter_eq_right.mpr $ sdiff_eq_empty_iff_subset.mp $ card_eq_zero.mp h₀
      nth_rewrite 2 [← this]
      exact b5 Y X (X ∩ Y) (by simp) h
    | inr h₀ =>
      exfalso
      have ⟨a,ha⟩: ∃ a, Y \ X = {a} := card_eq_one.mp h₀
      specialize H₁ a Y Y (singleton_subset_iff.mp $ by
        rw [← ha]
        simp)
      apply H₁
      rw [← ha, ← diff_diff]
      exact b5 Y X (X ∩ Y) (by simp) h

lemma getAlive {n : ℕ} {ob : Finset (Fin (n + 2)) → Finset (Finset (Fin (n + 2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    (H₀ : ∃ Y X, X ∈ ob Y)
    (H₁ : ∀ (a : Fin (n + 2)) (X Y : Finset (Fin (n + 2))), a ∈ X ∩ Y → X \ {a} ∉ ob Y) :
    ob = alive (n + 2) := by
  ext X Y
  simp [alive]
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
        apply subset_antisymm
        · intro i hi
          simp at ha hi ⊢
          exact ⟨hi.1, fun hc => ha.2 $ hc ▸ hi.2⟩
        · intro i hi
          simp at hi ⊢
          constructor
          · exact hi.1
          · by_contra H₀
            exact two_in_sdiff _ _ _ _ ha hi.1 hi.2 H₀ $
                drop_at_most_one_CJ97_apply a5 b5 c5 d5 e5 inter_subset_left $
                    b5 X Y (X ∩ Y) (by compare) h
      have h₁ : X ∩ Y ∈ ob X := b5 X Y (X ∩ Y) (by compare) h
      specialize H₁ a X X
      rw [h₀] at h₁
      simp at ha H₁
      tauto
  intro h₂
  obtain ⟨Y',X',h'⟩ := H₀
  have h₀ : Y' ∈ ob Y' := by
    have := drop_at_most_one_CJ97_apply a5 b5 c5 d5 e5 (by simp)
      (b5 Y' X' (X' ∩ Y') (by simp) h')
    apply b5_transfer b5 H₁ (by convert this using 1;apply congrArg;simp) h'
  have h₁ : X ∈ ob X := obSelf_transfer b5 d5 e5 h₀ h₂.1
  nth_rewrite 2 [← inter_eq_left.mpr h₂.2] at h₁
  exact b5 X (X ∩ Y) Y (by simp) h₁



theorem unique_bad_world' {n : ℕ} {ob : Finset (Fin (n + 2)) → Finset (Finset (Fin (n + 2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    {a b : Fin (n + 2)} {X Y Z : Finset (Fin (n + 2))}
    (haZ : a ∈ Z) (imp : Z \ {a} ∈ ob Z)
    (hb : X \ Y = {b}) (h' : X ∩ Y ∈ ob X) :
    a = b := by
  have h₀ : X ∩ Y = X \ {b} := by
    rw [← hb]
    compare
  have h₄ : b ∈ X := by
    apply singleton_subset_iff.mp
    rw [← hb]
    simp
  exact unique_bad_world a5 b5 c5 d5 e5 haZ h₄ imp <| h₀ ▸ h'

theorem all_or_almost' {n : ℕ} {ob : Finset (Fin (n + 2)) → Finset (Finset (Fin (n + 2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    {a : Fin (n + 2)} {X' X Y : Finset (Fin (n + 2))}
    (haX' : a ∈ X')
    (imp : X' \ {a} ∈ ob X') (h' : X ∩ Y ∈ ob X) :
    X ∩ Y = X ∨ X ∩ Y = X \ {a} := by
  cases Nat.eq_or_lt_of_le (drop_at_most_one_CJ97_apply a5 b5 c5 d5 e5 (by simp) h') with
  | inl h =>
    have ⟨b,hb⟩ : ∃ b, X \ (X ∩ Y) = {b} := card_eq_one.mp h
    rw [unique_bad_world' a5 b5 c5 d5 e5 haX' imp (by show _ = {b};rw [← hb];compare) h', ← hb]
    compare
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
    (H₁ : a ∈ X' ∩ Y' ∧ (X' ∩ Y') \ {a} ∈ ob Y') : ob = stayAlive a := by
  have adHoc₂ : ∀ X, ∀ a ∈ X, X \ {a} ∈ ob X →
      ob {a} = {Y | a ∈ Y}.toFinset := ob_forbidden a5 b5 c5 $ ob_forbidden_self b5 d5 e5 adHoc
  have imp : (X' ∩ Y') \ {a} ∈ ob (X' ∩ Y') := e5 Y' (X' ∩ Y') ((X' ∩ Y') \ {a}) (by simp) H₁.2
      (by
      intro hc
      have : (X' ∩ Y') \ {a} = ∅ := by
        convert hc using 1
        compare
      rw [this] at H₁
      exact a5 _ H₁.2)
  rw [funext_iff]
  intro X
  have hag := @obSelf_sdiff (n+2) ob b5 d5 e5
    (X' ∩ Y') X a H₁.1 (e5 Y' (X' ∩ Y') ( (X' ∩ Y') \ {a})
      (by simp) H₁.2 (by
        intro hc
        have : (X' ∩ Y') \ {a} = ∅ := by
          convert hc using 1
          compare
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
      have h' : X ∩ Y ∈ ob X := b5 X Y (X ∩ Y) (by compare) h
      constructor
      · exact fun hc => a5 _ <| hc ▸ h'
      · by_cases H₂ : X \ {a} = ∅
        · rw [H₂]
          simp
        · have h₀ : X \ {a} ∈ ob (X \ {a}) := e5 (X) (X \ {a}) (X \ {a}) (by simp)
            (obSelf_sdiff b5 d5 e5 H₁.1 imp H₂) (by simp_all)
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
      apply b5 X (X ∩ Y) Y (by simp)
      have hX : X ≠ ∅ := fun hc => by simp [hc] at h
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
          · exact obSelf a5 b5 d5 e5 X ({a} ∪ Xᶜ) a (by
              rw [union_sdiff_left]


              contrapose! H₁
              simp at H₁ ⊢
              cases H₁ with
              | inl h => exact h
              | inr h =>
                  ext y
                  simp
                  by_cases H : y = a
                  · subst H
                    tauto
                  · rw [eq_compl_comm.mp h.symm]
                    simp
                    exact H)
              (by
                rw [inter_union_distrib_left]
                simp
                exact H₀) h₀
        · exact ht H₀
      | inr h' =>
        rw [h']
        by_cases H₀ : a ∈ X
        · exact obSelf_sdiff b5 d5 e5 H₁.1 imp (h' ▸ h.1)
        · have : X = X \ {a} := sdiff_singleton_eq_erase a X ▸ (Finset.erase_eq_of_notMem H₀).symm
          rw [← this]
          exact ht H₀


def noObligations (n : ℕ) : Finset (Fin n) → Finset (Finset (Fin n)) :=
  fun _ => ∅

/--
June 11, 2025
Only three models of CJ 1997 for a given `n ≥ 2`.
-/
theorem models_ofCJ_1997 {n : ℕ}
    (ob : Finset (Fin (n+2)) → Finset (Finset (Fin (n+2))))
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob):
  (∃ a, ob = stayAlive a) ∨ ob = alive (n+2) ∨ ob = noObligations (n+2) := by
  by_cases H₀ : ∃ Y X, X ∈ ob Y
  · by_cases H₁ : ∃ a Y X, a ∈ X ∩ Y ∧ (X ∩ Y) \ {a} ∈ ob Y
    · obtain ⟨a,Y,X,H₁⟩ := H₁
      left
      use a
      exact getStayAlive a5 b5 c5 d5 e5 (univ_ob_univ a5 d5 e5) H₀ H₁
    · push_neg at H₁
      exact .inr <| .inl <| getAlive a5 b5 c5 d5 e5 H₀ (by
        intro a X Y h hc
        have : (X ∩ Y) \ {a} ∈ ob Y := b5 Y (X \ {a}) ( (X ∩ Y) \ {a})
            (by compare) hc
        by_cases H₂ : a ∈ Y
        · specialize H₁ a Y X (by compare)
          tauto
        · simp at h
          tauto)
  · push_neg at H₀
    right
    right
    unfold noObligations
    compare



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


/-- first two alternatives are actually the same -/
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


theorem models_ofCJ_1997_full {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob):
  (∃ a, ob = stayAlive a) ∨ ob = alive n ∨ ob = noObligations n := by
  cases n with
  | zero =>
    exact .inr <| .inr <| (models_ofCJ_1997₀ ob a5).2
  | succ n =>
    cases n with
    | zero   => exact models_ofCJ_1997₁ ob a5 b5
    | succ n => exact models_ofCJ_1997  ob a5 b5 c5 d5 e5

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

theorem models_ofCJ_1997_equiv {n : ℕ}
    (ob : Finset (Fin n) → Finset (Finset (Fin n))) :
    (A5 ob ∧ B5 ob ∧ C5Strong ob ∧ D5 ob ∧ E5 ob) ↔
    ((∃ a, ob = stayAlive a) ∨ ob = alive n ∨ ob = noObligations n) := by
  constructor
  · intro h
    apply models_ofCJ_1997_full <;> tauto
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
