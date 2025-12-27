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

`lemma9_1996` [d5]
--> `semiglobal_holds` [acde5]
--> [`global_holds_specific`] --> [`global_holds`]
                                        |
                                        v
            [`unique_bad`] <- [`local_holds`]
                    |
                    v
            [`all_or_almost'`]      [abde5] <--- `obSelfSdiff_of_bad`     `local_of_global'`
                             \       |             /         |[bde5]                    |[ade]
                              \/     v            /          |                          v
`selfOb_of_bad` -->[`stayAlive_of_semibad`]<- /           |                  `local_of_global''`
      [bde]                  /\       |                      |                          |[ade]
                            /         v                      v                          v
              `univ_ob_univ`       [`models_ofCJ_1997`]  <- [`getAlive`] <--- [`local_holds`]
                  [ade5]

                                      - `ob_singleton_alive_of_selfOb`
                                      - `obSelf_singleton`
                                      - `univ_ob_univ`         --- `obSelfSdiff_of_bad`
                                      - `obSelf_of_semibad`    --- `obSelf`
                                      - `bad_cosubsingleton_of_ob`
                     [`stayAlive_of_semibad`] - `selfOb_of_bad`
                    /
[`models_ofCJ_1997`]
                    \
                     [`getAlive`] - `obSelf_of_obSelf`
                                  - `b5_transfer`
                                  - `local_holds_apply`

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

/-- `ob` has the `drop_at_most_one` property
if whenever a subset is obligatory, it is a relative cosubsingleton
  -/
def covering {n : ℕ}
    (ob : Finset (Fin n) → Finset (Finset (Fin n))) :=
    ∀ B C, B ∈ ob C → ccss C B


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
lemma lemma9_1996
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
theorem semiglobal_holds {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (a5 : A5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    {A : Finset (Fin n)}
    {a₁ a₂ : Fin n} (ha₂ : a₁ ≠ a₂)
    (ha₀ : a₁ ∉ A) (ha₁ : a₂ ∉ A)
    (hcorr : {a₁, a₂} ∈ ob {a₁, a₂})
    :
    ¬ good ob A := by
  intro h
  let Z₁ := A ∪ {a₁}
  let Z₂ := A ∪ {a₂}
  have h₁ : Z₁ ∈ ob {a₁, a₂} := e5 (A ∪ {a₁, a₂}) {a₁, a₂} Z₁ (by simp)
    (pair_comm a₁ a₂ ▸ lemma9_1996 d5 ha₂.symm h) $ ne_empty_of_mem <| by
    show a₁ ∈ _; simp [Z₁]
  have h₂ : Z₂ ∈ ob {a₁, a₂} := e5 (A ∪ {a₁, a₂}) {a₁, a₂} Z₂ (by simp)
    (lemma9_1996 d5 ha₂ h) $ ne_empty_of_mem <| by
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
lemma global_holds_specific
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
  exact semiglobal_holds a5 c5 d5 e5 ha'.2.2 ha'.1 ha'.2.1 this h

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

/-- Not only is `a` "bad" but there is an obligation that singles it out. -/
def bad {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) (a : Fin n) :=
    ∃ X, a ∈ X ∧ X \ {a} ∈ ob X


def semibad {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) (a : Fin n) :=
    ∃ X Y : Finset (Fin n), a ∈ X ∩ Y ∧ (X ∩ Y) \ {a} ∈ ob X

/-- The model according to which there are no obligations at all. -/
def noObligations (n : ℕ) : Finset (Fin n) → Finset (Finset (Fin n)) :=
  fun _ => ∅




/-- A context `Y` is obligatory given itself, provided
that `∃ a ∉ Y, ∃ X, a ∈ X ∧ X \ {a} ∈ ob X`.
-/
theorem selfOb_of_bad {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob) {Y : Finset (Fin n)}
    {a : Fin n}
    (hbad : bad ob a)
    (haY : a ∉ Y)
    (hY : Y ≠ ∅) : Y ∈ ob Y := by
  obtain ⟨X,ha,hX⟩ := hbad

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

theorem obSelfSdiff_of_bad {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
    {a : Fin n} (hbad : bad ob a)
    {Y : Finset (Fin n)} (haY : Y \ {a} ≠ ∅) :
    Y \ {a} ∈ ob Y := by
  have ⟨X,ha,h⟩ := hbad
  have : (X ∪ Y) \ {a} ∈ ob (X ∪ Y) := by
    convert d5 _ _ (X ∪ Y) (by simp) h (by simp) using 1
    exact union_sdiff_singleton ha haY
  have : (X ∪ Y) \ {a} ∈ ob Y := e5 (X ∪ Y) Y ((X ∪ Y) \ {a}) (by simp) this (by
      contrapose! haY
      rw [← haY]
      compare)
  exact b5 _ _ _ (by compare) this


theorem obSelf_of_obSelf {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob) {X Y : Finset (Fin n)}
    (hX : X ∈ ob X) (hY : Y ≠ ∅) : Y ∈ ob Y := by
  have : X ∪ Y ∈ ob (X ∪ Y) := by
    convert d5 (Z := X ∪ Y) X X (by simp) hX (by simp) using 1
    compare
  exact b5 _ _ _ (by simp) $ e5 _ Y _ subset_union_right this (by compare)


theorem obSelf_of_obSelfSdiff {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
    {X : Finset (Fin n)} {a : Fin n}
    (haX : a ∈ X) (hX : X ≠ univ)
    (h : X \ {a} ∈ ob X) : X ∈ ob X := by
  let Y := {a} ∪ Xᶜ
  have hY : Y \ {a} ≠ ∅ := by
    unfold Y
    contrapose! hX
    have : ({a} ∪ Xᶜ) \ {a} = Xᶜ \ {a} := by compare
    rw [this] at hX
    ext i
    simp
    by_cases H : i = a
    subst H
    tauto
    contrapose! hX
    refine nonempty_def.mpr ?_
    use i
    simp
    tauto
  have h₀ := @obSelfSdiff_of_bad n ob b5 d5 e5 a ⟨X,haX, h⟩ Y hY
  have : Y \ {a} ∈ ob (Y \ {a}) := e5 _ _ _ sdiff_subset h₀
      ((inter_self (Y \ {a})).symm ▸ fun hc => a5 Y $ hc ▸ h₀)
  exact @obSelf_of_obSelf n ob b5 d5 e5 (Y \ {a}) X
    this (ne_empty_of_mem haX)



lemma ob_singleton_alive_of_selfOb {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) {a : Fin n}
    (ha : {a} ∈ ob {a}) : ob {a} = {Y | a ∈ Y}.toFinset := by
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

lemma obSelfSingleton_of_bad {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
    (adHoc : ∀ a : Fin n, univ \ {a} ∈ ob univ → univ ∈ ob univ)
    -- `adHoc` follows from a5 but is maybe weaker?
    (a : Fin n)
    (hbad : bad ob a) :
    {a} ∈ ob {a} := by
  obtain ⟨X,ha,ha'⟩ := hbad
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
theorem local_of_global {n : ℕ}
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

/-- A trivial consequence of `local_of_global`.  -/
theorem local_of_global' {n : ℕ}
    {ob : Finset (Fin n) → Finset (Finset (Fin n))}
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob) {B C : Finset (Fin n)}
    (hBC₀:  Finset.card (C \ B) ≥ 2)
    (hBC₁ : B ⊆ C)
    (hBC₂ : B ∈ ob C) :
     ∃ A, #A ≤ n - 2 ∧ good ob A := by
  have := fun a ↦ Not.imp a $ @local_of_global n ob a5 d5 e5
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
  refine ⟨?_, hA.1⟩
  have : 2 ≤ #((univ : Finset (Fin (n)))) := by
    apply le_trans
    show 2 ≤ #(U \ A)
    omega
    apply card_le_card
    simp
  have : #(U \ A) = #U - #A := by
    refine card_sdiff_of_subset hU.1
  rw [this] at hU
  have : #U ≤ #((univ : Finset (Fin (n)))) := by
    apply card_le_card
    simp
  have : #((univ : Finset (Fin (n)))) = n := card_fin n
  omega



/--
Given that no small₂ set is good (which is not automatic here since
we don't assume B5 and C5),
an obligatory set cannot be more than 1 world away from its larger context.

(This cannot be formulated in terms of `Fin n`
but requires `Fin (n+1)`.) -/
theorem local_of_global'' {n : ℕ}
    {ob : Finset (Fin (n+1)) → Finset (Finset (Fin (n+1)))}
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob)
    (large_of_ob: ∀ A, good ob A → cosubsingleton A) :
                   covering ob := by
  -- if every universally good set is cosubsingle
  -- then every somewhere good set is there-cosubsingle
  simp_rw [large_iff_cosubsingleton] at large_of_ob
  intro B C ho hBC
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
    have := local_of_global' a5 d5 e5 hBC.1 hBC.2.1 hBC.2.2
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

lemma card_compl_aux {n : ℕ} {A : Finset (Fin (n + 2))}
      (hA : #A < n + 1) : 2 < #Aᶜ + 1 := by
    have : #Aᶜ = #(univ \ A) := by congr
    rw [this]
    have : #(univ \ A) = #((univ : Finset (Fin (n+2)))) - #A := by
        refine card_sdiff_of_subset ?_
        simp
    rw [this]
    have : #((univ : Finset (Fin (n+2)))) = n+2 := card_fin (n + 2)
    rw [this]
    omega

lemma card_compl_aux' {n : ℕ} {A : Finset (Fin (n + 2))} (hs : 2 ≤ #Aᶜ) :
  #A ≤ n := by
    have : #Aᶜ = #(univ \ A) := by congr
    rw [this] at hs
    have : #(univ \ A) = #((univ : Finset (Fin (n+2)))) - #A := by
        refine card_sdiff_of_subset ?_
        simp
    rw [this] at hs
    have : #((univ : Finset (Fin (n+2)))) = n+2 := card_fin (n + 2)
    rw [this] at hs
    omega


/-- If `A` is small₂ then `A` is not good.
This is just some set-wrangling on top of `global_holds_specific`.
-/
lemma global_holds {n : ℕ}
    {ob : Finset (Fin (n+2)) → Finset (Finset (Fin (n+2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    (A : Finset (Fin (n + 2))) (hs : small₂ A) :
    ¬ good ob A := by
  have hA : #A ≤ n := card_compl_aux' hs
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
  exact global_holds_specific a5 b5 c5 d5 e5 ha'

/-- A direct consequence of `global_holds` and `local_of_global`. -/
theorem local_holds {n : ℕ}
    {ob : Finset (Fin (n+2)) → Finset (Finset (Fin (n+2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob) :
    covering ob := by
  unfold covering ccss
  by_contra H
  push_neg at H
  obtain ⟨B,C,h₀,h₁,h₂⟩ := H

  have global_holds': ∀ A, good ob A → #A ≥ n+1 := by
    have hn := global_holds a5 b5 c5 d5 e5
    intro A hA
    contrapose! hA
    exact hn _ $ Nat.lt_add_one_iff.mp $ card_compl_aux hA
  have := local_of_global'' a5 d5 e5 (by
    have := global_holds'
    simp_rw [← large_iff_cosubsingleton] at this
    exact this
  ) _ _ h₀ h₁
  omega

/-- Allow `B` and `C` to be implicit in `local_holds`. -/
def local_holds_apply {n : ℕ}
    {ob : Finset (Fin (n+2)) → Finset (Finset (Fin (n+2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    {B C : Finset (Fin (n+2))} :=
  local_holds a5 b5 c5 d5 e5 B C

lemma diff_diff {n : ℕ}
    {X Y : Finset (Fin (n + 2))} : X ∩ Y = Y \ (Y \ X) := by
  compare

/-- An obvious consequence of `B5`. -/
lemma obSelf_of_ob_of_subset {n : ℕ} {ob : Finset (Fin (n + 2)) → Finset (Finset (Fin (n + 2)))}
    (b5 : B5 ob)
    {X Y : Finset (Fin (n + 2))} (hd : Y ⊆ X)
    (h : X ∈ ob Y) : Y ∈ ob Y := by
  nth_rewrite 2 [← inter_eq_right.mpr hd]
  exact b5 Y X (X ∩ Y) (by simp) h

theorem not_ob_of_almost {n : ℕ} {ob : Finset (Fin (n + 2)) → Finset (Finset (Fin (n + 2)))}
    (b5 : B5 ob)
    (H₁ : ∀ (a : Fin (n + 2)) (X Y : Finset (Fin (n + 2))), a ∈ X ∩ Y → X \ {a} ∉ ob Y) {X Y : Finset (Fin (n + 2))}
    (h₀ : #(Y \ X) = 1) : X ∉ ob Y := by
  have ⟨a,ha⟩: ∃ a, Y \ X = {a} := card_eq_one.mp h₀
  specialize H₁ a Y Y (singleton_subset_iff.mp $ by
    rw [← ha]
    simp)
  rw [← ha, ← diff_diff] at H₁
  have := b5 Y X (X ∩ Y) (by simp)
  tauto

/-- A glue lemma for `obSelf_of_ob_of_subset`. -/
lemma obSelf_of_ob_of_subset.glue {n : ℕ} {ob : Finset (Fin (n + 2)) → Finset (Finset (Fin (n + 2)))}
  (b5 : B5 ob)
  (H₁ : ∀ (a : Fin (n + 2)) (X Y : Finset (Fin (n + 2))), a ∈ X ∩ Y → X \ {a} ∉ ob Y)
  {X Y : Finset (Fin (n + 2))} (hd : #(Y \ X) ≤ 1)
  (h : X ∈ ob Y) : Y ∈ ob Y := by
    cases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with
    | inl h₀ =>
      exact obSelf_of_ob_of_subset b5
        (sdiff_eq_empty_iff_subset.mp $ card_eq_zero.mp h₀) h
    | inr h₀ =>
      exfalso
      apply not_ob_of_almost b5 H₁ h₀ h


lemma getAlive {n : ℕ} {ob : Finset (Fin (n + 2)) → Finset (Finset (Fin (n + 2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    (H₀ : ob ≠ noObligations (n+2))
    (H₁ : ∀ a, ¬ semibad ob a) :
    ob = alive (n + 2) := by
  have H₀ : ∃ Y X, X ∈ ob Y := by
    contrapose! H₀
    ext Y X
    unfold noObligations
    simp
    apply H₀
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
                local_holds_apply a5 b5 c5 d5 e5
                    (b5 X Y (X ∩ Y) (by compare) h) inter_subset_left
      have h₁ : X ∩ Y ∈ ob X := b5 X Y (X ∩ Y) (by compare) h
      unfold semibad at H₁
      push_neg at H₁
      specialize H₁ a X X
      rw [h₀] at h₁
      simp at ha H₁
      tauto
  intro h₂
  obtain ⟨Y',X',h'⟩ := H₀
  have h₀ : Y' ∈ ob Y' := by
    have := local_holds_apply a5 b5 c5 d5 e5
        (b5 Y' X' (X' ∩ Y') (by simp) h')
        (by simp)
    apply obSelf_of_ob_of_subset.glue b5 (by
        unfold semibad at H₁
        push_neg at H₁
        intro a X Y haXY
        specialize H₁ a Y X (by rw [inter_comm];tauto)
        contrapose! H₁
        apply b5
        show X \ {a} ∩ Y = _
        compare
        exact H₁) (by convert this using 1;apply congrArg;simp) h'
  have h₁ : X ∈ ob X := obSelf_of_obSelf b5 d5 e5 h₀ h₂.1
  nth_rewrite 2 [← inter_eq_left.mpr h₂.2] at h₁
  exact b5 X (X ∩ Y) Y (by simp) h₁



theorem unique_bad {n : ℕ}
    {ob : Finset (Fin (n+2)) → Finset (Finset (Fin (n+2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    {a b : Fin (n+2)} (ha : bad ob a) (hb : bad ob b) : a = b := by
  obtain ⟨X,ha, hoa⟩ := ha
  obtain ⟨Y,hb, hob⟩ := hb
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
    convert local_holds_apply a5 b5 c5 d5 e5
        (c5 _ _ _ h₁ h₃)
        (by intro;simp;tauto)
        using 2
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


theorem bad_cosubsingleton_of_ob {n : ℕ} {ob : Finset (Fin (n + 2)) → Finset (Finset (Fin (n + 2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    {a : Fin (n + 2)}
    (hbad : bad ob a)
    {X Y : Finset (Fin (n + 2))}
    (h' : X ∩ Y ∈ ob X) :
    X ∩ Y = X ∨ X ∩ Y = X \ {a} := by
  obtain ⟨X',haX',imp⟩ := hbad
  cases Nat.eq_or_lt_of_le (local_holds_apply a5 b5 c5 d5 e5
    h' inter_subset_left) with
  | inl h =>
    right
    have ⟨b,hb⟩ : ∃ b, X \ (X ∩ Y) = {b} := card_eq_one.mp h
    have hbX : X ∩ Y = X \ {b} := by
      rw [← hb]
      rw [diff_diff]
      compare
    have : b ∈ X := by
      apply singleton_subset_iff.mp
      rw [← hb]
      simp
    have hbad' := @unique_bad n ob a5 b5 c5 d5 e5 a b (by use X') (by
        use X;constructor;exact this;exact hbX ▸ h')
    rw [hbad']
    exact hbX
  | inr h =>
    left
    apply subset_antisymm
    · exact inter_subset_left
    · simp at h
      apply subset_inter _ h
      exact subset_refl _

/-- If `X` contains a semibad world `b` and
at least one other world `a` then `X` is self-obligatory.
 -/
lemma obSelf_of_semibad {n : ℕ} {ob : Finset (Fin (n + 2)) → Finset (Finset (Fin (n + 2)))}
    (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
    {b : Fin (n + 2)} (H₁ : semibad ob b)

    {X : Finset (Fin (n + 2))} (G : ¬X = {b}) (H₀ : b ∈ X) :
    X ∈ ob X := by
  obtain ⟨X',Y',H₁⟩ := H₁
  have h₁ : (X' ∩ Y') \ {b} ≠ ∅ := by
    have := H₁.2
    contrapose! this
    rw [this]
    apply a5
  have h₀ : X \ {b} ∈ ob X := by
    have g₁ := e5 _ _ _ (by show X' ∩ Y' ⊆ X';simp) H₁.2 (by
        have := h₁
        contrapose! this;rw [← this];compare)
    exact @obSelfSdiff_of_bad (n+2) ob b5 d5 e5 b (by
        use X' ∩ Y'
        constructor
        exact H₁.1
        exact g₁) X (by
            contrapose! G
            exact subset_antisymm (sdiff_eq_empty_iff_subset.mp G) $
                singleton_subset_iff.mpr H₀)
  by_cases H₁ : X = univ
  · subst H₁
    apply univ_ob_univ a5 d5 e5 b
    exact h₀
  · have h₂ : ({b} ∪ Xᶜ) \ {b} ≠ ∅ := by
      rw [union_sdiff_left]
      contrapose! H₁
      simp at H₁ ⊢
      cases H₁ with
      | inl h => exact h
      | inr h =>
        exfalso
        have : {b} ⊆ Xᶜ := subset_of_eq h.symm
        rw [singleton_subset_iff, mem_compl] at this
        exact this H₀
    exact @obSelf_of_obSelfSdiff (n+2) ob a5 b5 d5 e5 X b H₀ H₁ h₀

theorem stayAlive_of_semibad {n : ℕ} {ob : Finset (Fin (n + 2)) → Finset (Finset (Fin (n + 2)))}
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)
    {a : Fin (n+2)} (H₁ : semibad ob a) : ob = stayAlive a := by
  obtain ⟨Y',X',⟨H₁₀,H₁₁⟩⟩ := H₁
  ext X Y
  rw [inter_comm] at H₁₁ H₁₀
  have h₁ :  X' ∩ Y' ∩ ((X' ∩ Y') \ {a}) ≠ ∅ := by
      rw [inter_eq_right.mpr sdiff_subset]
      exact fun hc => a5 _ $ hc ▸ H₁₁
  have imp : (X' ∩ Y') \ {a} ∈ ob (X' ∩ Y') :=
    e5 _ _ _ inter_subset_right H₁₁ h₁
  by_cases G : X = {a}
  · subst G
    simp [stayAlive]
    have h₂ : ∀ X, ∀ a ∈ X, X \ {a} ∈ ob X → ob {a} = {Y | a ∈ Y}.toFinset := by
      intro X b hbX hbX'
      apply @ob_singleton_alive_of_selfOb (n+2) ob a5 b5 c5 b
        $ (obSelfSingleton_of_bad b5 d5 e5 $
            univ_ob_univ a5 d5 e5) b ⟨X, hbX, hbX'⟩
    rw [h₂ (X' ∩ Y') a H₁₀ imp]
    simp
    apply venn_singleton
  · simp [stayAlive]
    constructor
    · intro h
      have h' : X ∩ Y ∈ ob X := b5 X Y (X ∩ Y) (by compare) h
      constructor
      · exact fun hc => a5 _ <| hc ▸ h'
      · cases bad_cosubsingleton_of_ob a5 b5 c5 d5 e5 (by use X' ∩ Y') h' with
          | inl h =>
            rw [h]
            simp
          | inr h =>
            rw [h]
    · intro h
      apply b5 X (X ∩ Y) Y (by simp)
      have hX : X ≠ ∅ := fun hc => by simp [hc] at h
      have ht (H₀) := selfOb_of_bad b5 d5 e5 (by use X' ∩ Y') H₀ hX
      cases all_or_almost h.2 with
      | inl h₀ =>
        rw [h₀]
        by_cases H₀ : a ∈ X
        · exact obSelf_of_semibad a5 b5 d5 e5 (by
            have := H₁₀
            have := H₁₁
            use Y', X'
            rw [inter_comm]
            tauto) (by
            have := h₁
            contrapose! this;rw [← this];compare) H₀
        · exact ht H₀
      | inr h' =>
        rw [h']
        by_cases H₀ : a ∈ X
        · exact @obSelfSdiff_of_bad (n+2) ob b5 d5 e5 a (by
                use X' ∩ Y') X (by
                contrapose! G
                exact subset_antisymm (sdiff_eq_empty_iff_subset.mp G) $
                    singleton_subset_iff.mpr H₀)
        · have : X = X \ {a} := sdiff_singleton_eq_erase a X ▸ (Finset.erase_eq_of_notMem H₀).symm
          rw [← this]
          exact ht H₀


/--
There are only three models of CJ 1997 for a given `n ≥ 2`:
`stayAlive`, `alive`, `noObligations`.
-/
theorem models_ofCJ_1997 {n : ℕ} --June 11, 2025
    (ob : Finset (Fin (n+2)) → Finset (Finset (Fin (n+2))))
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob):
  (∃ a, ob = stayAlive a) ∨ ob = alive (n+2) ∨ ob = noObligations (n+2) := by
  by_cases H₀ : ob = noObligations (n+2)
  · exact .inr $ .inr H₀
  · by_cases H₁ : ∃ a, semibad ob a
    · left
      obtain ⟨a,H₁⟩ := H₁
      use a
      exact stayAlive_of_semibad a5 b5 c5 d5 e5 H₁
    · push_neg at H₁
      exact .inr $ .inl $ getAlive a5 b5 c5 d5 e5 H₀ H₁



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
