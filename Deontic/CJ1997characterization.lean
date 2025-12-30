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

`insert_single_ob_pair` [d5]
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
`obSelf_of_bad_not_mem` -->[`stayAlive_of_bad`]<- /           |                  `local_of_global''`
      [bde]                  /\       |                      |                          |[ade]
                            /         v                      v                          v
              `obSelf_univ`       [`models_ofCJ_1997`]  <- [`getAlive`] <--- [`local_holds`]
                  [ade5]

                                      - `ob_singleton_alive_of_selfOb`
                                      - `obSelf_singleton`
                                      - `obSelf_univ`         --- `obSelfSdiff_of_bad`
                                      - `obSelf_of_bad_mem`    --- `obSelf`
                                      - `bad_cosubsingleton_of_ob`
                     [`stayAlive_of_bad`] - `obSelf_of_bad_not_mem`
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


def small₂ {n : ℕ} (A : Finset (Fin n)) :=
    2 ≤ #Aᶜ

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

def quasibad {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) (a : Fin n) := ∃ X Y, a ∈ X \ Y ∧ Y ∈ ob X

lemma semibad_of_bad {n : ℕ} {ob : Finset (Fin n) → Finset (Finset (Fin n))} {a : Fin n}
    (hbad : bad ob a) : semibad ob a := by
    obtain ⟨X,h₀⟩ := hbad
    use X, X
    simp
    exact h₀

/-- The model according to which there are no obligations at all. -/
def noObligations (n : ℕ) : Finset (Fin n) → Finset (Finset (Fin n)) :=
  fun _ => ∅

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

lemma card_compl_aux {n : ℕ} {A : Finset (Fin (n + 2))}
      (hA : #A < n + 1) : 2 < #Aᶜ + 1 := by
    have : #Aᶜ = #(univ \ A) := by congr
    rw [this]
    have : #(univ \ A) = #((univ : Finset (Fin (n + 2)))) - #A := by
        refine card_sdiff_of_subset ?_
        simp
    rw [this]
    have : #((univ : Finset (Fin (n + 2)))) = n + 2 := card_fin (n + 2)
    rw [this]
    omega

lemma card_compl_aux' {n : ℕ} {A : Finset (Fin (n + 2))} (hs : 2 ≤ #Aᶜ) :
  #A ≤ n := by
    have : #Aᶜ = #(univ \ A) := by congr
    rw [this] at hs
    have : #(univ \ A) = #((univ : Finset (Fin (n + 2)))) - #A := by
        refine card_sdiff_of_subset ?_
        simp
    rw [this] at hs
    have : #((univ : Finset (Fin (n + 2)))) = n + 2 := card_fin (n + 2)
    rw [this] at hs
    omega

lemma diff_diff {n : ℕ}
    {X Y : Finset (Fin n)} : X ∩ Y = Y \ (Y \ X) := by
  compare

lemma sdiff_ne_empty_of_ne_empty_of_mem {n : ℕ} {b : Fin n}
    {X : Finset (Fin n)} (G : ¬X = {b}) (H₀ : b ∈ X) : X \ {b} ≠ ∅ := by
  contrapose! G
  exact subset_antisymm (sdiff_eq_empty_iff_subset.mp G) $
    singleton_subset_iff.mpr H₀

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

/-- A weaker version using the weaker C5 axiom.-/
theorem single_ob_pair
    (c5 : C5 ob) (d5 : D5 ob) (e5 : E5 ob)
    {A : Finset (Fin k)} {a₁ a₂ : Fin k} (ha₂ : a₁ ≠ a₂) (ha₀ : a₁ ∉ A)
    (ha₁ : a₂ ∉ A) (hcorr : {a₁, a₂} ∈ ob {a₁, a₂}) (h : inter_ifsub ob A) :
    ({a₁} ∈ ob {a₁, a₂} ∧ {a₂} ∈ ob {a₁, a₂}) := by
  let Z₁ := A ∪ {a₁}
  let Z₂ := A ∪ {a₂}
  have h₁ : Z₁ ∈ ob {a₁, a₂} := e5 (A ∪ {a₁, a₂}) {a₁, a₂} Z₁ (by simp)
    (pair_comm a₁ a₂ ▸ insert_single_ob_pair d5 ha₂.symm h) $ ne_empty_of_mem <| by
    show a₁ ∈ _; simp [Z₁]
  have h₂ : Z₂ ∈ ob {a₁, a₂} := e5 (A ∪ {a₁, a₂}) {a₁, a₂} Z₂ (by simp)
    (insert_single_ob_pair d5 ha₂ h) $ ne_empty_of_mem <| by
    show a₂ ∈ _; simp [Z₂]
  have : {a₁} = Z₁ ∩ {a₁, a₂} := by
    ext b
    simp [Z₁]
    intro h₀ h₁
    rw [h₁] at h₀
    tauto
  have this₂ : {a₂} = Z₂ ∩ {a₁, a₂} := by
    ext b
    simp [Z₂]
    intro h₀ h₁
    cases h₁ with
    | inl h => subst h;tauto
    | inr h => tauto
  have help₁ :  {a₁, a₂} ∩ Z₁ ∩ {a₁, a₂} ≠ ∅ := by
    rw [inter_comm]
    simp
    rw [inter_comm]
    rw [← this]
    simp
  have help₂ :  {a₁, a₂} ∩ Z₂ ∩ {a₁, a₂} ≠ ∅ := by
    rw [inter_comm]
    simp
    rw [inter_comm]
    rw [← this₂]
    simp
  have h₃ : {a₁} ∈ ob {a₁, a₂} := this ▸ (c5 {a₁, a₂} Z₁ {a₁, a₂} h₁ hcorr help₁)
  have : {a₂} = Z₂ ∩ {a₁, a₂} := by
    ext b;simp [Z₂]
    intro h₁ h₀
    cases h₀ with
    | inl h => subst h;tauto
    | inr h => subst h;tauto
  have h₄ : {a₂} ∈ ob {a₁, a₂} := by
    have hh := c5 {a₁, a₂} Z₂ {a₁, a₂} h₂ hcorr help₂
    rw [← this] at hh
    exact hh
  tauto

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
    (h : inter_ifsub ob A)
    :
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

structure ABCDE where
    (a5 : A5 ob) (b5 : B5 ob) (c5 : C5Strong ob) (d5 : D5 ob) (e5 : E5 ob)


/-- If `A` is small₂ (missing a pair of worlds)
then `A` is not inter_ifsub. -/
lemma global_holds_specific (t : @ABCDE k ob)
    {A : Finset <| Fin k} {a₁ a₂ : Fin k} (h₁ : a₁ ∉ A) (h₂ : a₂ ∉ A)
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
  simp
  ext b;simp
  constructor
  intro h
  cases h with
    | inl h => subst h;tauto
    | inr h => rw [h];tauto
  tauto

/- A context `Y` is obligatory given itself, provided
that `∃ a ∉ Y, ∃ X, a ∈ X ∧ X \ {a} ∈ ob X`.
-/
-- theorem obSelf_of_bad_not_mem
--     (t : @BDE k ob)
--     {Y : Finset (Fin k)}
--     {a : Fin k}
--     (hbad : bad ob a)
--     (hY : Y ≠ ∅)
--     (haY : a ∉ Y) : Y ∈ ob Y := by
--   obtain ⟨X,ha,hX⟩ := hbad

--   have : Y ⊆ Y ∩ ((X ∪ Y) \ X ∪ X \ {a}) := by
--     intro y hy
--     simp
--     constructor
--     exact hy
--     by_cases H : y ∈ X
--     · right
--       simp_all
--       intro hc
--       subst hc
--       exact haY hy
--     · tauto
--   have g₀ : Y ∩ ((X ∪ Y) \ X ∪ X \ {a}) ≠ ∅ := by
--     contrapose! hY
--     apply subset_empty.mp
--     apply subset_trans this
--     rw [hY]
--   have g₁ : Y = ((X ∪ Y) \ X ∪ X \ {a}) ∩ Y := by
--     ext i;simp
--     intro hi
--     by_cases H : i ∈ X
--     · exact .inr ⟨H, fun hc => haY $ hc ▸ hi⟩
--     · exact .inl ⟨.inr hi, H⟩
--   have h₀ := t.d5 _ _ (X ∪ Y) sdiff_subset hX subset_union_left
--   have h₁ := t.e5 _ _ _ subset_union_right h₀ g₀
--   have h₂ := t.b5 _ _ (((X ∪ Y) \ X ∪ X \ {a}) ∩ Y)
--     (by simp) h₁
--   convert h₂

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



-- lemma ob_singleton_of_obSelf -- not needed!
--     (a5 : A5 ob) (b5 : B5 ob) (c5 : C5 ob) {a : Fin k}
--     (ha : {a} ∈ ob {a}) : ob {a} = {Y | a ∈ Y}.toFinset := by
--   apply subset_antisymm
--   · intro Y hY -- regular c5 should be enough here
--     simp
--     by_contra H
--     have h₀ : Y ∩ {a} ∈ ob {a} := by
--         apply c5 _ _ _ hY ha
--         have : Y ∩ {a} ∈ ob {a} := by
--             apply b5
--             show Y ∩ {a} = _
--             simp
--             exact hY
--         rw [inter_comm]
--         simp
--         rw [inter_comm]
--         intro hc
--         apply a5
--         rw [hc] at this
--         exact this
--     have h₁ : Y ∩ {a} = ∅ := subset_empty.mp fun i hi => by
--       exfalso
--       simp at hi
--       exact H $ hi.2.symm ▸ hi.1
--     exact a5 _ $ h₁ ▸ h₀
--   · intro Y hY
--     simp at hY
--     exact b5 {a} (Y ∩ {a}) Y (by simp) (by
--       have : Y ∩ {a} = {a} := by
--         apply subset_antisymm <;> (simp;tauto)
--       rw [this]
--       tauto)


structure ADE where
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob)

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

lemma obSelf_univNOA
    (d5 : D5 ob) (e5 : E5 ob) (a : Fin k)
    (ha : univ \ {a} ∈ ob univ) (h : univ \ {a} ≠ ∅) : univ ∈ ob univ := by
  by_cases H : k = 0
  · subst H;have := a.2; simp at this
  have ⟨n,hn⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero H
  subst hn
  have : univ \ {a} ∈ ob (univ \ {a}) :=
    e5 univ  (univ \ {a}) (univ \ {a}) (by simp) ha (by
      simp only [inter_self]
      exact h
    )
  have := d5 (univ \ {a}) (univ \ {a}) univ (by simp) this (by simp)
  convert this using 2
  simp


lemma sdiff_union_sdiff (A B C : Finset (Fin k)) :
    A \ C ⊆ A \ B ∪ B \ C := by
      intro i hi
      simp at hi ⊢
      tauto


lemma obSelfSingleton_of_bad (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
    {a : Fin k} (hbad : bad ob a) : {a} ∈ ob {a} := by
  apply b5 _ univ _ (by simp)
  apply e5 _ _ _ (subset_univ _)
  apply obSelf_univ a5 d5 e5 a
  obtain ⟨X,ha,ha'⟩ := hbad
  have : univ \ {a} = univ \ X ∪ X \ {a} := by
    apply subset_antisymm
    · apply sdiff_union_sdiff
    · intro i hi
      simp at hi ⊢
      cases hi with
        | inl h => exact fun hc => h $ hc ▸ ha
        | inr h => exact h.2
  rw [this]
  apply d5 X (X \ {a}) univ (by simp) ha' (by simp)
  simp

def obSelf (A : Finset (Fin k)) := A ∈ ob A

-- theorem obSelf_of_obSelfSdiff
--     (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
--     {X : Finset (Fin k)} {a : Fin k}
--     (haX : X ≠ ∅)
--     (h : X \ {a} ∈ ob X) : X ∈ ob X := by
--   apply obSelf_of_obSelf ⟨b5, d5, e5⟩ (hY := haX)
--   show X \ {a} ∈ ob (X \ {a})
--   exact e5 X (X \ {a}) (X \ {a}) (by simp) h (by
--     rw [inter_self]
--     intro hc
--     apply a5
--     rw [hc] at h
--     exact h
--   )

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

--
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
  simp at hBC
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
  have hU : #U ≤ k - 2 ∧ inter_ifsub ob U := by
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
  rw [@card_sdiff_of_subset (Fin k) U univ _ (by simp), card_fin] at h
  omega


/-- A trivial consequence of `local_of_global`.  -/
theorem local_of_global'
    (a5 : A5 ob) (d5 : D5 ob) (e5 : E5 ob) {B C : Finset (Fin k)}
    (hBC₀:  Finset.card (C \ B) ≥ 2)
    (hBC₁ : B ⊆ C)
    (hBC₂ : B ∈ ob C) :
     ∃ A, #A ≤ k - 2 ∧ inter_ifsub ob A := by
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

  push_neg at hU
  refine ⟨?_, hA.1⟩
  have : 2 ≤ #((univ : Finset (Fin k))) := by
    apply le_trans
    show 2 ≤ #(U \ A)
    omega
    apply card_le_card
    simp
  have : #(U \ A) = #U - #A := by
    refine card_sdiff_of_subset hU.1
  rw [this] at hU
  have : #U ≤ #((univ : Finset (Fin k))) := by
    apply card_le_card
    simp
  have : #((univ : Finset (Fin k))) = k := card_fin k
  omega



theorem local_of_global₀
    {ob : Finset (Fin 0) → Finset (Finset (Fin 0))}
    (a5 : A5 ob) :
    covering ob := by
  intro C B hBC
  have : B = ∅ := eq_empty_of_isEmpty B
  rw [this] at hBC
  exfalso
  apply a5
  exact hBC

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
  by_cases H : k = 0
  · subst H;apply local_of_global₀ a5
  have ⟨n,hn⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero H
  subst hn
  by_cases H : n = 0
  · subst H
    intro C B ho
    simp [cocos]
    intro hBC
    exact card_le_card $ subset_univ (C \ B)
  · have ⟨m,hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero H
    subst hm
    intro B C ho
    simp [cocos]
    intro hBC
    have hn (A) (hA : #A ≤ m) : ¬ inter_ifsub ob A := by
        intro hc
        specialize large_of_ob A hc
        rw [large_iff_cosubsingleton] at large_of_ob
        omega
    have h_a : ¬ (∃ B C, #(C \ B) ≥ 2 ∧ B ⊆ C ∧ B ∈ ob C) := by
        intro ⟨B,C,hBC⟩
        have := local_of_global' a5 d5 e5 hBC.1 hBC.2.1 hBC.2.2
        revert this
        simp
        exact hn
    push_neg at h_a
    by_contra H
    simp at H
    exact h_a C B H hBC ho

lemma global_holds₀
    {ob : Finset (Fin 0) → Finset (Finset (Fin 0))}
    (A : Finset (Fin 0)) (hs : small₂ A) :
    ¬ inter_ifsub ob A := by
    unfold inter_ifsub small₂ at *
    exfalso
    revert hs
    simp
    suffices #Aᶜ ≤ 0 by omega
    suffices #Aᶜ ≤ #(univ : Finset (Fin 0)) by convert this
    apply card_le_card
    apply subset_univ

lemma global_holds₁
    {ob : Finset (Fin 1) → Finset (Finset (Fin 1))}
    (A : Finset (Fin 1)) (hs : small₂ A) :
    ¬ inter_ifsub ob A := by
    unfold inter_ifsub small₂ at *
    exfalso
    revert hs
    simp
    suffices #Aᶜ ≤ 1 by omega
    suffices #Aᶜ ≤ #(univ : Finset (Fin 1)) by convert this
    apply card_le_card
    apply subset_univ

/-- If `A` is small₂ then `A` is not inter_ifsub.
This is just some set-wrangling on top of `global_holds_specific`.
-/
lemma global_holds (t : @ABCDE k ob)
    (A : Finset (Fin k)) (hs : small₂ A) :
    ¬ inter_ifsub ob A := by
  by_cases H : k ≤ 1
  · have : k = 0 ∨ k = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp H
    cases this with
    | inl h =>
        subst h
        apply global_holds₀ _ hs
    | inr h =>
        subst h
        apply global_holds₁ _ hs
  simp at H
  have ⟨n,hn⟩ : ∃ n, k = n + 2 := Nat.exists_eq_add_of_le' H
  subst hn
  have hA : #A ≤ n := card_compl_aux' hs
  have ⟨a₁,a₂,h₁,h₂,h₁₂⟩: ∃ a₁ a₂, a₁ ∉ A ∧ a₂ ∉ A ∧ a₁ ≠ a₂ := by
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
  exact global_holds_specific t h₁ h₂ h₁₂

theorem local_holds₀
    {ob : Finset (Fin 0) → Finset (Finset (Fin 0))} :
    covering ob := by
  unfold covering cocos
  intro C B h₀
  simp
  constructor
  exact Unique.uniq instUniqueOfIsEmpty B
  intro h₁
  suffices #(C \ B) ≤ 0 by omega
  simp
  intro i
  have := i.2
  simp at this

theorem local_holds₁
    {ob : Finset (Fin 1) → Finset (Finset (Fin 1))} :
    covering ob := by
  unfold covering cocos
  intro C B h₀
  simp
  intro h₁
  suffices #(C \ B) ≤ #(univ : Finset (Fin 1)) by convert this
  apply card_le_card
  apply subset_univ

/-- A direct consequence of `global_holds` and `local_of_global`. -/
theorem local_holds (t : @ABCDE k ob) :
    covering ob := by
  by_cases H : k ≤ 1
  · have : k = 0 ∨ k = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp H
    cases this with
    | inl h => subst h;apply local_holds₀
    | inr h => subst h;apply local_holds₁
  · simp at H
    have ⟨n, hn⟩ : ∃ n, k = n + 2 := Nat.exists_eq_add_of_le' H
    subst hn
    have (A) (hA : inter_ifsub ob A) : cosubsingleton A := by
        rw [large_iff_cosubsingleton]
        contrapose! hA
        exact global_holds t _ $ Nat.lt_add_one_iff.mp $ card_compl_aux hA
    unfold covering cocos
    by_contra H
    push_neg at H
    simp at H
    obtain ⟨B,C,h₀,h₁,h₂⟩ := H
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

def semibad' {n : ℕ} (ob : Finset (Fin n) → Finset (Finset (Fin n))) (a : Fin n) :=
    ∃ X Y : Finset (Fin n), a ∈ X ∩ Y ∧ X \ {a} ∈ ob Y


lemma not_ob_of_almost
    (b5 : B5 ob)
    (H₁ : ∀ a, ¬ semibad' ob a)
    {X Y : Finset (Fin k)}
    (h₀ : #(Y \ X) = 1) : X ∉ ob Y := fun hc => by
  unfold semibad' at H₁
  push_neg at H₁
  have ⟨a,ha⟩: ∃ a, Y \ X = {a} := card_eq_one.mp h₀
  specialize H₁ a Y Y (singleton_subset_iff.mp $ by
    rw [← ha]
    simp)
  rw [← ha, ← diff_diff] at H₁
  exact H₁ $ (b5 Y X (X ∩ Y) (by simp)) hc


/-- A glue lemma for `obSelf_of_ob_of_subset`. -/
lemma obSelf_of_ob_of_almost_subset
  (b5 : B5 ob)
  (H₁ : ∀ a, ¬ semibad' ob a)
  {X Y : Finset (Fin k)}
  (h : X ∈ ob Y)
  (hd : #(Y \ X) ≤ 1)
  : Y ∈ ob Y := by
    cases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with
    | inl h₀ =>
      exact obSelf_of_ob_of_subset b5
        (sdiff_eq_empty_iff_subset.mp $ card_eq_zero.mp h₀) h
    | inr h₀ => exact False.elim $ not_ob_of_almost b5 H₁ h₀ h


lemma semibad_of_semibad'
    (b5 : B5 ob) {a : Fin k} (h : semibad' ob a) : semibad ob a := by
    obtain ⟨Y,X,hXY⟩ := h
    use X, Y
    constructor
    · rw [inter_comm]
      exact hXY.1
    · apply b5 (Y := Y \ {a})
      compare
      exact hXY.2

/-- Not used, but for the record... -/
lemma semibad'_of_semibad
    (b5 : B5 ob) {a : Fin k} (h : semibad ob a) : semibad' ob a := by
    obtain ⟨Y,X,hXY⟩ := h
    use X, Y
    constructor
    · rw [inter_comm]
      exact hXY.1
    ·exact b5 _ _ _ (by compare) hXY.2

lemma semibad'_iff_semibad
    (b5 : B5 ob) {a : Fin k} :
    semibad' ob a ↔ semibad ob a := by
  constructor
  apply semibad_of_semibad' b5
  apply semibad'_of_semibad b5



theorem quasibad.aux {k : ℕ} {ob : Finset (Fin k) → Finset (Finset (Fin k))}
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



/-- Does this really require all of ABCDE? -/
lemma semibad_of_quasibad
    (t : @ABCDE k ob)
    {X Y : Finset (Fin k)} (h : Y ∈ ob X) -- quasibad
    {a : Fin k} (ha : a ∈ X \ Y) :  semibad ob a := by
        have : X ∩ Y ∈ ob X := t.b5 X Y (X ∩ Y) (by compare) h
        use X, X
        rw [quasibad.aux t h ha] at this
        simp at ha ⊢
        tauto

lemma quasibad_iff_semibad (t : @ABCDE k ob)
    (a : Fin k) : @quasibad k ob a ↔ semibad ob a := by
    constructor
    · intro h
      unfold quasibad at h
      obtain ⟨U,V,hUV⟩ := h
      exact semibad_of_quasibad t hUV.2 hUV.1
    · clear t
      intro h
      unfold semibad at h
      unfold quasibad
      obtain ⟨X,Y,hXY⟩ := h
      use X
      use (X ∩ Y) \ {a}
      constructor
      simp at hXY ⊢
      tauto
      tauto




lemma sub_alive.core (a5 : A5 ob) (b5 : B5 ob)
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

lemma sub_alive (t : @ABCDE k ob)
    (H₁ : ∀ a, ¬ semibad ob a) : ∀ Y, ob Y ⊆ alive k Y := by
    have h₀ := quasibad_iff_semibad t
    apply sub_alive.core t.a5 t.b5 (by
        intro a hc
        rw [h₀] at hc
        exact H₁ a hc)
    -- OLD PROOF:
    -- intro X Y h
    -- simp [alive]
    -- constructor
    -- · exact fun hc => t.a5 _ $ t.b5 _ _ _ (by simp) $ hc ▸ h
    -- · by_contra H
    --   unfold semibad at H₁
    --   push_neg at H₁
    --   have ⟨a,ha⟩ : ∃ a, a ∈ X \ Y := Nonempty.exists_mem $ sdiff_nonempty.mpr H
    --   specialize H₁ a X X
    --   have h₁ : X ∩ Y ∈ ob X := t.b5 X Y (X ∩ Y) (by compare) h
    --   rw [quasibad.aux t h ha] at h₁
    --   simp at ha H₁
    --   exact H₁ ha.1 h₁


-- not used
lemma sub_aliveBAD (t : @ABCDE k ob)
    (H₁ : ∀ a, ¬ bad ob a) : ∀ Y, ob Y ⊆ alive k Y := by
    intro X Y h
    simp [alive]
    constructor
    · exact fun hc => t.a5 _ $ t.b5 _ _ _ (by simp) $ hc ▸ h
    · by_contra H
      unfold bad at H₁
      push_neg at H₁
      have ⟨a,ha⟩ : ∃ a, a ∈ X \ Y := Nonempty.exists_mem $ sdiff_nonempty.mpr H
      specialize H₁ a X (by simp at ha;tauto)
      have h₁ : X ∩ Y ∈ ob X := t.b5 X Y (X ∩ Y) (by compare) h
      rw [quasibad.aux t h ha] at h₁
      exact H₁ h₁



-- lemma alive_subMAYBE (t : @ABCDE k ob) (H₀ : ob ≠ noObligations k)
--     (H₁ : ∀ a, ¬ quasibad ob a) : ∀ Y, alive k Y ⊆ ob Y := by
--   unfold quasibad at H₁
--   push_neg at H₁
--   simp [alive]
--   intro X Y
--   simp
--   contrapose! H₁
--   simp
--   sorry

lemma alive_sub_of_no_semibad' (t : @ABCDE k ob) (H₀ : ob ≠ noObligations k)
    (H₁ : ∀ a, ¬ semibad' ob a) : ∀ Y, alive k Y ⊆ ob Y := by
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
  exact t.b5 X X Y (by compare) $ obSelf_of_obSelf ⟨t.b5, t.d5, t.e5⟩
    (obSelf_of_ob_of_almost_subset t.b5 H₁ h' this)
    h₂.1

/--

The implications are

bad →[∅] semibad ↔[B5] semibad' →[∅] quasibad →[ABCDE5] semibad →[AE5] bad

bad, quasibad = bad for the man with the dog and no fence
unique_bad = bad for Carmo and Jones' theory!

-/
lemma alive_sub (t : @ABCDE k ob) (H₀ : ob ≠ noObligations k)
    (H₁ : ∀ a, ¬ semibad ob a) : ∀ Y, alive k Y ⊆ ob Y := by
  apply alive_sub_of_no_semibad' t H₀
  simp_rw [semibad'_iff_semibad t.b5]
  exact H₁

lemma alive_of_no_bad (t : @ABCDE k ob) (H₀ : ob ≠ noObligations k)
    (H₁ : ∀ a, ¬ semibad ob a) : ob = alive k := (Set.eqOn_univ _ _).mp fun Y _ => by
  apply subset_antisymm
  apply sub_alive t H₁
  apply alive_sub t H₀ H₁

theorem unique_bad (t : @ABCDE k ob) -- maybe five.d instead of t.d5?
    {a b : Fin k} (ha : bad ob a) (hb : bad ob b) : a = b := by
  obtain ⟨X,ha, hoa⟩ := ha
  obtain ⟨Y,hb, hob⟩ := hb
  have h₁ : (X ∪ Y) \ {a} ∈ ob (X ∪ Y) := by
    convert t.d5 _ _ (X ∪ Y) (by simp) hoa (by simp) using 1
    apply union_diff_singleton ; tauto
  have h₃ : (X ∪ Y) \ {b} ∈ ob (X ∪ Y) := by
    convert t.d5 _ _ (X ∪ Y) (by simp) hob (by simp) using 1
    convert union_diff_singleton Y X hb using 2
    · exact union_comm X Y
    · nth_rewrite 1 [union_comm]
      rfl
  have : #({a,b}) ≤ 1 := by
    have := local_holds_apply t (t.c5 _ _ _ h₁ h₃)
    unfold cocos at this
    simp at this
    specialize this (subset_trans inter_subset_union $ union_subset sdiff_subset sdiff_subset)
    convert this using 2
    apply pair_venn <;> tauto
  cases Nat.eq_or_lt_of_le this with
  | inl h =>
    by_contra H
    have := card_pair H
    omega
  | inr h => simp at h

theorem bad_cosubsingleton_of_ob (t : @ABCDE k ob)
    {a : Fin k}
    (hbad : bad ob a)
    {X Y : Finset (Fin k)}
    (h' : X ∩ Y ∈ ob X) :
    X ∩ Y = X ∨ X ∩ Y = X \ {a} := by
  obtain ⟨X',haX',imp⟩ := hbad
  have := local_holds_apply t
    h'
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

/-- If `X` contains a semibad world `b` and
at least one other world `a` then `X` is self-obligatory.
 -/
-- lemma obSelf_of_bad_mem {k : ℕ} {ob : Finset (Fin k) → Finset (Finset (Fin k))}
--     (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
--     {b : Fin k} (H₁ : bad ob b)
--     {X : Finset (Fin k)} (G : ¬X = {b}) (H₀ : b ∈ X) :
--     X ∈ ob X :=
--     obSelf_of_obSelfSdiff a5 b5 d5 e5 (ne_empty_of_mem H₀)
--     $ obSelfSdiff_of_bad ⟨b5, d5, e5⟩ H₁ $ sdiff_ne_empty_of_ne_empty_of_mem G H₀




-- /-- This works, but is not needed for the characterization. -/
-- theorem ob_bad
--     (a5 : A5 ob) (b5 : B5 ob) (c5 : C5 ob) (d5 : D5 ob) (e5 : E5 ob)
--     (a : Fin k)
--     (hbad : bad ob a) : ob {a} = {Y | a ∈ Y}.toFinset :=
--   ob_singleton_of_obSelf a5 b5 c5
--          $ obSelfSingleton_of_bad a5 b5 d5 e5 hbad

theorem bad_of_semibad
    (a5 : A5 ob) (e5 : E5 ob)
    {a : Fin k} (H₁ : semibad ob a) : bad ob a := by
  obtain ⟨Y',X',⟨H₁₀,H₁₁⟩⟩ := H₁
  rw [inter_comm] at H₁₁ H₁₀
  have h₁ :  X' ∩ Y' ∩ ((X' ∩ Y') \ {a}) ≠ ∅ := by
      rw [inter_eq_right.mpr sdiff_subset]
      exact fun hc => a5 _ $ hc ▸ H₁₁
  exact ⟨(X' ∩ Y'), H₁₀, e5 _ _ _ inter_subset_right H₁₁ h₁⟩

-- lemma obSelf_of_bad_mem {k : ℕ} {ob : Finset (Fin k) → Finset (Finset (Fin k))}
--     (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
--     {b : Fin k} (H₁ : bad ob b)
--     {X : Finset (Fin k)} (G : X \ {b} ≠ ∅) :
--     X ∈ ob X :=
--     obSelf_of_obSelfSdiff a5 b5 d5 e5 (by contrapose! G;rw [G];simp)
--     $ obSelfSdiff_of_bad ⟨b5, d5, e5⟩ H₁ G

-- lemma obSelf_of_bad_nonsingle
--     (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
--     {a : Fin k} (hbad : bad ob a) {X : Finset (Fin k)}
--     (ha : X ≠ {a})
--     (he : X ≠ ∅) : X ∈ ob X := by
--   apply obSelf_of_obSelfSdiff a5 b5 d5 e5 he
--   apply obSelfSdiff_of_bad ⟨b5, d5, e5⟩ hbad
--   simp
--   tauto

lemma diff_ne
{a : Fin k}
{X : Finset (Fin k)}
(ha : X ≠ {a})
(he : X ≠ ∅) : X \ {a} ≠ ∅ := by simp;tauto


lemma obSelf_of_bad_nonsingle (t : @BDE k ob)
    {a : Fin k} (hbad : bad ob a) {X : Finset (Fin k)}
    (ha : X ≠ {a})
    (he : X ≠ ∅) : X ∈ ob X := by
  apply obSelf_of_obSelfSdiff t (han := diff_ne ha he)
  exact obSelfSdiff_of_bad t hbad (han := diff_ne ha he)

--   apply obSelf_of_bad_mem a5 b5 d5 e5 hbad h

--   by_cases H₀ : a ∈ X
--   ·
--     exact obSelf_of_bad_mem   a5 b5  d5  e5  hbad ha H₀
--   · exact obSelf_of_bad_not_mem ⟨b5, d5, e5⟩ hbad he H₀

theorem obSelf_of_bad
    (a5 : A5 ob) (b5 : B5 ob) (d5 : D5 ob) (e5 : E5 ob)
    (hbad : ∃ a, bad ob a) {X : Finset (Fin k)}
    (he : X ≠ ∅) : X ∈ ob X := by
  obtain ⟨a,hbad⟩ := hbad
  by_cases ha : X = {a}
  · exact ha ▸ obSelfSingleton_of_bad a5 b5 d5 e5 hbad
  · exact obSelf_of_bad_nonsingle ⟨b5, d5, e5⟩ hbad ha he

theorem sub_stayAlive_of_bad (t : @ABCDE k ob)
    {a : Fin k} (hbad : bad ob a) : ∀ Y, ob Y ⊆ stayAlive a Y:= by
    intro X Y
    simp [stayAlive]
    · intro h
      have h' : X ∩ Y ∈ ob X := t.b5 X Y (X ∩ Y) (by compare) h
      constructor
      · exact fun hc => t.a5 _ <| hc ▸ h'
      · cases bad_cosubsingleton_of_ob t hbad h' with
          | inl h => rw [h]; simp
          | inr h => rw [h]

-- theorem stayAlive_sub_of_badOLD
--     (a5 : A5 ob) (b5 : B5 ob) (c5 : C5 ob) (d5 : D5 ob) (e5 : E5 ob)
--     {a : Fin k} (hbad : bad ob a) : ∀ Y, stayAlive a Y ⊆ ob Y:= by
--     intro X Y
--     simp [stayAlive]
--     · by_cases G : X = {a}
--       · subst G
--         rw [ob_bad a5 b5 c5 d5 e5 (hbad := hbad)]
--         simp
--         contrapose!
--         intro h
--         exact singleton_inter_of_notMem h

--       · intro h hh
--         apply b5 X (X ∩ Y) Y (by simp)
--         have hX : X ≠ ∅ := fun hc => by simp [hc] at h
--         cases all_or_almost hh with
--         | inl h₀ => rw [h₀]; exact obSelf_of_bad a5 b5 d5 e5 hbad G hX
--         | inr h' => exact h' ▸ obSelfSdiff_of_bad ⟨b5, d5, e5⟩ hbad (Y := X) $ h' ▸ h

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
theorem models_ofCJ_1997 (t : @ABCDE k ob) --June 11, 2025
:
  (∃ a, ob = stayAlive a) ∨ ob = alive k ∨ ob = noObligations k := by
  by_cases H₀ : ob = noObligations k
  · exact .inr $ .inr H₀
  · by_cases H₁ : ∃ a, semibad ob a
    · left
      obtain ⟨a,H₁⟩ := H₁
      use a
      exact stayAlive_of_bad t (bad_of_semibad t.a5 t.e5 H₁)
    · push_neg at H₁
      exact .inr $ .inl $ alive_of_no_bad t H₀ H₁

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
