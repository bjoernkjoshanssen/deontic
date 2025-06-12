import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Deontic.Venn
/-!
# Lemma II.2.2

We prove Lemma II.2.2 from [Carmo and Jones 2022].

We show that Observation 5.2 is correct except that the example
does not satisfy 5(e).
-/

open Set

-- Carmo and Jones' axioms
def CJ5a {U : Type*} (ob : Set U → Set (Set U)) :=
    ∀ (X : Set U), ∅ ∉ ob X

def CJ5b {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (X Y Z : Set U), Z ∩ X = Y ∩ X → (Z ∈ ob X ↔ Y ∈ ob X)

/- This is the old one from 2002.
 def CJ5c (ob : Set U → Set (Set U)) :=
 ∀ (X Y Z : Set U), Y ∈ ob X → (Z ∈ ob X → Y ∩ Z ∈ ob X)
-/

def CJ5c_star {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (X : Set U) (β : Set (Set U)),
  (h1 : β ⊆ ob X) → (h2 : β ≠ ∅) → ⋂₀β ∩ X ≠ ∅ → ⋂₀β ∈ ob X

def CJ5c_star_finite {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (X : Set U) (Y Z : (Set U)),
  (Y ∈ ob X) → (Z ∈ ob X) → (X ∩ Y ∩ Z ≠ ∅) → (Y ∩ Z) ∈ ob X

def CJ5d {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (X Y Z : Set U), Y ⊆ X → Y ∈ ob X → X ⊆ Z → (Z \ X) ∪ Y ∈ ob Z

def CJ5e {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (X Y Z : Set U), Y ⊆ X → Z ∈ ob X → Y ∩ Z ≠ ∅ → Z ∈ ob Y

def CJ5bd {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (X Y Z : Set U), Y ∈ ob (X) ∧ X ⊆ Z → (Z \ X) ∪ Y ∈ ob Z

theorem bdImpliesD {U : Type*} (ob : Set U → Set (Set U))
    (h : CJ5bd ob) : CJ5d ob := by
  unfold CJ5d
  unfold CJ5bd at h
  intro X Y Z h₀ h₁ h₂
  apply h; tauto

def CJ5f {U : Type*} (ob : Set U → Set (Set U)) :=
  ∀ (β : Set (Set U)) (_ : β ≠ ∅) (X : Set U),
  (∀ Z, Z ∈ β →  X ∈ ob Z)  → (X ∈ ob (⋃₀ β))


def CJ5g {U : Type*}
    (ob : Set U → Set (Set U)) :=
  ∀ (X Y Z : Set U), Y ∈ ob X → Z ∈ ob Y →
    X ∩ Y ∩ Z ≠ ∅ → Y ∩ Z ∈ ob X


--Lemma II.2.1 --
theorem bd5 {U : Type*} {ob : Set U → Set (Set U)}
    (b5 : CJ5b ob) (d5 : CJ5d ob) : CJ5bd ob := by
  intro X Y Z h
  have sets_eq : ((Z \ X) ∪ (Y ∩ X)) ∩ Z = ((Z \ X) ∪ Y) ∩ Z := by
    ext
    simp
    tauto
  have input2 : Y ∩ X ∈ ob X :=
    (b5 X Y (Y ∩ X) (by rw [inter_assoc, inter_self])).mpr h.1
  exact (b5 Z ((Z \ X) ∪ Y) ((Z \ X) ∪ (Y ∩ X)) sets_eq).mp
    (d5 X (Y ∩ X) Z inter_subset_right input2 h.2)


lemma implication_in_ob {U : Type*} {ob : Set U → Set (Set U)}
    (b5 : CJ5b ob) (d5 : CJ5d  ob) {β : Set (Set U)} {X : Set U}
    (h : X ∈ ⋂₀ (ob '' β)) : {(⋃₀ β \ Z) ∪ X | Z ∈ β} ⊆ ob (⋃₀ β) := by
  have h : ∀ Z ∈ β, X ∈ ob Z := by simp at h;exact h
  exact fun _ ⟨Y,hY⟩ => hY.2 ▸ bd5 b5 d5 Y X (⋃₀ β)
    ⟨h Y hY.1, fun _ hy => mem_sUnion.mpr ⟨Y,hY.1, hy⟩⟩

lemma inter_not_empty {U : Type*} {ob : Set U → Set (Set U)}
    {β : Set (Set U)} {X : Set U} (h2 : β ≠ ∅)
    (h3 : ∀ Z ∈ β, X ∈ ob Z) (a5 : CJ5a ob) (b5 : CJ5b ob) :
    ⋂₀ {⋃₀ β \ Z ∪ X | Z ∈ β} ∩ ⋃₀ β ≠ ∅ := by
  obtain ⟨Z, hZ⟩ := exists_mem_of_ne_empty h2
  have hZ2 := h3 Z hZ
  have xz_not_empty : X ∩ Z ≠ ∅ := by
    intro hc
    apply a5 Z
    specialize b5 Z ∅ X (by rw [hc,empty_inter])
    apply b5.mp <| h3 _ hZ
  have xz_subset_xh : X ∩ Z ⊆ X ∩ ⋃₀β := fun a ha =>
    ⟨ha.1, mem_sUnion.mpr ⟨Z,hZ, ha.2⟩⟩
  rw [← in_union_yet_in_none' X h2]
  exact fun hi => xz_not_empty <| subset_eq_empty (hi ▸ xz_subset_xh) rfl

/-- Lemma II.2.2 Formalized by RJ Reiff. -/
theorem II_2_2 {U : Type} {ob : Set U → Set (Set U)} (a5 : CJ5a ob)
    (b5 : CJ5b ob) (cstar5 : CJ5c_star ob) (d5 : CJ5d ob) : CJ5f ob := by
  intro β h2 X h3
  rw [in_union_yet_in_none' X h2]
  have h3₀ : X ∈ ⋂₀ (ob '' β) := by simp; exact h3
  exact cstar5
    (⋃₀ β) {(⋃₀ β \ Z) ∪ X | Z ∈ β}
    (implication_in_ob b5 d5 h3₀)
    (not_empty X h2)
    (inter_not_empty h2 h3 a5 b5)


/--

Lemma II-2-1
Assuming condition (5b), the following condition below is equivalent to (5d):
(5bd) if Y∈ob(X) and X⊆Z, then ((Z-X) ∪ Y) ∈ ob(Z)
-/
lemma II_2_1 {U : Type} {ob : Set U → Set (Set U)}
    (b5 : CJ5b ob) : CJ5d ob ↔ CJ5bd ob := ⟨bd5 b5, by tauto⟩



/--
The deduction of (5-g) is as follows:

From `Y ∈ ob(X)` deduce `((X∪Y)-X)∪Y)∈ob(X∪Y)`, i.e., `Y∈ob(X∪Y)`
(take into account that `X⊆(X∪Y)`, and use lemma II-2-1 of [2]);

Analogously, from `Z∈ob(X)` deduce `((X∪Y)-Y)∪Z)∈ob(X∪Y)`, i.e., `((X-Y)∪Z)∈ob(X∪Y)`;

Since `X∩Y∩Z≠∅`, we have that `Y∩((X-Y)∪Z)∩(X∪Y) = Y∩Z ≠ ∅`, and so, by condition (5-c),
`Y∩((X-Y)∪Z))∈ob(X∪Y)`, i.e., `Y∩Z∈ob(X∪Y)`;

But then, from `Y∩Z∈ob(X∪Y)`, `X⊆(X∪Y)` and `X∩Y∩Z≠∅`, by condition (5-e),
it follows that `Y∩Z∈ob(X)` (as we wish to prove).
(Formalized May 26, 2025.)
-/
theorem Observation_5_1_2 {U : Type} {ob : Set U → Set (Set U)}
    (b5 : CJ5b ob) (cstar5 : CJ5c_star ob) (d5 : CJ5d ob) (e5: CJ5e ob) :
    CJ5g ob := by
  intro X Y Z h₀ h₁ h₂
  have g₀ : CJ5bd ob := @bd5 U ob b5 d5
  have h₀ : ((X ∪ Y) \ X) ∪ Y ∈ ob (X∪Y) := by
    apply g₀
    tauto
  have h₁ : Y ∈ ob (X∪Y) := by
    convert h₀
    ext;simp;tauto
  have h₆ : ((X ∪ Y) \ Y) ∪ Z ∈ ob (X∪Y) := by
    apply g₀
    tauto
  have h₅ : Y ∩ Z ≠ ∅ := by
    revert h₂
    contrapose!
    intro h
    ext i
    simp
    intro g₀ g₁ g₂
    have : i ∈ Y ∩ Z := by simp;tauto
    aesop
  have by5c : Y ∩ ((X \ Y) ∪ Z) ∈ ob (X∪Y) := by
    unfold CJ5c_star at cstar5
    have := @cstar5 (X ∪ Y) {Y, X \ Y ∪ Z}
      (by
        intro S hS
        simp at hS
        cases hS with
        | inl h => symm at h;subst h;tauto
        | inr h => rw [h];simp at h₆;tauto
        ) (by
          exact Ne.symm (ne_insert_of_not_mem {X \ Y ∪ Z} id))
          (by
          revert h₂
          simp
          contrapose!
          intro h
          have h₄ : Y ∩ ((X \ Y) ∪ Z) ∩ (X ∪ Y) = Y ∩ Z  := by
            ext;simp;tauto
          rw [h₄] at h
          rw [inter_assoc]
          rw [h]
          simp)
    simp at this
    tauto
  apply e5
  show X ⊆ X ∪ Y
  simp
  have : Y ∩ Z = Y ∩ (X \ Y ∪ Z) := by ext;simp;tauto
  rw [this]
  tauto
  revert h₂
  simp
  contrapose!
  intro h
  rw [← h]
  exact inter_assoc X Y Z

open Classical
/-- The function ob from Carmo and Jones 2022 Observation 5.2. -/
def observation_5_2 (X : Set (Fin 4)) : Set (Set (Fin 4)) :=
  ite (X ∩ {0,1} = ∅)
    {Y | Y ∩ X = {3}}
    {Y | Y ⊇ {0,1} ∩ X}


lemma ob52_a : CJ5a observation_5_2 := fun X h => by
  unfold observation_5_2 at h
  by_cases H : X ∩ {0,1} = ∅
  rw [H] at h
  simp at h
  revert h
  simp
  apply ne_of_not_superset
  exact fun a ↦ a rfl
  rw [if_neg H] at h
  simp at h
  apply H
  rw [inter_comm] at h
  exact h

lemma ob52_b : CJ5b observation_5_2 := fun X Y₀ Y₁ h₀ => by
  unfold observation_5_2
  constructor
  · intro h
    simp at h
    by_cases H : X ∩ {0,1} = ∅
    · rw [H] at h
      simp at h
      rw [H]
      simp
      aesop
    · rw [if_neg H] at h ⊢
      simp at h ⊢
      intro i hi
      suffices i ∈ Y₀ ∩ X by
        aesop
      rw [← h₀]
      simp
      constructor
      tauto
      simp at hi
      tauto
  · intro h
    simp at h
    by_cases H : X ∩ {0,1} = ∅
    · rw [H] at h
      simp at h
      rw [H]
      simp
      aesop
    · rw [if_neg H] at h ⊢
      simp at h ⊢
      intro i hi
      suffices i ∈ Y₁ ∩ X by
        simp at this
        aesop
      rw [h₀]
      simp
      constructor
      tauto
      simp at hi
      tauto

lemma ob52_c : CJ5c_star observation_5_2 := fun X 𝓢 h₀ h₁ h₂ => by
  obtain ⟨S,hS⟩ : ∃ S, S ∈ 𝓢 := exists_mem_of_ne_empty h₁
  unfold observation_5_2 at h₀ ⊢
  by_cases H : X ∩ {0,1} = ∅
  rw [H] at h₀ ⊢
  simp at h₀ ⊢
  ext i
  simp
  constructor
  · intro h
    have := h.1
    have := this S hS
    have := h₀ hS
    simp at this
    suffices i ∈ ({3} : Set (Fin 4)) by
      simp at this
      exact this
    rw [← this]
    simp
    tauto
  · intro h
    subst h
    constructor
    · intro T hT
      specialize h₀ hT
      simp at h₀
      suffices 3 ∈ T ∩ X by exact mem_of_mem_inter_left this
      rw [h₀]
      simp
    · specialize h₀ hS
      simp at h₀
      suffices 3 ∈ S ∩ X by exact mem_of_mem_inter_right this
      rw [h₀]
      simp
  rw [if_neg H] at h₀ ⊢
  simp at h₀ ⊢
  exact h₀

/-- Surprisingly, 5(e) is NOT true
despite what CJ 2022 claim.
The mistake in the detailed proof supplied on Feb 2, 2022
is that we are in Case 1 and although I'll grant that
Z ∩ Y ⊇ {0,1} ∩ Y, this doesn't matter since {0,1} ∩ Y = ∅.

-/
lemma ob52_e' : ¬ CJ5e observation_5_2 := by
  intro h
  specialize h {0,2} {2} {2,0}
  unfold observation_5_2 at h
  simp at h
  split at h
  next h_1 =>
    simp_all only [Fin.isValue, mem_setOf_eq]
    have : (0 : Fin 4) ∈ ({0,2} : Set (Fin 4)) ∩ {0,1} := by simp
    rw [h_1] at this
    simp at this
  next h_1 =>
    simp_all only [Fin.isValue, mem_setOf_eq]
    specialize h (by
      intro j hj
      simp at hj⊢
      fin_cases j <;> tauto)
    have : 2 ∈ ({2,0} : Set (Fin 4)) ∩ {2} := by simp
    rw [h] at this
    simp at this

lemma q_in : {0,1} ∈ observation_5_2 univ:= by
  unfold observation_5_2
  simp
  rw [if_neg (by
    refine nonempty_iff_ne_empty'.mp ?_
    exact instNonemptyElemInsert 0 {1})]
  simp

lemma r_not_in : ¬ {0,2} ∈ observation_5_2 (univ \ {0,1}):= by
  intro hc
  unfold observation_5_2 at hc
  simp at hc
  have : 3 ∈ ({3} : Set (Fin 4)) := by simp
  rw [← hc] at this
  simp at this


lemma ob52_g : CJ5g observation_5_2 := by
  unfold CJ5g
  intro X Y Z h₀ h₁ h₂
  unfold observation_5_2 at *
  by_cases H₀ : X ∩ {0,1} = ∅
  rw [H₀] at h₀ ⊢
  simp_all
  by_cases H₁ : Y ∩ {0,1} = ∅
  · rw [H₁] at h₁
    simp at h₁
    apply subset_antisymm
    apply subset_trans
    show Y ∩ Z ∩ X ⊆ Z ∩ Y
    intro;simp;tauto
    exact Eq.subset h₁
    intro i hi
    simp at hi
    subst hi
    simp_all
    constructor
    suffices 3 ∈ Z ∩ Y by simp at this;tauto
    rw [h₁]
    simp
    suffices 3 ∈ Y ∩ X by simp at this;tauto
    rw [h₀]
    simp
  · rw [if_neg H₁] at h₁
    simp at h₁
    apply subset_antisymm
    apply subset_trans
    show Y ∩ Z ∩ X ⊆ Y ∩ X
    intro;simp;tauto
    exact Eq.subset h₀
    intro i hi
    simp at hi
    subst hi
    -- simp_all
    constructor
    · have : 3 ∈ Y := by
        suffices 3 ∈ Y ∩ X by simp at this;tauto
        rw [h₀]
        simp
      constructor
      tauto
      obtain ⟨j,hj⟩ : ∃ j, j ∈ X ∩ Y ∩ Z := by
        refine nonempty_def.mp ?_
        exact nonempty_iff_ne_empty.mpr h₂
      fin_cases j
      · simp at hj
        have : 0 ∈ X ∩ {0, 1} := by simp;tauto
        rw [H₀] at this
        simp at this
      · simp at hj
        have : 1 ∈ X ∩ {0, 1} := by simp;tauto
        rw [H₀] at this
        simp at this
      · simp at hj
        have : 2 ∈ Y ∩ X := by simp;tauto
        rw [h₀] at this
        simp at this
      · simp at hj
        tauto
    · suffices 3 ∈ Y ∩ X by simp at this;tauto
      rw [h₀]
      simp
  rw [if_neg H₀] at h₀ ⊢
  simp at h₀ ⊢
  constructor
  · tauto
  · by_cases H₁ : Y ∩ {0,1} = ∅
    · rw [H₁] at h₁
      simp at h₁
      intro i hi
      fin_cases i
      · simp at hi ⊢
        exfalso
        have : 0 ∈ Y ∩ {0,1} := by simp;tauto
        rw [H₁] at this
        simp at this
      · simp at hi ⊢
        exfalso
        have : 1 ∈ {0,1} ∩ X := by simp;tauto
        have : 1 ∈ Y ∩ {0,1} := by simp;apply h₀;simp;tauto
        rw [H₁] at this
        simp at this
      · simp at hi ⊢
      · simp at hi ⊢
    · rw [if_neg H₁] at h₁
      simp at h₁
      intro i hi
      apply h₁
      simp at hi ⊢
      constructor
      tauto
      apply h₀
      simp
      constructor
      tauto
      tauto

lemma ob52_f : CJ5f observation_5_2 := by
  unfold CJ5f
  intro 𝓢 h𝓢 X h
  unfold observation_5_2 at h ⊢
  by_cases H₀ : ⋃₀ 𝓢 ∩ {0, 1} = ∅
  · rw [H₀]
    simp
    obtain ⟨A,hA⟩ : ∃ A, A ∈ 𝓢 := exists_mem_of_ne_empty h𝓢
    have h' := h A hA
    by_cases H₁ : A ∩ {0,1} = ∅
    · rw [H₁] at h'
      apply subset_antisymm
      · intro i hi
        fin_cases i
        simp_all
        have : 0 ∈ ⋃₀ 𝓢 := mem_of_mem_inter_right hi
        have : 0 ∈ ⋃₀ 𝓢 ∩ {0, 1} := by simp;tauto
        rw [H₀] at this
        simp at this
        simp_all
        have : 1 ∈ ⋃₀ 𝓢 := mem_of_mem_inter_right hi
        have : 1 ∈ ⋃₀ 𝓢 ∩ {0, 1} := by simp;tauto
        rw [H₀] at this
        simp at this
        simp_all
        obtain ⟨T,hT⟩ := hi.2
        have h'' := h T hT.1
        by_cases H₂ : T ∩ {0,1} = ∅
        rw [H₂] at h''
        simp at h''
        have : 2 ∈ X ∩ T := by simp;tauto
        rw [h''] at this
        simp at this

        rw [if_neg H₂] at h''
        simp at h''

        apply H₂
        apply eq_empty_of_subset_empty
        apply subset_trans
        show T ∩ {0,1} ⊆ ( ⋃₀ 𝓢 ∩ {0, 1})
        intro i hi
        simp at hi ⊢
        simp_all
        use T
        tauto
        rw [H₀]

        simp at hi ⊢
      · intro i hi
        simp at hi
        subst hi
        simp at h ⊢
        constructor
        · simp at h'
          suffices 3 ∈ X ∩ A by simp at this;aesop
          rw [h']
          simp
        use A
        simp_all
        suffices 3 ∈ X ∩ A by simp at this;aesop
        rw [h']
        simp
    · rw [if_neg H₁] at h'
      simp at h'
      ext i
      fin_cases i
      · simp
        intro hX B hB
        specialize h B hB
        by_cases H₂ : B ∩ {0,1} = ∅
        · -- easy
          intro hc
          have : 0 ∈ B ∩ {0,1} := by simp;tauto
          rw [H₂] at this
          simp at this

        · intro hc
          rw [if_neg H₂] at h
          simp at h
          have : 0 ∈ ⋃₀ 𝓢 ∩ {0, 1} := by
            simp
            use B
          rw [H₀] at this
          simp at this
      · simp
        intro hX B hB
        specialize h B hB
        by_cases H₂ : B ∩ {0,1} = ∅
        · -- easy
          intro hc
          have : 1 ∈ B ∩ {0,1} := by simp;tauto
          rw [H₂] at this
          simp at this
        · intro hc
          rw [if_neg H₂] at h
          simp at h
          have : 1 ∈ ⋃₀ 𝓢 ∩ {0, 1} := by
            simp
            use B
          rw [H₀] at this
          simp at this


      · exfalso
        apply H₁
        apply eq_empty_of_subset_empty
        apply subset_trans
        show A ∩ {0,1} ⊆ ⋃₀ 𝓢 ∩ {0, 1}
        simp
        intro i hi
        use A
        constructor
        tauto
        exact hi.1
        rw [H₀]
      · exfalso
        apply H₁
        apply eq_empty_of_subset_empty
        apply subset_trans
        show A ∩ {0,1} ⊆ ⋃₀ 𝓢 ∩ {0, 1}
        simp
        intro i hi
        use A
        constructor
        tauto
        exact hi.1
        rw [H₀]
  · rw [if_neg H₀]
    simp
    intro i hi
    simp at hi
    obtain ⟨A,hA⟩ := hi.2
    specialize h A hA.1
    by_cases H₁ : A ∩ {0,1} = ∅
    rw [H₁] at h
    simp at h
    fin_cases i

    simp_all
    exfalso
    have : 0 ∈ A ∩ {0,1} := by simp;tauto
    rw [H₁] at this
    simp at this

    simp_all
    exfalso
    have : 1 ∈ A ∩ {0,1} := by simp;tauto
    rw [H₁] at this
    simp at this

    simp_all
    simp_all

    fin_cases i
    · simp_all
      aesop
    · simp_all
      aesop
    · simp_all
    · simp_all
