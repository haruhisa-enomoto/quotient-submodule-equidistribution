import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexReverseLastInvariance
import QuotientSubmoduleEquidistribution.RepresentationTheory.NormalizedFourVertexLadderRealization

/-!
# Three-vertex factor-ladder endpoint

A rooted bad deleted support of cardinality three is exactly the support of
a projectively based admissible AR hook.  The proof adjoins one isolated
projective boundary vertex, relabels the augmented support by `Fin 4`, and
applies the certified normalized four-vertex boundary classifier.  The dummy
boundary rules out the hookless outcome.  Uniqueness on a three-element
support then identifies bad supports with projective strip triples, whose
cardinality is invariant under aligned biduality.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped BigOperators

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {k R : Type u} [Field k] [IsAlgClosed k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

namespace ThreeVertex

open QuotientSubmoduleEquidistribution.NormalizedFourVertexLadderClassification
open QuotientSubmoduleEquidistribution.FactorLadder

def optionExtendVector {D : Type*} (v : IntVector D) :
    IntVector (Option D)
  | none => 0
  | some x => v x

def optionExtendAddHom {D : Type*}
    (f : IntVector D →+ IntVector D) :
    IntVector (Option D) →+ IntVector (Option D) where
  toFun v
    | none => 0
    | some y => f (fun x => v (some x)) y
  map_zero' := by
    funext y
    cases y with
    | none => rfl
    | some y =>
        change f (0 : IntVector D) y = 0
        exact congrFun f.map_zero y
  map_add' v w := by
    funext y
    cases y with
    | none => rfl
    | some y =>
        change f ((fun x => v (some x)) +
          (fun x => w (some x))) y = _
        exact congrFun (f.map_add
          (fun x => v (some x)) (fun x => w (some x))) y

def optionAugmentation {D : Type*} (A : Data D) : Data (Option D) where
  theta := optionExtendAddHom A.theta
  tau := optionExtendAddHom A.tau

@[simp]
theorem optionExtendAddHom_apply_extend {D : Type*}
    (f : IntVector D →+ IntVector D) (v : IntVector D) :
    optionExtendAddHom f (optionExtendVector v) =
      optionExtendVector (f v) := by
  funext y
  cases y <;> rfl

@[simp]
theorem optionExtendVector_sub {D : Type*}
    (v w : IntVector D) :
    optionExtendVector (v - w) =
      optionExtendVector v - optionExtendVector w := by
  funext y
  cases y <;> rfl

@[simp]
theorem optionExtendVector_positivePart {D : Type*}
    (v : IntVector D) :
    optionExtendVector (positivePart v) =
      positivePart (optionExtendVector v) := by
  funext y
  cases y <;> simp [optionExtendVector, positivePart]

theorem optionAugmentation_ladder {D : Type*}
    (A : Data D) (x : D) (n : ℕ) :
    (optionAugmentation A).ladder (some x) n =
      optionExtendVector (A.ladder x n) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      funext y
      cases y with
      | none => simp [Data.ladder_zero, FactorLadder.basis,
          optionAugmentation, optionExtendVector]
      | some y =>
          simp only [Data.ladder_zero, optionExtendVector]
          by_cases h : y = x <;> simp [FactorLadder.basis, h]
  | one =>
      rw [Data.ladder_one, Data.ladder_one]
      change optionExtendAddHom A.theta (basis (some x)) =
        optionExtendVector (A.theta (basis x))
      have hbasis : (fun y => basis (some x) (some y)) = basis x := by
        funext y
        by_cases h : y = x <;> simp [basis, h]
      funext y
      cases y with
      | none => rfl
      | some y =>
          change A.theta (fun z => basis (some x) (some z)) y =
            A.theta (basis x) y
          rw [hbasis]
  | more n hn hn1 =>
      rw [show n + 2 = n + 2 by rfl, Data.ladder_add_two,
        Data.ladder_add_two, hn, hn1]
      simp [optionAugmentation]

def labelEquivOfCardThree
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ)) :
    Option (DeletedLabel ((Deleted : Set ι)ᶜ)) ≃ Vertex := by
  classical
  have hD : Fintype.card (DeletedLabel ((Deleted : Set ι)ᶜ)) = 3 := by
    rw [← Nat.card_eq_fintype_card,
      natCard_deletedLabel_compl Deleted]
    exact hcard
  let e₀ : Option (DeletedLabel ((Deleted : Set ι)ᶜ)) ≃ Vertex :=
    Fintype.equivFinOfCardEq (by simp [hD])
  exact e₀.trans (Equiv.swap (e₀ (some p)) 0)

@[simp]
theorem labelEquivOfCardThree_apply_distinguished
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ)) :
    labelEquivOfCardThree Deleted hcard p (some p) = 0 := by
  classical
  simp [labelEquivOfCardThree]

def augmentedEdge {K : Set ι}
    (x y : Option (DeletedLabel K)) : Prop :=
  match x, y with
  | some x, some y =>
      HasIrreducibleMorphism (σ.obj x.1) (σ.obj y.1)
  | _, _ => False

noncomputable def augmentedEdgeBool {K : Set ι}
    (x y : Option (DeletedLabel K)) : Bool := by
  classical
  exact if augmentedEdge σ x y then true else false

set_option linter.unusedSectionVars false in
theorem augmentedEdgeBool_eq_true_iff {K : Set ι}
    (x y : Option (DeletedLabel K)) :
    augmentedEdgeBool (σ := σ) x y = true ↔ augmentedEdge σ x y := by
  classical
  simp [augmentedEdgeBool]

def augmentedTauTarget {K : Set ι}
    (x : Option (DeletedLabel K)) :
    Option (Option (DeletedLabel K)) :=
  match x with
  | none => none
  | some x =>
      (factorLadderTauTarget (σ := σ) (D := AR) K x).map some

def augmentedBoundary {K : Set ι}
    (x : Option (DeletedLabel K)) : Prop :=
  match x with
  | none => True
  | some x => Projective (σ.obj x.1)

def augmentedCode
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ)) : Code := by
  classical
  let e := labelEquivOfCardThree Deleted hcard p
  exact codeOfEquiv e
    (fun x y => augmentedEdgeBool (σ := σ) x y = true)
    (augmentedTauTarget σ AR)

def augmentedBoundaryCode
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ)) : AdditionalBoundary := by
  classical
  let e := labelEquivOfCardThree Deleted hcard p
  exact additionalBoundaryOfEquiv e (augmentedBoundary σ)

set_option linter.unusedSectionVars false in
theorem augmentedEdge_irrefl {K : Set ι}
    (x : Option (DeletedLabel K)) :
    ¬ augmentedEdge σ x x := by
  cases x with
  | none => simp [augmentedEdge]
  | some x =>
      change ¬ HasIrreducibleMorphism (σ.obj x.1) (σ.obj x.1)
      exact σ.hasNoIrreducibleEndomorphism_obj x.1

theorem augmentedCode_edge_iff
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ))
    (x y : Option (DeletedLabel ((Deleted : Set ι)ᶜ))) :
    edge (augmentedCode (σ := σ) AR Deleted hcard p)
        (labelEquivOfCardThree Deleted hcard p x)
        (labelEquivOfCardThree Deleted hcard p y) = true ↔
      augmentedEdgeBool (σ := σ) x y = true := by
  classical
  apply edge_codeOfEquiv
  intro z
  rw [augmentedEdgeBool_eq_true_iff (σ := σ)]
  exact augmentedEdge_irrefl σ z

theorem augmentedCode_tauEq_iff
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ))
    (hp : Projective (σ.obj p.1))
    (x y : Option (DeletedLabel ((Deleted : Set ι)ᶜ))) :
    tauEq (augmentedCode (σ := σ) AR Deleted hcard p)
        (labelEquivOfCardThree Deleted hcard p x)
        (labelEquivOfCardThree Deleted hcard p y) = true ↔
      augmentedTauTarget σ AR x = some y := by
  classical
  apply tauEq_codeOfEquiv
  have hsymm :
      (labelEquivOfCardThree Deleted hcard p).symm 0 = some p := by
    apply (labelEquivOfCardThree Deleted hcard p).injective
    simp
  rw [hsymm]
  simp [augmentedTauTarget, factorLadderTauTarget, hp]

theorem augmentedCode_tauNone_iff
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ))
    (hp : Projective (σ.obj p.1))
    (x : Option (DeletedLabel ((Deleted : Set ι)ᶜ))) :
    tauNone (augmentedCode (σ := σ) AR Deleted hcard p)
        (labelEquivOfCardThree Deleted hcard p x) = true ↔
      augmentedTauTarget σ AR x = none := by
  classical
  apply tauNone_codeOfEquiv
  have hsymm :
      (labelEquivOfCardThree Deleted hcard p).symm 0 = some p := by
    apply (labelEquivOfCardThree Deleted hcard p).injective
    simp
  rw [hsymm]
  simp [augmentedTauTarget, factorLadderTauTarget, hp]

theorem augmentedBoundaryCode_iff
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ))
    (hp : Projective (σ.obj p.1))
    (x : Option (DeletedLabel ((Deleted : Set ι)ᶜ))) :
    boundaryAt (augmentedBoundaryCode (σ := σ) Deleted hcard p)
        (labelEquivOfCardThree Deleted hcard p x) = true ↔
      augmentedBoundary σ x := by
  classical
  apply boundaryAt_additionalBoundaryOfEquiv
  have hsymm :
      (labelEquivOfCardThree Deleted hcard p).symm 0 = some p := by
    apply (labelEquivOfCardThree Deleted hcard p).injective
    simp
  rw [hsymm]
  exact hp

set_option linter.unusedSectionVars false in
theorem middleMultiplicity_eq_edgeIndicator
    {K : Set ι}
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ K)
    (x y : DeletedLabel K) :
    deletedMiddleMultiplicity (σ := σ) (D := AR) K x y =
      if augmentedEdgeBool (σ := σ) (some y) (some x) then 1 else 0 := by
  classical
  by_cases h : HasIrreducibleMorphism (σ.obj y.1) (σ.obj x.1)
  · simpa [augmentedEdgeBool, augmentedEdge, h] using hunit x y h
  · have hnotpos : ¬ 0 <
        deletedMiddleMultiplicity (σ := σ) (D := AR) K x y :=
      (AR.deletedMiddleMultiplicity_pos_iff_irreducible σ K x y).not.mpr h
    have hnonneg := AR.deletedMiddleMultiplicity_nonneg σ K x y
    have hz : deletedMiddleMultiplicity (σ := σ) (D := AR) K x y = 0 := by
      omega
    simp [augmentedEdgeBool, augmentedEdge, h, hz]

theorem augmentedFactorLadderRelabeling
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ))
    (hp : Projective (σ.obj p.1))
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ
      ((Deleted : Set ι)ᶜ)) :
    Data.Relabeling
      (optionAugmentation
        (AR.factorLadderData σ ((Deleted : Set ι)ᶜ)))
      (FiniteARTranslationData.NormalizedFour.codeFactorLadderData
        (augmentedCode (σ := σ) AR Deleted hcard p))
      (labelEquivOfCardThree Deleted hcard p) where
  theta v := by
    classical
    letI : ∀ a : ι, Decidable (a ∈ ((Deleted : Set ι)ᶜ)) :=
      fun _ => Classical.propDecidable _
    letI : Fintype (DeletedLabel ((Deleted : Set ι)ᶜ)) :=
      Subtype.fintype _
    let e := labelEquivOfCardThree Deleted hcard p
    let C := augmentedCode (σ := σ) AR Deleted hcard p
    funext y
    obtain ⟨y, rfl⟩ := e.surjective y
    dsimp only [e, C]
    simp only [Data.reindex_apply,
      FiniteARTranslationData.NormalizedFour.codeFactorLadderData,
      QuotientSubmoduleEquidistribution.FactorLadder.matrixAddHom_apply]
    rw [Equiv.symm_apply_apply]
    change optionExtendAddHom
        (AR.factorLadderData σ ((Deleted : Set ι)ᶜ)).theta v y = _
    rw [AR.factorLadderData_theta]
    calc
      _ = ∑ x : Option (DeletedLabel ((Deleted : Set ι)ᶜ)),
          v x * if augmentedEdgeBool (σ := σ) y x then 1 else 0 := by
        cases y with
        | none =>
            change 0 = _
            simp [augmentedEdgeBool,
              augmentedEdge]
        | some y =>
            change factorLadderTheta (σ := σ) (D := AR)
              ((Deleted : Set ι)ᶜ) (fun x => v (some x)) y = _
            simp only [factorLadderTheta,
              QuotientSubmoduleEquidistribution.FactorLadder.matrixAddHom_apply]
            simp only [Fintype.sum_option, augmentedEdgeBool,
              augmentedEdge, Bool.false_eq_true, if_false, mul_zero,
              zero_add]
            simp_rw [middleMultiplicity_eq_edgeIndicator σ AR hunit]
            simp [augmentedEdgeBool, augmentedEdge]
      _ = ∑ x : Vertex,
          v (e.symm x) *
            if edge C (e y) x = true then 1 else 0 := by
        apply Fintype.sum_equiv e
        intro x
        have hiff := augmentedCode_edge_iff
          (σ := σ) AR Deleted hcard p y x
        by_cases h : augmentedEdgeBool (σ := σ) y x = true
        · have hc := hiff.mpr h
          have hc' : edge C (e y) (e x) = true := by
            simpa [C, e] using hc
          rw [if_pos h, if_pos hc']
          simp
        · have hc : edge C (e y) (e x) ≠ true :=
            fun hc => h (hiff.mp (by simpa [C, e] using hc))
          rw [if_neg h, if_neg hc]
          simp

  tau v := by
    classical
    letI : ∀ a : ι, Decidable (a ∈ ((Deleted : Set ι)ᶜ)) :=
      fun _ => Classical.propDecidable _
    letI : Fintype (DeletedLabel ((Deleted : Set ι)ᶜ)) :=
      Subtype.fintype _
    let e := labelEquivOfCardThree Deleted hcard p
    let C := augmentedCode (σ := σ) AR Deleted hcard p
    funext y
    obtain ⟨y, rfl⟩ := e.surjective y
    dsimp only [e, C]
    simp only [Data.reindex_apply,
      FiniteARTranslationData.NormalizedFour.codeFactorLadderData,
      QuotientSubmoduleEquidistribution.FactorLadder.matrixAddHom_apply]
    rw [Equiv.symm_apply_apply]
    change optionExtendAddHom
        (AR.factorLadderData σ ((Deleted : Set ι)ᶜ)).tau v y = _
    rw [AR.factorLadderData_tau]
    calc
      _ = ∑ x : Option (DeletedLabel ((Deleted : Set ι)ᶜ)),
          v x * if augmentedTauTarget σ AR x = some y then 1 else 0 := by
        cases y with
        | none =>
            change 0 = _
            simp [Fintype.sum_option, augmentedTauTarget]
        | some y =>
            change factorLadderTau (σ := σ) (D := AR)
              ((Deleted : Set ι)ᶜ) (fun x => v (some x)) y = _
            simp only [factorLadderTau,
              QuotientSubmoduleEquidistribution.FactorLadder.matrixAddHom_apply]
            simp [Fintype.sum_option, augmentedTauTarget,
              factorLadderTauEntry]
      _ = ∑ x : Vertex,
          v (e.symm x) *
            if tauEq C x (e y) = true then 1 else 0 := by
        apply Fintype.sum_equiv e
        intro x
        have hiff := augmentedCode_tauEq_iff
          (σ := σ) AR Deleted hcard p hp x y
        by_cases h : augmentedTauTarget σ AR x = some y
        · have hc := hiff.mpr h
          have hc' : tauEq C (e x) (e y) = true := by
            simpa [C, e] using hc
          rw [if_pos h, if_pos hc']
          simp
        · have hc : tauEq C (e x) (e y) ≠ true :=
            fun hc => h (hiff.mp (by simpa [C, e] using hc))
          rw [if_neg h, if_neg hc]
          simp

theorem augmentedFactorLadder_coefficient_eq_of_code_eq
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ))
    (hp : Projective (σ.obj p.1))
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ
      ((Deleted : Set ι)ᶜ))
    (x : DeletedLabel ((Deleted : Set ι)ᶜ))
    (y : Option (DeletedLabel ((Deleted : Set ι)ᶜ)))
    (n : ℕ) (v : NatVector)
    (hcode :
      (FiniteARTranslationData.NormalizedFour.codeFactorLadderData
        (augmentedCode (σ := σ) AR Deleted hcard p)).ladder
          (labelEquivOfCardThree Deleted hcard p (some x)) n =
        FiniteARTranslationData.NormalizedFour.natCastVector v) :
    (optionAugmentation
      (AR.factorLadderData σ ((Deleted : Set ι)ᶜ))).ladder
        (some x) n y =
      (v (labelEquivOfCardThree Deleted hcard p y) : ℤ) := by
  have hrelabel := augmentedFactorLadderRelabeling
    σ AR Deleted hcard p hp hunit
  have h := congrFun (hrelabel.reindex_ladder (some x) n)
    (labelEquivOfCardThree Deleted hcard p y)
  rw [hcode] at h
  simpa [Data.reindex_apply,
    FiniteARTranslationData.NormalizedFour.natCastVector] using h

theorem factorLadder_coefficient_eq_of_code_eq
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ))
    (hp : Projective (σ.obj p.1))
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ
      ((Deleted : Set ι)ᶜ))
    (x y : DeletedLabel ((Deleted : Set ι)ᶜ))
    (n : ℕ) (v : NatVector)
    (hcode :
      (FiniteARTranslationData.NormalizedFour.codeFactorLadderData
        (augmentedCode (σ := σ) AR Deleted hcard p)).ladder
          (labelEquivOfCardThree Deleted hcard p (some x)) n =
        FiniteARTranslationData.NormalizedFour.natCastVector v) :
    (AR.factorLadderData σ ((Deleted : Set ι)ᶜ)).ladder x n y =
      (v (labelEquivOfCardThree Deleted hcard p (some y)) : ℤ) := by
  have h := augmentedFactorLadder_coefficient_eq_of_code_eq
    σ AR Deleted hcard p hp hunit x (some y) n v hcode
  rw [optionAugmentation_ladder] at h
  exact h

private theorem exists_apply_ne_of_ne
    {α β : Type*} {f g : α → β} (h : f ≠ g) :
    ∃ x, f x ≠ g x := by
  by_contra hall
  push Not at hall
  exact h (funext hall)

set_option linter.unusedSectionVars false in
theorem augmentedTauTarget_some_injective
    {K : Set ι}
    {x₁ x₂ y : Option (DeletedLabel K)}
    (h₁ : augmentedTauTarget σ AR x₁ = some y)
    (h₂ : augmentedTauTarget σ AR x₂ = some y) : x₁ = x₂ := by
  cases x₁ with
  | none => simp [augmentedTauTarget] at h₁
  | some x₁ =>
      cases x₂ with
      | none => simp [augmentedTauTarget] at h₂
      | some x₂ =>
          cases y with
          | none => simp [augmentedTauTarget] at h₁
          | some y =>
              simp only [augmentedTauTarget, Option.map_eq_some_iff,
                Option.some.injEq, exists_eq_right] at h₁ h₂
              exact congrArg some
                (AR.factorLadderTauTarget_some_injective σ K h₁ h₂)

set_option linter.unusedSectionVars false in
theorem data_of_factorLadderTauTarget_eq_some
    {K : Set ι} {x y : DeletedLabel K}
    (h : factorLadderTauTarget (σ := σ) (D := AR) K x = some y) :
    ∃ hx : ¬ Projective (σ.obj x.1),
      (AR.arTranslation σ ⟨x.1, hx⟩).1 = y.1 := by
  classical
  by_cases hx : Projective (σ.obj x.1)
  · simp [factorLadderTauTarget, hx] at h
  · refine ⟨hx, ?_⟩
    by_cases hm : (AR.arTranslation σ ⟨x.1, hx⟩).1 ∈ K
    · simp [factorLadderTauTarget, hx, hm] at h
    · by_cases ht : factorLadderTheta (σ := σ) (D := AR) K
          (FactorLadder.basis x) = 0
      · simp [factorLadderTauTarget, hx, hm, ht] at h
      · have hs := h
        simp [factorLadderTauTarget, hx, hm, ht] at hs
        exact congrArg Subtype.val hs

set_option linter.unusedSectionVars false in
theorem factorLadderTauTarget_eq_some_self_of_fixed
    {K : Set ι} (x y : DeletedLabel K)
    (hx : ¬ Projective (σ.obj x.1))
    (hfix : (AR.arTranslation σ ⟨x.1, hx⟩).1 = x.1)
    (hyx : HasIrreducibleMorphism (σ.obj y.1) (σ.obj x.1)) :
    factorLadderTauTarget (σ := σ) (D := AR) K x = some x := by
  classical
  have hm : (AR.arTranslation σ ⟨x.1, hx⟩).1 ∉ K := by
    rw [hfix]
    exact x.2
  have ht : factorLadderTheta (σ := σ) (D := AR) K
      (FactorLadder.basis x) ≠ 0 := by
    intro hz
    have hc := congrFun hz y
    rw [AR.factorLadderTheta_basis_apply σ K x y, Pi.zero_apply] at hc
    have hpos :=
      (AR.deletedMiddleMultiplicity_pos_iff_irreducible σ K x y).2 hyx
    omega
  simp [factorLadderTauTarget, hx, ht, hfix, x.2]

set_option linter.unusedSectionVars false in
include k in
theorem augmentedBoundaryAxiomConditions
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ))
    (hp : Projective (σ.obj p.1))
    (hroot : ∀ x : DeletedLabel ((Deleted : Set ι)ᶜ),
      ∃ p : DeletedLabel ((Deleted : Set ι)ᶜ),
        Projective (σ.obj p.1) ∧
          Relation.ReflTransGen
            (fun a b : DeletedLabel ((Deleted : Set ι)ᶜ) ↦
              HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x) :
    BoundaryAxiomConditions
      (augmentedCode (σ := σ) AR Deleted hcard p)
      (augmentedBoundaryCode (σ := σ) Deleted hcard p) := by
  classical
  let e := labelEquivOfCardThree Deleted hcard p
  let C := augmentedCode (σ := σ) AR Deleted hcard p
  let B := augmentedBoundaryCode (σ := σ) Deleted hcard p
  refine
    { rooted := ?_
      boundary_no_tau := ?_
      tau_valid := ?_
      tau_injective := ?_
      mesh_incidence := ?_
      two_cycle_fixed := ?_
      translated_boundary_no_two_cycle := ?_ }
  · intro x
    let x' := e.symm x
    cases hx' : x' with
    | none =>
        refine ⟨e none, ?_, ?_⟩
        · apply (augmentedBoundaryCode_iff
            (σ := σ) Deleted hcard p hp none).2
          trivial
        · have hx : e none = x := by
            rw [← hx']
            exact e.apply_symm_apply x
          simpa [hx] using
            (Relation.ReflTransGen.refl :
              Relation.ReflTransGen (fun a b : Vertex ↦ edge C a b = true)
                (e none) (e none))
    | some x₀ =>
        rcases hroot x₀ with ⟨q, hqP, hqx⟩
        refine ⟨e (some q), ?_, ?_⟩
        · apply (augmentedBoundaryCode_iff
            (σ := σ) Deleted hcard p hp (some q)).2
          exact hqP
        · have hlift : Relation.ReflTransGen
              (fun a b : Vertex ↦ edge C a b = true)
              (e (some q)) (e (some x₀)) :=
            hqx.lift (fun z => e (some z)) (by
              intro a b hab
              apply (augmentedCode_edge_iff
                (σ := σ) AR Deleted hcard p (some a) (some b)).2
              simp [augmentedEdgeBool, augmentedEdge, hab])
          have hx : e (some x₀) = x := by
            rw [← hx']
            exact e.apply_symm_apply x
          simpa [C, e, hx] using hlift
  · intro x hx
    let x' := e.symm x
    have hboundary : augmentedBoundary σ x' :=
      (augmentedBoundaryCode_iff
        (σ := σ) Deleted hcard p hp x').1 (by
          simpa [B, e, x'] using hx)
    have hnone : augmentedTauTarget σ AR x' = none := by
      cases hx' : x' with
      | none => simp [augmentedTauTarget]
      | some x₀ =>
          have hxP : Projective (σ.obj x₀.1) := by
            simpa [augmentedBoundary, hx'] using hboundary
          simp [augmentedTauTarget, factorLadderTauTarget, hxP]
    have hout := (augmentedCode_tauNone_iff
      (σ := σ) AR Deleted hcard p hp x').2 hnone
    simpa [e, x'] using hout
  · intro x
    let x' := e.symm x
    cases ht : augmentedTauTarget σ AR x' with
    | none =>
        left
        have hout := (augmentedCode_tauNone_iff
          (σ := σ) AR Deleted hcard p hp x').2 ht
        simpa [e, x'] using hout
    | some y =>
        right
        refine ⟨e y, ?_⟩
        have hout := (augmentedCode_tauEq_iff
          (σ := σ) AR Deleted hcard p hp x' y).2 ht
        simpa [e, x'] using hout
  · intro x y
    let x' := e.symm x
    let y' := e.symm y
    cases hx : augmentedTauTarget σ AR x' with
    | none =>
        left
        have hout := (augmentedCode_tauNone_iff
          (σ := σ) AR Deleted hcard p hp x').2 hx
        simpa [e, x'] using hout
    | some tx =>
        cases hy : augmentedTauTarget σ AR y' with
        | none =>
            right
            left
            have hout := (augmentedCode_tauNone_iff
              (σ := σ) AR Deleted hcard p hp y').2 hy
            simpa [e, y'] using hout
        | some ty =>
            by_cases hcode : tauCode C x ≠ tauCode C y
            · exact Or.inr (Or.inr (Or.inl hcode))
            · right
              right
              right
              have hxt : tauEq C x (e tx) = true := by
                have hout := (augmentedCode_tauEq_iff
                  (σ := σ) AR Deleted hcard p hp x' tx).2 hx
                simpa [C, e, x'] using hout
              have hyt : tauEq C y (e tx) = true := by
                rw [tauEq] at hxt ⊢
                rw [← not_ne_iff.mp hcode]
                exact hxt
              have hyt' : augmentedTauTarget σ AR y' = some tx :=
                (augmentedCode_tauEq_iff
                  (σ := σ) AR Deleted hcard p hp y' tx).1
                    (by simpa [C, e, y'] using hyt)
              have hxy' : x' = y' :=
                augmentedTauTarget_some_injective σ AR hx hyt'
              calc
                x = e x' := (e.apply_symm_apply x).symm
                _ = e y' := congrArg e hxy'
                _ = y := e.apply_symm_apply y
  · intro y t x ht
    let y' := e.symm y
    let t' := e.symm t
    let x' := e.symm x
    have hyE : e y' = y := e.apply_symm_apply y
    have htE : e t' = t := e.apply_symm_apply t
    have hxE : e x' = x := e.apply_symm_apply x
    have htarget : augmentedTauTarget σ AR y' = some t' :=
      (augmentedCode_tauEq_iff
        (σ := σ) AR Deleted hcard p hp y' t').1
          (by simpa [e, y', t'] using ht)
    cases hy' : y' with
    | none => simp [augmentedTauTarget, hy'] at htarget
    | some y₀ =>
        have hy0 : labelEquivOfCardThree Deleted hcard p (some y₀) = y := by
          simpa [e, hy'] using hyE
        cases ht' : t' with
        | none => simp [augmentedTauTarget, hy', ht'] at htarget
        | some t₀ =>
            have ht0 : labelEquivOfCardThree Deleted hcard p (some t₀) = t := by
              simpa [e, ht'] using htE
            simp only [augmentedTauTarget, hy', ht',
              Option.map_eq_some_iff, Option.some.injEq,
              exists_eq_right] at htarget
            cases hx' : x' with
            | none =>
                have hx0 : labelEquivOfCardThree Deleted hcard p none = x := by
                  simpa [e, hx'] using hxE
                constructor <;> intro h
                · have := (augmentedCode_edge_iff
                    (σ := σ) AR Deleted hcard p none (some y₀)).1
                      (by simpa [hx0, hy0] using h)
                  simp [augmentedEdgeBool, augmentedEdge] at this
                · have := (augmentedCode_edge_iff
                    (σ := σ) AR Deleted hcard p (some t₀) none).1
                      (by simpa [ht0, hx0] using h)
                  simp [augmentedEdgeBool, augmentedEdge] at this
            | some x₀ =>
                have hx0 : labelEquivOfCardThree Deleted hcard p (some x₀) = x := by
                  simpa [e, hx'] using hxE
                obtain ⟨hyNP, htranslate⟩ :=
                  data_of_factorLadderTauTarget_eq_some σ AR htarget
                have hinc := AR.arTranslation_incidence σ
                  ⟨y₀.1, hyNP⟩ x₀.1
                rw [htranslate] at hinc
                constructor
                · intro hxy
                  have hedge : augmentedEdgeBool (σ := σ)
                      (some t₀) (some x₀) = true :=
                    (augmentedEdgeBool_eq_true_iff (σ := σ) _ _).2 (hinc.mp
                    ((augmentedEdgeBool_eq_true_iff (σ := σ) _ _).1
                      ((augmentedCode_edge_iff
                        (σ := σ) AR Deleted hcard p
                          (some x₀) (some y₀)).1
                            (by simpa [hx0, hy0] using hxy))))
                  have hout := (augmentedCode_edge_iff
                    (σ := σ) AR Deleted hcard p
                      (some t₀) (some x₀)).2 hedge
                  simpa [ht0, hx0] using hout
                · intro htx
                  have hedge : augmentedEdgeBool (σ := σ)
                      (some x₀) (some y₀) = true :=
                    (augmentedEdgeBool_eq_true_iff (σ := σ) _ _).2 (hinc.mpr
                    ((augmentedEdgeBool_eq_true_iff (σ := σ) _ _).1
                      ((augmentedCode_edge_iff
                        (σ := σ) AR Deleted hcard p
                          (some t₀) (some x₀)).1
                            (by simpa [ht0, hx0] using htx))))
                  have hout := (augmentedCode_edge_iff
                    (σ := σ) AR Deleted hcard p
                      (some x₀) (some y₀)).2 hedge
                  simpa [hx0, hy0] using hout
  · intro x y hxy hyx
    let x' := e.symm x
    let y' := e.symm y
    have hxy' := (augmentedCode_edge_iff
      (σ := σ) AR Deleted hcard p x' y').1
        (by simpa [e, x', y'] using hxy)
    have hyx' := (augmentedCode_edge_iff
      (σ := σ) AR Deleted hcard p y' x').1
        (by simpa [e, x', y'] using hyx)
    cases hx' : x' with
    | none => simp [augmentedEdgeBool, augmentedEdge, hx'] at hxy'
    | some x₀ =>
        cases hy' : y' with
        | none => simp [augmentedEdgeBool, augmentedEdge, hy'] at hxy'
        | some y₀ =>
            have hxyA : HasIrreducibleMorphism
                (σ.obj x₀.1) (σ.obj y₀.1) := by
              simpa [augmentedEdgeBool, augmentedEdge, hx', hy'] using hxy'
            have hyxA : HasIrreducibleMorphism
                (σ.obj y₀.1) (σ.obj x₀.1) := by
              simpa [augmentedEdgeBool, augmentedEdge, hx', hy'] using hyx'
            rcases AR.exists_arTranslation_eq_self_of_two_cycle
                (K := k) σ x₀.1 y₀.1 hxyA hyxA with
              ⟨hxNP, hxfix⟩ | ⟨hyNP, hyfix⟩
            · left
              have htarget : augmentedTauTarget σ AR x' = some x' := by
                simpa [augmentedTauTarget, hx'] using
                  congrArg (Option.map some)
                    (factorLadderTauTarget_eq_some_self_of_fixed
                      σ AR x₀ y₀ hxNP hxfix hyxA)
              have hout := (augmentedCode_tauEq_iff
                (σ := σ) AR Deleted hcard p hp x' x').2 htarget
              simpa [e, x'] using hout
            · right
              have htarget : augmentedTauTarget σ AR y' = some y' := by
                simpa [augmentedTauTarget, hy'] using
                  congrArg (Option.map some)
                    (factorLadderTauTarget_eq_some_self_of_fixed
                      σ AR y₀ x₀ hyNP hyfix hxyA)
              have hout := (augmentedCode_tauEq_iff
                (σ := σ) AR Deleted hcard p hp y' y').2 htarget
              simpa [e, y'] using hout
  · intro q hq ⟨b, hbq⟩ z
    by_cases hqz : edge C q z = true
    · by_cases hzq : edge C z q = true
      · exfalso
        let q' := e.symm q
        let b' := e.symm b
        let z' := e.symm z
        have hqB : augmentedBoundary σ q' :=
          (augmentedBoundaryCode_iff
            (σ := σ) Deleted hcard p hp q').1
              (by simpa [e, q'] using hq)
        have hbq' : augmentedTauTarget σ AR b' = some q' :=
          (augmentedCode_tauEq_iff
            (σ := σ) AR Deleted hcard p hp b' q').1
              (by simpa [e, b', q'] using hbq)
        have hqz' := (augmentedCode_edge_iff
          (σ := σ) AR Deleted hcard p q' z').1
            (by simpa [C, e, q', z'] using hqz)
        have hzq' := (augmentedCode_edge_iff
          (σ := σ) AR Deleted hcard p z' q').1
            (by simpa [C, e, q', z'] using hzq)
        cases hb' : b' with
        | none => simp [augmentedTauTarget, hb'] at hbq'
        | some b₀ =>
            cases hq' : q' with
            | none => simp [augmentedTauTarget, hb', hq'] at hbq'
            | some q₀ =>
                cases hz' : z' with
                | none =>
                    simp [augmentedEdgeBool, augmentedEdge, hz'] at hqz'
                | some z₀ =>
                    have hqP : Projective (σ.obj q₀.1) := by
                      simpa [augmentedBoundary, hq'] using hqB
                    simp only [augmentedTauTarget, hb', hq',
                      Option.map_eq_some_iff, Option.some.injEq,
                      exists_eq_right] at hbq'
                    obtain ⟨hbNP, htranslate⟩ :=
                      data_of_factorLadderTauTarget_eq_some σ AR hbq'
                    have hqzA : HasIrreducibleMorphism
                        (σ.obj q₀.1) (σ.obj z₀.1) := by
                      simpa [augmentedEdgeBool, augmentedEdge, hq', hz']
                        using hqz'
                    have hzqA : HasIrreducibleMorphism
                        (σ.obj z₀.1) (σ.obj q₀.1) := by
                      simpa [augmentedEdgeBool, augmentedEdge, hq', hz']
                        using hzq'
                    have hqI : Injective (σ.obj q₀.1) :=
                      AR.injective_of_projective_two_cycle
                        (K := k) σ q₀.1 z₀.1 hqP hqzA hzqA
                    exact (AR.arTranslation σ ⟨b₀.1, hbNP⟩).2
                      (by simpa [htranslate] using hqI)
      · exact Or.inr (Bool.eq_false_of_not_eq_true hzq)
    · exact Or.inl (Bool.eq_false_of_not_eq_true hqz)

theorem augmentedBoundaryWitnessConditions_of_fourStep
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ))
    (hp : Projective (σ.obj p.1))
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ
      ((Deleted : Set ι)ᶜ))
    (x : DeletedLabel ((Deleted : Set ι)ᶜ))
    (H : (AR.factorLadderData σ ((Deleted : Set ι)ᶜ)).FourStepAvoidingCertificate
        (deletedProjectiveSet σ ((Deleted : Set ι)ᶜ)) x) :
    BoundaryWitnessConditions
      (augmentedCode (σ := σ) AR Deleted hcard p)
      (augmentedBoundaryCode (σ := σ) Deleted hcard p)
      (labelEquivOfCardThree Deleted hcard p (some x)) := by
  classical
  let e := labelEquivOfCardThree Deleted hcard p
  let C := augmentedCode (σ := σ) AR Deleted hcard p
  let B := augmentedBoundaryCode (σ := σ) Deleted hcard p
  have hstart : boundaryAt B (e (some x)) = false := by
    have hxNP : ¬ Projective (σ.obj x.1) := by
      intro hxP
      apply H.start_not_mem
      simpa [deletedProjectiveSet] using hxP
    cases hb : boundaryAt B (e (some x))
    · rfl
    · have hboundary := (augmentedBoundaryCode_iff
        (σ := σ) Deleted hcard p hp (some x)).1 (by
          simpa [B, e] using hb)
      exact (hxNP (by simpa [augmentedBoundary] using hboundary)).elim
  have zeroOfBoundary : ∀ (n : ℕ) (v : NatVector),
      (FiniteARTranslationData.NormalizedFour.codeFactorLadderData C).ladder
          (e (some x)) n =
        FiniteARTranslationData.NormalizedFour.natCastVector v →
      n ≤ 4 → ∀ q, boundaryAt B q = true → v q = 0 := by
    intro n v hcode hn q hq
    let q' := e.symm q
    have hqB : augmentedBoundary σ q' :=
      (augmentedBoundaryCode_iff
        (σ := σ) Deleted hcard p hp q').1 (by
          simpa [B, e, q'] using hq)
    have hcoeff := augmentedFactorLadder_coefficient_eq_of_code_eq
      σ AR Deleted hcard p hp hunit x q' n v (by
        simpa [C, e] using hcode)
    have heq : e q' = q := e.apply_symm_apply q
    cases hq' : q' with
    | none =>
        have heq0 : labelEquivOfCardThree Deleted hcard p none = q := by
          simpa [e, hq'] using heq
        rw [optionAugmentation_ladder] at hcoeff
        have hz : (0 : ℤ) = (v q : ℤ) := by
          simpa [optionExtendVector, hq', heq0] using hcoeff
        exact_mod_cast hz.symm
    | some q₀ =>
        have heq0 : labelEquivOfCardThree Deleted hcard p (some q₀) = q := by
          simpa [e, hq'] using heq
        have hqP : Projective (σ.obj q₀.1) := by
          simpa [augmentedBoundary, hq'] using hqB
        have hqMem : q₀ ∈
            deletedProjectiveSet σ ((Deleted : Set ι)ᶜ) := by
          simpa [deletedProjectiveSet] using hqP
        have hz := H.boundary_zero_through_four n hn q₀ hqMem
        rw [optionAugmentation_ladder] at hcoeff
        simp only [hq', optionExtendVector] at hcoeff
        have hz' : (0 : ℤ) = (v q : ℤ) := by
          rw [hz] at hcoeff
          simpa [optionExtendVector, hq', heq0] using hcoeff
        exact_mod_cast hz'.symm
  refine
    { start_not_boundary := hstart
      boundary_zero_zero := ?_
      boundary_zero_one := ?_
      boundary_zero_two := ?_
      boundary_zero_three := ?_
      boundary_zero_four := ?_
      pair_zero_two := ?_
      pair_zero_three := ?_ }
  · intro q hq
    rw [ladderCoefficientZero_eq_natural]
    exact zeroOfBoundary 0 (naturalLadderZero (e (some x)))
      (by
        exact
          (FiniteARTranslationData.NormalizedFour.codeFactorLadderData_ladder_zero
            C (e (some x)))) (by omega) q (by simpa [B] using hq)
  · intro q hq
    rw [ladderCoefficientOne_eq_natural]
    exact zeroOfBoundary 1 (naturalLadderOne C (e (some x)))
      (by exact
        (FiniteARTranslationData.NormalizedFour.codeFactorLadderData_ladder_one
          C (e (some x)))) (by omega) q (by simpa [B] using hq)
  · intro q hq
    rw [ladderCoefficientTwo_eq_natural]
    exact zeroOfBoundary 2 (naturalLadderTwo C (e (some x)))
      (by exact
        (FiniteARTranslationData.NormalizedFour.codeFactorLadderData_ladder_two
          C (e (some x)))) (by omega) q (by simpa [B] using hq)
  · intro q hq
    rw [ladderCoefficientThree_eq_natural]
    exact zeroOfBoundary 3 (naturalLadderThree C (e (some x)))
      (by exact
        (FiniteARTranslationData.NormalizedFour.codeFactorLadderData_ladder_three
          C (e (some x)))) (by omega) q (by simpa [B] using hq)
  · intro q hq
    rw [ladderCoefficientFour_eq_natural]
    exact zeroOfBoundary 4 (naturalLadderFour C (e (some x)))
      (by exact
        (FiniteARTranslationData.NormalizedFour.codeFactorLadderData_ladder_four
          C (e (some x)))) (by omega) q (by simpa [B] using hq)
  · rcases H.pair_zero_two with h02 | h13
    · left
      rcases exists_apply_ne_of_ne h02 with ⟨y, hy⟩
      refine ⟨e (some y), ?_⟩
      rw [ladderCoefficientZero_eq_natural,
        ladderCoefficientTwo_eq_natural]
      intro hnat
      apply hy
      have h0 := factorLadder_coefficient_eq_of_code_eq
        σ AR Deleted hcard p hp hunit x y 0
          (naturalLadderZero (e (some x)))
          (by exact
            (FiniteARTranslationData.NormalizedFour.codeFactorLadderData_ladder_zero
              C (e (some x))))
      have h2 := factorLadder_coefficient_eq_of_code_eq
        σ AR Deleted hcard p hp hunit x y 2
          (naturalLadderTwo C (e (some x)))
          (by exact
            (FiniteARTranslationData.NormalizedFour.codeFactorLadderData_ladder_two
              C (e (some x))))
      exact h0.trans ((congrArg (fun n : ℕ => (n : ℤ))
        (by simpa [e] using hnat)).trans h2.symm)
    · right
      rcases exists_apply_ne_of_ne h13 with ⟨y, hy⟩
      refine ⟨e (some y), ?_⟩
      rw [ladderCoefficientOne_eq_natural,
        ladderCoefficientThree_eq_natural]
      intro hnat
      apply hy
      have h1 := factorLadder_coefficient_eq_of_code_eq
        σ AR Deleted hcard p hp hunit x y 1
          (naturalLadderOne C (e (some x)))
          (by exact
            (FiniteARTranslationData.NormalizedFour.codeFactorLadderData_ladder_one
              C (e (some x))))
      have h3 := factorLadder_coefficient_eq_of_code_eq
        σ AR Deleted hcard p hp hunit x y 3
          (naturalLadderThree C (e (some x)))
          (by exact
            (FiniteARTranslationData.NormalizedFour.codeFactorLadderData_ladder_three
              C (e (some x))))
      exact h1.trans ((congrArg (fun n : ℕ => (n : ℤ))
        (by simpa [e] using hnat)).trans h3.symm)
  · rcases H.pair_zero_three with h03 | h14
    · left
      rcases exists_apply_ne_of_ne h03 with ⟨y, hy⟩
      refine ⟨e (some y), ?_⟩
      rw [ladderCoefficientZero_eq_natural,
        ladderCoefficientThree_eq_natural]
      intro hnat
      apply hy
      have h0 := factorLadder_coefficient_eq_of_code_eq
        σ AR Deleted hcard p hp hunit x y 0
          (naturalLadderZero (e (some x)))
          (by exact
            (FiniteARTranslationData.NormalizedFour.codeFactorLadderData_ladder_zero
              C (e (some x))))
      have h3 := factorLadder_coefficient_eq_of_code_eq
        σ AR Deleted hcard p hp hunit x y 3
          (naturalLadderThree C (e (some x)))
          (by exact
            (FiniteARTranslationData.NormalizedFour.codeFactorLadderData_ladder_three
              C (e (some x))))
      exact h0.trans ((congrArg (fun n : ℕ => (n : ℤ))
        (by simpa [e] using hnat)).trans h3.symm)
    · right
      rcases exists_apply_ne_of_ne h14 with ⟨y, hy⟩
      refine ⟨e (some y), ?_⟩
      rw [ladderCoefficientOne_eq_natural,
        ladderCoefficientFour_eq_natural]
      intro hnat
      apply hy
      have h1 := factorLadder_coefficient_eq_of_code_eq
        σ AR Deleted hcard p hp hunit x y 1
          (naturalLadderOne C (e (some x)))
          (by exact
            (FiniteARTranslationData.NormalizedFour.codeFactorLadderData_ladder_one
              C (e (some x))))
      have h4 := factorLadder_coefficient_eq_of_code_eq
        σ AR Deleted hcard p hp hunit x y 4
          (naturalLadderFour C (e (some x)))
          (by exact
            (FiniteARTranslationData.NormalizedFour.codeFactorLadderData_ladder_four
              C (e (some x))))
      exact h1.trans ((congrArg (fun n : ℕ => (n : ℤ))
        (by simpa [e] using hnat)).trans h4.symm)

def admissibleHookOfAugmentedBoundaryHookAt
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ))
    (hp : Projective (σ.obj p.1))
    {a u b : Vertex}
    (h : BoundaryHookAt
      (augmentedCode (σ := σ) AR Deleted hcard p)
      (augmentedBoundaryCode (σ := σ) Deleted hcard p) a u b = true) :
    AR.AdmissibleHook σ ((Deleted : Set ι)ᶜ) := by
  classical
  let e := labelEquivOfCardThree Deleted hcard p
  let C := augmentedCode (σ := σ) AR Deleted hcard p
  let B := augmentedBoundaryCode (σ := σ) Deleted hcard p
  let H := boundaryHookConditions_of_boundaryHookAt h
  let a' := e.symm a
  let u' := e.symm u
  let b' := e.symm b
  have haE : e a' = a := e.apply_symm_apply a
  have huE : e u' = u := e.apply_symm_apply u
  have hbE : e b' = b := e.apply_symm_apply b
  have huNot : ¬ augmentedBoundary σ u' := by
    intro huB
    have htrue := (augmentedBoundaryCode_iff
      (σ := σ) Deleted hcard p hp u').2 huB
    have : boundaryAt B u = true := by simpa [B, e, u'] using htrue
    have hfalse : boundaryAt B u = false := by
      simpa [H, B] using H.u_not_boundary
    rw [hfalse] at this
    contradiction
  have hbNot : ¬ augmentedBoundary σ b' := by
    intro hbB
    have htrue := (augmentedBoundaryCode_iff
      (σ := σ) Deleted hcard p hp b').2 hbB
    have : boundaryAt B b = true := by simpa [B, e, b'] using htrue
    have hfalse : boundaryAt B b = false := by
      simpa [H, B] using H.b_not_boundary
    rw [hfalse] at this
    contradiction
  have huExists : ∃ u₀, u' = some u₀ := by
    cases hu' : u' with
    | none => exact (huNot (by simp [augmentedBoundary, hu'])).elim
    | some u₀ => exact ⟨u₀, rfl⟩
  let u₀ := Classical.choose huExists
  have hu' : u' = some u₀ := Classical.choose_spec huExists
  have hbExists : ∃ b₀, b' = some b₀ := by
    cases hb' : b' with
    | none => exact (hbNot (by simp [augmentedBoundary, hb'])).elim
    | some b₀ => exact ⟨b₀, rfl⟩
  let b₀ := Classical.choose hbExists
  have hb' : b' = some b₀ := Classical.choose_spec hbExists
  have hauCode : edge C a u = true :=
    (edge_eq_true_iff_of_uniquePredecessor H.predecessor_u a).2 rfl
  have hauAug : augmentedEdgeBool (σ := σ) a' u' = true :=
    (augmentedCode_edge_iff
      (σ := σ) AR Deleted hcard p a' u').1 (by
        simpa [C, e, a', u'] using hauCode)
  have haExists : ∃ a₀, a' = some a₀ := by
    cases ha' : a' with
    | none =>
        simp [augmentedEdgeBool, augmentedEdge, ha', hu'] at hauAug
    | some a₀ => exact ⟨a₀, rfl⟩
  let a₀ := Classical.choose haExists
  have ha' : a' = some a₀ := Classical.choose_spec haExists
  have huNP : ¬ Projective (σ.obj u₀.1) := by
    simpa [augmentedBoundary, hu'] using huNot
  have hbNP : ¬ Projective (σ.obj b₀.1) := by
    simpa [augmentedBoundary, hb'] using hbNot
  have htAug : augmentedTauTarget σ AR b' = some a' :=
    (augmentedCode_tauEq_iff
      (σ := σ) AR Deleted hcard p hp b' a').1 (by
        simpa [C, e, a', b'] using H.tau_b)
  have htFactor : factorLadderTauTarget (σ := σ) (D := AR)
      ((Deleted : Set ι)ᶜ) b₀ = some a₀ := by
    simpa [augmentedTauTarget, ha', hb'] using htAug
  have htExists := data_of_factorLadderTauTarget_eq_some σ AR htFactor
  let hbNP' := Classical.choose htExists
  have htau : (AR.arTranslation σ ⟨b₀.1, hbNP'⟩).1 = a₀.1 :=
    Classical.choose_spec htExists
  refine
    { a := a₀
      u := u₀
      b := b₀
      u_nonprojective := huNP
      b_nonprojective := hbNP
      predecessor_u := ?_
      predecessor_b := ?_
      tau_b := by simpa using htau }
  · constructor
    · have hcode := (edge_eq_true_iff_of_uniquePredecessor
        H.predecessor_u a).2 rfl
      have haug := (augmentedCode_edge_iff
        (σ := σ) AR Deleted hcard p a' u').1 (by
          simpa [C, e, a', u'] using hcode)
      simpa [augmentedEdgeBool, augmentedEdge, ha', hu'] using haug
    · intro w hw
      have hwaug : augmentedEdgeBool (σ := σ) (some w) u' = true := by
        simpa [augmentedEdgeBool, augmentedEdge, hu'] using hw
      have hwcode := (augmentedCode_edge_iff
        (σ := σ) AR Deleted hcard p (some w) u').2 hwaug
      have heq := (edge_eq_true_iff_of_uniquePredecessor H.predecessor_u
        (e (some w))).1 (by simpa [C, e, u'] using hwcode)
      have heq' : some w = a' := by
        apply e.injective
        simpa [a'] using heq
      exact Option.some.inj (by simpa [ha'] using heq')
  · constructor
    · have hcode := (edge_eq_true_iff_of_uniquePredecessor
        H.predecessor_b u).2 rfl
      have haug := (augmentedCode_edge_iff
        (σ := σ) AR Deleted hcard p u' b').1 (by
          simpa [C, e, u', b'] using hcode)
      simpa [augmentedEdgeBool, augmentedEdge, hu', hb'] using haug
    · intro w hw
      have hwaug : augmentedEdgeBool (σ := σ) (some w) b' = true := by
        simpa [augmentedEdgeBool, augmentedEdge, hb'] using hw
      have hwcode := (augmentedCode_edge_iff
        (σ := σ) AR Deleted hcard p (some w) b').2 hwaug
      have heq := (edge_eq_true_iff_of_uniquePredecessor H.predecessor_b
        (e (some w))).1 (by simpa [C, e, b'] using hwcode)
      have heq' : some w = u' := by
        apply e.injective
        simpa [u'] using heq
      exact Option.some.inj (by simpa [hu'] using heq')

include k in
theorem nonempty_admissibleHook_of_bad_rooted_three
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (hroot : QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (hbad : QuotientFactorLadderBad (k := k) (R := R) σ Deleted) :
    Nonempty (AR.AdmissibleHook σ ((Deleted : Set ι)ᶜ)) := by
  classical
  let K : Set ι := ((Deleted : Finset ι) : Set ι)ᶜ
  rcases hbad with ⟨x, hnot⟩
  have hroot' : ∀ y : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p y := by
    intro y
    rcases (AR.fourVertexHookData σ Deleted hroot).rooted y with
      ⟨p, hp, hpy⟩
    refine ⟨p, ?_, ?_⟩
    · simpa [K, fourVertexHookData, deletedProjectiveSet] using hp
    · simpa [K, fourVertexHookData] using hpy
  rcases hroot' x with ⟨p, hp, _⟩
  let C := augmentedCode (σ := σ) AR Deleted hcard p
  let B := augmentedBoundaryCode (σ := σ) Deleted hcard p
  let e := labelEquivOfCardThree Deleted hcard p
  have hunit := AR.hasUnitDeletedMiddleMultiplicities_of_isAlgClosed
    (k := k) (R := R) σ K
  have hfour := σ.finiteDimensionalFactorLadder_fourStepAvoidingCertificate
    (k := k) (R := R) K x (by simpa [K] using hnot)
  have hAxioms : BoundaryAxioms C B = true :=
    boundaryAxioms_eq_true_of_conditions
      (augmentedBoundaryAxiomConditions
        (k := k) (σ := σ) AR Deleted hcard p hp hroot')
  have hWitness : BoundaryWitness C B (e (some x)) = true :=
    boundaryWitness_eq_true_of_conditions
      (augmentedBoundaryWitnessConditions_of_fourStep
        (σ := σ) AR Deleted hcard p hp hunit x hfour)
  have hHas : HasBoundaryHook C B = true := by
    by_contra hnotTrue
    have hHookless : HasBoundaryHook C B = false :=
      Bool.eq_false_of_not_eq_true hnotTrue
    have hNo := noAdditionalBoundary_of_axioms_of_hookless_of_witness
      C B (e (some x)) hAxioms hHookless hWitness
    have hDummy : boundaryAt B (e none) = true := by
      apply (augmentedBoundaryCode_iff
        (σ := σ) Deleted hcard p hp none).2
      trivial
    have hDummyZero : e none = 0 :=
      (boundaryAt_eq_true_iff_of_noAdditionalBoundary hNo (e none)).1 hDummy
    have hRootZero : e (some p) = 0 := by
      set_option linter.unnecessarySimpa false in
        simpa [e] using
          labelEquivOfCardThree_apply_distinguished Deleted hcard p
    have : (none : Option (DeletedLabel K)) = some p := by
      apply e.injective
      exact hDummyZero.trans hRootZero.symm
    contradiction
  rcases exists_boundaryHookAt_of_hasBoundaryHook C B hHas with
    ⟨a, u, b, hHook⟩
  exact ⟨admissibleHookOfAugmentedBoundaryHookAt
    (σ := σ) AR Deleted hcard p hp hHook⟩

theorem AdmissibleHook.stripSupport_eq_deleted_of_card_three
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (hroot : QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (H : AR.AdmissibleHook σ ((Deleted : Set ι)ᶜ)) :
    (H.toStripAdmissibleTriple σ AR Deleted hroot).support = Deleted := by
  classical
  let T := H.toStripAdmissibleTriple σ AR Deleted hroot
  change {H.a.1, H.u.1, H.b.1} = Deleted
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · simpa using H.a.2
    · simpa using H.u.2
    · simpa using H.b.2
  · have hT := T.support_card
    change ({H.a.1, H.u.1, H.b.1} : Finset ι).card = 3 at hT
    rw [hT, hcard]

theorem AdmissibleHook.source_projective_of_card_three
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (hroot : QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (H : AR.AdmissibleHook σ ((Deleted : Set ι)ᶜ)) :
    Projective (σ.obj H.a.1) := by
  classical
  let T := H.toStripAdmissibleTriple σ AR Deleted hroot
  rcases (AR.fourVertexHookData σ Deleted hroot).rooted H.a with
    ⟨p, hp, _⟩
  have hpP : Projective (σ.obj p.1) := by
    simpa [fourVertexHookData, deletedProjectiveSet] using hp
  have hpDeleted : p.1 ∈ Deleted := by simpa using p.2
  have hpSupport : p.1 ∈ T.support := by
    rw [AdmissibleHook.stripSupport_eq_deleted_of_card_three
      (σ := σ) AR Deleted hcard hroot H]
    exact hpDeleted
  change p.1 ∈ ({H.a.1, H.u.1, H.b.1} : Finset ι) at hpSupport
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpSupport
  rcases hpSupport with hpa | hpu | hpb
  · simpa [hpa] using hpP
  · exfalso
    apply H.u_nonprojective
    simpa [hpu] using hpP
  · exfalso
    apply H.b_nonprojective
    simpa [hpb] using hpP

theorem admissibleHook_subsingleton_of_rooted_card_three
    (Deleted : Finset ι) (hcard : Deleted.card = 3)
    (hroot : QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted) :
    Subsingleton (AR.AdmissibleHook σ ((Deleted : Set ι)ᶜ)) := by
  classical
  constructor
  intro H₁ H₂
  by_contra hne
  let T₁ := H₁.toStripAdmissibleTriple σ AR Deleted hroot
  let T₂ := H₂.toStripAdmissibleTriple σ AR Deleted hroot
  have hb₂Deleted : H₂.b.1 ∈ Deleted := by simpa using H₂.b.2
  have hb₁Deleted : H₁.b.1 ∈ Deleted := by simpa using H₁.b.2
  rcases H₁.doubleHook_shape_of_ne σ AR Deleted hroot (by omega) hne with
    h₁₂ | h₂₁
  · have hb₂Support : H₂.b.1 ∈ T₁.support := by
      rw [AdmissibleHook.stripSupport_eq_deleted_of_card_three
        (σ := σ) AR Deleted hcard hroot H₁]
      exact hb₂Deleted
    change H₂.b.1 ∈ ({H₁.a.1, H₁.u.1, H₁.b.1} : Finset ι) at hb₂Support
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb₂Support
    rcases hb₂Support with hba | hbu | hbb
    · apply H₂.b_nonprojective
      simpa [hba] using h₁₂.2.1
    · have hneab := T₂.a_ne_b
      change H₂.a.1 ≠ H₂.b.1 at hneab
      apply hneab
      exact congrArg Subtype.val
        (h₁₂.2.2.trans (Subtype.ext hbu.symm))
    · have hneub := T₂.u_ne_b
      change H₂.u.1 ≠ H₂.b.1 at hneub
      apply hneub
      exact congrArg Subtype.val
        (h₁₂.1.symm.trans (Subtype.ext hbb.symm))
  · have hb₁Support : H₁.b.1 ∈ T₂.support := by
      rw [AdmissibleHook.stripSupport_eq_deleted_of_card_three
        (σ := σ) AR Deleted hcard hroot H₂]
      exact hb₁Deleted
    change H₁.b.1 ∈ ({H₂.a.1, H₂.u.1, H₂.b.1} : Finset ι) at hb₁Support
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb₁Support
    rcases hb₁Support with hba | hbu | hbb
    · apply H₁.b_nonprojective
      simpa [hba] using h₂₁.2.1
    · have hneab := T₁.a_ne_b
      change H₁.a.1 ≠ H₁.b.1 at hneab
      apply hneab
      exact congrArg Subtype.val
        (h₂₁.2.2.trans (Subtype.ext hbu.symm))
    · have hneub := T₁.u_ne_b
      change H₁.u.1 ≠ H₁.b.1 at hneub
      apply hneub
      exact congrArg Subtype.val
        (h₂₁.1.symm.trans (Subtype.ext hbb.symm))

def quotientBadRootedThreeFamily : Finset (Finset ι) :=
  QuotientSubmoduleEquidistribution.SetClosure.badRootedDeletions
    (QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset)
    (QuotientFactorLadderBad (k := k) (R := R) σ) 3

abbrev QuotientBadRootedThree : Type v :=
  {Deleted // Deleted ∈ quotientBadRootedThreeFamily
    (k := k) (R := R) σ}

def StripAdmissibleTriple.toAdmissibleHookOnSupport
    (T : AR.StripAdmissibleTriple σ) :
    AR.AdmissibleHook σ ((T.support : Set ι)ᶜ) := by
  classical
  let a : DeletedLabel ((T.support : Set ι)ᶜ) :=
    ⟨T.a, by simp [StripAdmissibleTriple.support]⟩
  let u : DeletedLabel ((T.support : Set ι)ᶜ) :=
    ⟨T.u, by simp [StripAdmissibleTriple.support]⟩
  let b : DeletedLabel ((T.support : Set ι)ᶜ) :=
    ⟨T.b, by simp [StripAdmissibleTriple.support]⟩
  refine
    { a := a
      u := u
      b := b
      u_nonprojective := T.u_nonprojective
      b_nonprojective := T.b_nonprojective
      predecessor_u := ?_
      predecessor_b := ?_
      tau_b := T.tau_b }
  · constructor
    · exact T.a_to_u
    · intro z hz
      have hzSupport : z.1 ∈ T.support := by simpa using z.2
      simp only [StripAdmissibleTriple.support, Finset.mem_insert,
        Finset.mem_singleton] at hzSupport
      rcases hzSupport with hza | hzu | hzb
      · exact Subtype.ext hza
      · exfalso
        apply σ.hasNoIrreducibleEndomorphism_obj T.u
        simpa [hzu] using hz
      · exact (T.b_not_to_u (by simpa [hzb] using hz)).elim
  · constructor
    · exact T.u_to_b
    · intro z hz
      have hzSupport : z.1 ∈ T.support := by simpa using z.2
      simp only [StripAdmissibleTriple.support, Finset.mem_insert,
        Finset.mem_singleton] at hzSupport
      rcases hzSupport with hza | hzu | hzb
      · exact (T.a_not_to_b (by simpa [hza] using hz)).elim
      · exact Subtype.ext hzu
      · exfalso
        apply σ.hasNoIrreducibleEndomorphism_obj T.b
        simpa [hzb] using hz

theorem StripAdmissibleTriple.support_projectivelyRooted
    (T : AR.StripAdmissibleTriple σ)
    (haP : Projective (σ.obj T.a)) :
    QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset T.support := by
  classical
  intro x hx
  change x ∈ ({T.a, T.u, T.b} : Finset ι) at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · refine ⟨T.a, by simpa, by simp, Relation.ReflTransGen.refl⟩
  · refine ⟨T.a, by simpa, by simp, ?_⟩
    exact Relation.ReflTransGen.single ⟨by simp, by simp, T.a_to_u⟩
  · refine ⟨T.a, by simpa, by simp, ?_⟩
    apply Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single ⟨by simp, by simp, T.a_to_u⟩)
    exact ⟨by simp, by simp, T.u_to_b⟩

include k in
theorem quotientBadRootedThree_nonempty_hook
    (D : QuotientBadRootedThree (k := k) (R := R) σ) :
    Nonempty ((σ.finiteDimensionalARTranslationData k R).AdmissibleHook
      σ ((D.1 : Set ι)ᶜ)) := by
  have h : D.1.card = 3 ∧
      QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
        σ.irreducibleEdge σ.projectiveLabelFinset D.1 ∧
      QuotientFactorLadderBad (k := k) (R := R) σ D.1 := by
    simpa only [quotientBadRootedThreeFamily,
      QuotientSubmoduleEquidistribution.SetClosure.mem_badRootedDeletions] using D.2
  exact nonempty_admissibleHook_of_bad_rooted_three
    (k := k) (σ := σ) (σ.finiteDimensionalARTranslationData k R)
      D.1 h.1 h.2.1 h.2.2

noncomputable def quotientBadRootedThreeToProjectiveStrip
    (D : QuotientBadRootedThree (k := k) (R := R) σ) :
    {T : (σ.finiteDimensionalARTranslationData k R).StripAdmissibleTriple σ //
      Projective (σ.obj T.a)} := by
  classical
  have h : D.1.card = 3 ∧
      QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
        σ.irreducibleEdge σ.projectiveLabelFinset D.1 ∧
      QuotientFactorLadderBad (k := k) (R := R) σ D.1 := by
    simpa only [quotientBadRootedThreeFamily,
      QuotientSubmoduleEquidistribution.SetClosure.mem_badRootedDeletions] using D.2
  let H := Classical.choice
    (quotientBadRootedThree_nonempty_hook
      (k := k) (σ := σ) D)
  exact ⟨H.toStripAdmissibleTriple σ
      (σ.finiteDimensionalARTranslationData k R) D.1 h.2.1,
    AdmissibleHook.source_projective_of_card_three
      (σ := σ) (σ.finiteDimensionalARTranslationData k R)
        D.1 h.1 h.2.1 H⟩

noncomputable def projectiveStripToQuotientBadRootedThree
    (T : {T : (σ.finiteDimensionalARTranslationData k R).StripAdmissibleTriple σ //
      Projective (σ.obj T.a)}) :
    QuotientBadRootedThree (k := k) (R := R) σ := by
  classical
  refine ⟨T.1.support, ?_⟩
  rw [quotientBadRootedThreeFamily,
    QuotientSubmoduleEquidistribution.SetClosure.mem_badRootedDeletions]
  refine ⟨T.1.support_card,
    StripAdmissibleTriple.support_projectivelyRooted
      (σ := σ) (σ.finiteDimensionalARTranslationData k R) T.1 T.2, ?_⟩
  exact quotientFactorLadderBad_of_admissibleHook
    (k := k) (R := R) σ T.1.support
      (StripAdmissibleTriple.toAdmissibleHookOnSupport
        (σ := σ) (σ.finiteDimensionalARTranslationData k R) T.1)

noncomputable def quotientBadRootedThreeEquivProjectiveStrip :
    QuotientBadRootedThree (k := k) (R := R) σ ≃
      {T : (σ.finiteDimensionalARTranslationData k R).StripAdmissibleTriple σ //
        Projective (σ.obj T.a)} where
  toFun := quotientBadRootedThreeToProjectiveStrip
    (k := k) (σ := σ)
  invFun := projectiveStripToQuotientBadRootedThree
    (k := k) (R := R) σ
  left_inv D := by
    apply Subtype.ext
    let H := Classical.choice
      (quotientBadRootedThree_nonempty_hook
        (k := k) (σ := σ) D)
    have h : D.1.card = 3 ∧
        QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
          σ.irreducibleEdge σ.projectiveLabelFinset D.1 ∧
        QuotientFactorLadderBad (k := k) (R := R) σ D.1 := by
      simpa only [quotientBadRootedThreeFamily,
        QuotientSubmoduleEquidistribution.SetClosure.mem_badRootedDeletions] using D.2
    change (H.toStripAdmissibleTriple σ
      (σ.finiteDimensionalARTranslationData k R) D.1 h.2.1).support = D.1
    exact AdmissibleHook.stripSupport_eq_deleted_of_card_three
      (σ := σ) (σ.finiteDimensionalARTranslationData k R)
        D.1 h.1 h.2.1 H
  right_inv T := by
    apply Subtype.ext
    let D := projectiveStripToQuotientBadRootedThree
      (k := k) (R := R) σ T
    have hD : D.1.card = 3 ∧
        QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
          σ.irreducibleEdge σ.projectiveLabelFinset D.1 ∧
        QuotientFactorLadderBad (k := k) (R := R) σ D.1 := by
      simpa only [quotientBadRootedThreeFamily,
        QuotientSubmoduleEquidistribution.SetClosure.mem_badRootedDeletions] using D.2
    let H := Classical.choice
      (quotientBadRootedThree_nonempty_hook
        (k := k) (σ := σ) D)
    let H₀ := StripAdmissibleTriple.toAdmissibleHookOnSupport
      (σ := σ) (σ.finiteDimensionalARTranslationData k R) T.1
    have hH : H = H₀ :=
      (admissibleHook_subsingleton_of_rooted_card_three
        (σ := σ) (σ.finiteDimensionalARTranslationData k R)
          D.1 hD.1 hD.2.1).allEq H H₀
    change (H.toStripAdmissibleTriple σ
      (σ.finiteDimensionalARTranslationData k R) D.1 hD.2.1) = T.1
    rw [hH]
    ext <;> rfl

section Reverse

variable {S : Type u}
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing S]
  {κ : Type w} [Fintype κ] [DecidableEq κ]
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

def submoduleBadRootedThreeFamily
    (D : AlignedBiduality σ τ) : Finset (Finset ι) :=
  QuotientSubmoduleEquidistribution.SetClosure.badRootedDeletions
    (QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted
      σ.irreducibleEdge σ.injectiveLabelFinset)
    (SubmoduleFactorLadderBad (k := k) (S := S) σ τ D) 3

abbrev SubmoduleBadRootedThree
    (D : AlignedBiduality σ τ) : Type v :=
  {Deleted // Deleted ∈ submoduleBadRootedThreeFamily
    (k := k) (S := S) σ τ D}

set_option linter.unusedSectionVars false in
theorem mem_quotientBadRootedThreeFamily_dualDeleted_iff
    (D : AlignedBiduality σ τ) (Deleted : Finset ι) :
    D.dualDeleted σ τ Deleted ∈
        quotientBadRootedThreeFamily (k := k) (R := S) τ ↔
      Deleted ∈ submoduleBadRootedThreeFamily
        (k := k) (S := S) σ τ D := by
  rw [quotientBadRootedThreeFamily, submoduleBadRootedThreeFamily,
    QuotientSubmoduleEquidistribution.SetClosure.mem_badRootedDeletions,
    QuotientSubmoduleEquidistribution.SetClosure.mem_badRootedDeletions]
  constructor
  · rintro ⟨hcard, hroot, hbad⟩
    exact ⟨by simpa using hcard,
      (D.isProjectivelyRooted_dualDeleted_iff_isInjectivelyCorooted
        σ τ Deleted).1 hroot,
      (D.quotientFactorLadderBad_dualDeleted_iff_submoduleFactorLadderBad
        (k := k) (R := R) (S := S) σ τ Deleted).1 hbad⟩
  · rintro ⟨hcard, hroot, hbad⟩
    exact ⟨by simpa using hcard,
      (D.isProjectivelyRooted_dualDeleted_iff_isInjectivelyCorooted
        σ τ Deleted).2 hroot,
      (D.quotientFactorLadderBad_dualDeleted_iff_submoduleFactorLadderBad
        (k := k) (R := R) (S := S) σ τ Deleted).2 hbad⟩

noncomputable def quotientBadRootedThreeEquivSubmodule
    (D : AlignedBiduality σ τ) :
    QuotientBadRootedThree (k := k) (R := S) τ ≃
      SubmoduleBadRootedThree (k := k) (S := S) σ τ D where
  toFun Q := by
    let Deleted := D.forward.labelEquiv.finsetCongr.symm Q.1
    refine ⟨Deleted, ?_⟩
    apply (mem_quotientBadRootedThreeFamily_dualDeleted_iff
      (k := k) (R := R) (S := S) σ τ D Deleted).1
    have hDeleted : D.dualDeleted σ τ Deleted = Q.1 := by
      change D.forward.labelEquiv.finsetCongr
        (D.forward.labelEquiv.finsetCongr.symm Q.1) = Q.1
      exact D.forward.labelEquiv.finsetCongr.apply_symm_apply Q.1
    rw [hDeleted]
    exact Q.2
  invFun Q := ⟨D.dualDeleted σ τ Q.1,
    (mem_quotientBadRootedThreeFamily_dualDeleted_iff
      (k := k) (R := R) (S := S) σ τ D Q.1).2 Q.2⟩
  left_inv Q := by
    apply Subtype.ext
    change D.forward.labelEquiv.finsetCongr
      (D.forward.labelEquiv.finsetCongr.symm Q.1) = Q.1
    exact D.forward.labelEquiv.finsetCongr.apply_symm_apply Q.1
  right_inv Q := by
    apply Subtype.ext
    change D.forward.labelEquiv.finsetCongr.symm
      (D.forward.labelEquiv.finsetCongr Q.1) = Q.1
    exact D.forward.labelEquiv.finsetCongr.symm_apply_apply Q.1

include k in
theorem badRootedThree_card_eq_of_alignedBiduality
    (D : AlignedBiduality σ τ) :
    (quotientBadRootedThreeFamily (k := k) (R := R) σ).card =
      (submoduleBadRootedThreeFamily
        (k := k) (S := S) σ τ D).card := by
  let ARσ := σ.finiteDimensionalARTranslationData k R
  let ARτ := τ.finiteDimensionalARTranslationData k S
  calc
    (quotientBadRootedThreeFamily (k := k) (R := R) σ).card =
        Fintype.card (QuotientBadRootedThree (k := k) (R := R) σ) := by
      simp [QuotientBadRootedThree]
    _ = Fintype.card {T : ARσ.StripAdmissibleTriple σ //
          Projective (σ.obj T.a)} :=
      Fintype.card_congr
        (quotientBadRootedThreeEquivProjectiveStrip
          (k := k) (R := R) σ)
    _ = Fintype.card {T : ARτ.StripAdmissibleTriple τ //
          Projective (τ.obj T.a)} :=
      FiniteARTranslationData.projectiveStrip_card_eq
        (K := k) σ τ ARσ ARτ D
    _ = Fintype.card (QuotientBadRootedThree (k := k) (R := S) τ) :=
      (Fintype.card_congr
        (quotientBadRootedThreeEquivProjectiveStrip
          (k := k) (R := S) τ)).symm
    _ = Fintype.card
        (SubmoduleBadRootedThree (k := k) (S := S) σ τ D) :=
      Fintype.card_congr
        (quotientBadRootedThreeEquivSubmodule
          (k := k) (R := R) (S := S) σ τ D)
    _ = (submoduleBadRootedThreeFamily
          (k := k) (S := S) σ τ D).card := by
      simp [SubmoduleBadRootedThree]

include k in
theorem levelCount_card_sub_three_eq_of_alignedBiduality
    (D : AlignedBiduality σ τ) (hthree : 3 ≤ Nat.card ι) :
    σ.qClosure.levelCount (Nat.card ι - 3) =
      σ.sClosure.levelCount (Nat.card ι - 3) := by
  apply levelCount_card_sub_eq_of_badRootedFactorLadderBalance
    (k := k) (R := R) (S := S) σ τ D 3 hthree
  exact badRootedThree_card_eq_of_alignedBiduality
    (k := k) (R := R) (S := S) σ τ D

end Reverse

end ThreeVertex
end FiniteARTranslationData
end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
