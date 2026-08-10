import QuotientSubmoduleEquidistribution.RepresentationTheory.AlgebraicallyClosedIrreducibleMultiplicityOne
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderEventualVanishing
import QuotientSubmoduleEquidistribution.RepresentationTheory.NormalizedFourVertexBoundaryAxioms

/-!
# Exact realization of normalized four-vertex factor ladders

This file identifies the actual multiplicity-free factor-ladder recurrence
with the unbounded natural semantics of a normalized code.  Projective
rootedness is used exactly where ordinary retained AR translation is shown
to agree with the restricted operator `tau_D`; algebraic closedness enters
only through the separately stated unit-multiplicity hypothesis.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped BigOperators

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable {k R : Type u} [Field k] [IsAlgClosed k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

namespace NormalizedFour

open QuotientSubmoduleEquidistribution.NormalizedFourVertexLadderClassification

/-- Integer factor-ladder datum directly decoded from a normalized code. -/
def codeFactorLadderData (C : Code) :
    QuotientSubmoduleEquidistribution.FactorLadder.Data Vertex where
  theta := QuotientSubmoduleEquidistribution.FactorLadder.matrixAddHom fun x y ↦
    if edge C y x then 1 else 0
  tau := QuotientSubmoduleEquidistribution.FactorLadder.matrixAddHom fun x y ↦
    if tauEq C x y then 1 else 0

def natCastVector (v : NatVector) :
    QuotientSubmoduleEquidistribution.FactorLadder.IntVector Vertex :=
  fun y ↦ (v y : ℤ)

theorem codeFactorLadderData_theta_natCast
    (C : Code) (v : NatVector) :
    (codeFactorLadderData C).theta (natCastVector v) =
      natCastVector (naturalTheta C v) := by
  funext y
  simp [codeFactorLadderData, natCastVector,
    QuotientSubmoduleEquidistribution.FactorLadder.matrixAddHom_apply,
    naturalTheta, natMask, Fin.sum_univ_four]

theorem codeFactorLadderData_tau_natCast
    (C : Code) (v : NatVector) :
    (codeFactorLadderData C).tau (natCastVector v) =
      natCastVector (naturalTauVector C v) := by
  funext y
  simp [codeFactorLadderData, natCastVector,
    QuotientSubmoduleEquidistribution.FactorLadder.matrixAddHom_apply,
    naturalTauVector, natMask, Fin.sum_univ_four]

theorem positivePart_natCast_sub (a b : ℕ) :
    max ((a : ℤ) - (b : ℤ)) 0 = (a - b : ℕ) := by
  omega

theorem codeFactorLadderData_step_natCast
    (C : Code) (next previous : NatVector) :
    QuotientSubmoduleEquidistribution.FactorLadder.positivePart
      ((codeFactorLadderData C).theta (natCastVector next) -
        (codeFactorLadderData C).tau (natCastVector previous)) =
      natCastVector (naturalStep C next previous) := by
  rw [codeFactorLadderData_theta_natCast,
    codeFactorLadderData_tau_natCast]
  funext y
  simp [QuotientSubmoduleEquidistribution.FactorLadder.positivePart, natCastVector,
    naturalStep, positivePart_natCast_sub]

theorem codeFactorLadderData_ladder_zero
    (C : Code) (x : Vertex) :
    (codeFactorLadderData C).ladder x 0 =
      natCastVector (naturalLadderZero x) := by
  funext y
  simp [QuotientSubmoduleEquidistribution.FactorLadder.Data.ladder_zero,
    QuotientSubmoduleEquidistribution.FactorLadder.basis, natCastVector, naturalLadderZero]

theorem codeFactorLadderData_ladder_one
    (C : Code) (x : Vertex) :
    (codeFactorLadderData C).ladder x 1 =
      natCastVector (naturalLadderOne C x) := by
  rw [QuotientSubmoduleEquidistribution.FactorLadder.Data.ladder_one]
  have hbasis := codeFactorLadderData_ladder_zero C x
  rw [QuotientSubmoduleEquidistribution.FactorLadder.Data.ladder_zero] at hbasis
  rw [hbasis, codeFactorLadderData_theta_natCast]
  rfl

theorem codeFactorLadderData_ladder_two
    (C : Code) (x : Vertex) :
    (codeFactorLadderData C).ladder x 2 =
      natCastVector (naturalLadderTwo C x) := by
  rw [show 2 = 0 + 2 by omega,
    QuotientSubmoduleEquidistribution.FactorLadder.Data.ladder_add_two,
    codeFactorLadderData_ladder_one,
    codeFactorLadderData_ladder_zero,
    codeFactorLadderData_step_natCast]
  rfl

theorem codeFactorLadderData_ladder_three
    (C : Code) (x : Vertex) :
    (codeFactorLadderData C).ladder x 3 =
      natCastVector (naturalLadderThree C x) := by
  rw [show 3 = 1 + 2 by omega,
    QuotientSubmoduleEquidistribution.FactorLadder.Data.ladder_add_two,
    codeFactorLadderData_ladder_two,
    codeFactorLadderData_ladder_one,
    codeFactorLadderData_step_natCast]
  rfl

theorem codeFactorLadderData_ladder_four
    (C : Code) (x : Vertex) :
    (codeFactorLadderData C).ladder x 4 =
      natCastVector (naturalLadderFour C x) := by
  rw [show 4 = 2 + 2 by omega,
    QuotientSubmoduleEquidistribution.FactorLadder.Data.ladder_add_two,
    codeFactorLadderData_ladder_three,
    codeFactorLadderData_ladder_two,
    codeFactorLadderData_step_natCast]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem BoundaryRealization.middleMultiplicity_eq_edgeIndicator
    {K : Set ι} (Q : BoundaryRealization (σ := σ) AR K)
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ K)
    (x y : DeletedLabel K) :
    deletedMiddleMultiplicity (σ := σ) (D := AR) K x y =
      if edge Q.code (Q.labelEquiv y) (Q.labelEquiv x) then 1 else 0 := by
  cases he : edge Q.code (Q.labelEquiv y) (Q.labelEquiv x)
  · have hirr : ¬ HasIrreducibleMorphism (σ.obj y.1) (σ.obj x.1) := by
      intro h
      have := (Q.edge_iff y x).2 h
      simp [he] at this
    have hnotpos : ¬ 0 <
        deletedMiddleMultiplicity (σ := σ) (D := AR) K x y :=
      (AR.deletedMiddleMultiplicity_pos_iff_irreducible σ K x y).not.mpr hirr
    have hnonneg := AR.deletedMiddleMultiplicity_nonneg σ K x y
    have hz : deletedMiddleMultiplicity (σ := σ) (D := AR) K x y = 0 := by
      omega
    simp [hz]
  · have hirr := (Q.edge_iff y x).1 he
    simpa [he] using hunit x y hirr

omit [DecidableEq ι] in
theorem factorTauTarget_eq_retainedTarget_of_rooted
    {K : Set ι}
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (x : DeletedLabel K) :
    factorLadderTauTarget (σ := σ) (D := AR) K x =
      AR.retainedARTranslationTarget σ K x := by
  classical
  by_cases hx : Projective (σ.obj x.1)
  · simp [factorLadderTauTarget, retainedARTranslationTarget, hx]
  · by_cases htx : (AR.arTranslation σ ⟨x.1, hx⟩).1 ∈ K
    · simp [factorLadderTauTarget, retainedARTranslationTarget, hx, htx]
    · have htheta : factorLadderTheta (σ := σ) (D := AR) K
          (QuotientSubmoduleEquidistribution.FactorLadder.basis x) ≠ 0 := by
        rcases hroot x with ⟨p, hp, hpx⟩
        rcases Relation.ReflTransGen.cases_tail hpx with hpx | ⟨y, _, hyx⟩
        · exact (hx (hpx ▸ hp)).elim
        · intro hzero
          have hcoord := congrFun hzero y
          rw [AR.factorLadderTheta_basis_apply σ K x y,
            Pi.zero_apply] at hcoord
          have hpos :=
            (AR.deletedMiddleMultiplicity_pos_iff_irreducible σ K x y).2 hyx
          omega
      simp [factorLadderTauTarget, retainedARTranslationTarget,
        hx, htx, htheta]

omit [DecidableEq ι] in
theorem BoundaryRealization.factorTauEntry_eq_indicator
    {K : Set ι} (Q : BoundaryRealization (σ := σ) AR K)
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (x y : DeletedLabel K) :
    factorLadderTauEntry (σ := σ) (D := AR) K x y =
      if tauEq Q.code (Q.labelEquiv x) (Q.labelEquiv y) then 1 else 0 := by
  classical
  rw [factorLadderTauEntry,
    factorTauTarget_eq_retainedTarget_of_rooted σ AR hroot]
  by_cases hx : Projective (σ.obj x.1)
  · have hnone := Q.tau_none_of_projective x hx
    have hfalse := tauEq_eq_false_of_tauNone hnone (Q.labelEquiv y)
    simp [retainedARTranslationTarget, hx, hfalse]
  · have hiff : AR.retainedARTranslationTarget σ K x = some y ↔
        tauEq Q.code (Q.labelEquiv x) (Q.labelEquiv y) = true :=
      (retainedARTranslationTarget_eq_some_iff
        (AR := AR) σ x y hx).trans (Q.tau_eq_iff x y hx).symm
    rw [if_congr hiff rfl rfl]

omit [DecidableEq ι] in
/-- Exact relabelling of the actual multiplicity-free factor ladder by its
normalized integer code. -/
theorem BoundaryRealization.factorLadderRelabeling
    {K : Set ι} (Q : BoundaryRealization (σ := σ) AR K)
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ K)
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x) :
    QuotientSubmoduleEquidistribution.FactorLadder.Data.Relabeling
      (AR.factorLadderData σ K) (codeFactorLadderData Q.code)
      Q.labelEquiv where
  theta v := by
    classical
    funext y
    simp only [QuotientSubmoduleEquidistribution.FactorLadder.Data.reindex_apply,
      AR.factorLadderData_theta, factorLadderTheta,
      QuotientSubmoduleEquidistribution.FactorLadder.matrixAddHom_apply,
      codeFactorLadderData]
    apply Fintype.sum_equiv Q.labelEquiv
    intro x
    rw [Q.middleMultiplicity_eq_edgeIndicator (AR := AR) σ hunit]
    simp
  tau v := by
    classical
    funext y
    simp only [QuotientSubmoduleEquidistribution.FactorLadder.Data.reindex_apply,
      AR.factorLadderData_tau, factorLadderTau,
      QuotientSubmoduleEquidistribution.FactorLadder.matrixAddHom_apply,
      codeFactorLadderData]
    apply Fintype.sum_equiv Q.labelEquiv
    intro x
    rw [Q.factorTauEntry_eq_indicator (AR := AR) σ hroot]
    simp

omit [DecidableEq ι] in
theorem BoundaryRealization.factorLadder_coefficient_eq_of_code_eq
    {K : Set ι} (Q : BoundaryRealization (σ := σ) AR K)
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ K)
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (x y : DeletedLabel K) (n : ℕ) (v : NatVector)
    (hcode : (codeFactorLadderData Q.code).ladder
      (Q.labelEquiv x) n = natCastVector v) :
    (AR.factorLadderData σ K).ladder x n y =
      (v (Q.labelEquiv y) : ℤ) := by
  have hrelabel := Q.factorLadderRelabeling (AR := AR) σ hunit hroot
  have h := congrFun (hrelabel.reindex_ladder x n) (Q.labelEquiv y)
  rw [hcode] at h
  simpa [QuotientSubmoduleEquidistribution.FactorLadder.Data.reindex_apply,
    natCastVector] using h

omit [DecidableEq ι] in
theorem BoundaryRealization.factorLadder_zero_coefficient_eq_natural
    {K : Set ι} (Q : BoundaryRealization (σ := σ) AR K)
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ K)
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (x y : DeletedLabel K) :
    (AR.factorLadderData σ K).ladder x 0 y =
      (naturalLadderZero (Q.labelEquiv x) (Q.labelEquiv y) : ℤ) :=
  Q.factorLadder_coefficient_eq_of_code_eq (AR := AR) σ hunit hroot
    x y 0 _ (codeFactorLadderData_ladder_zero Q.code (Q.labelEquiv x))

omit [DecidableEq ι] in
theorem BoundaryRealization.factorLadder_one_coefficient_eq_natural
    {K : Set ι} (Q : BoundaryRealization (σ := σ) AR K)
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ K)
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (x y : DeletedLabel K) :
    (AR.factorLadderData σ K).ladder x 1 y =
      (naturalLadderOne Q.code (Q.labelEquiv x)
        (Q.labelEquiv y) : ℤ) :=
  Q.factorLadder_coefficient_eq_of_code_eq (AR := AR) σ hunit hroot
    x y 1 _ (codeFactorLadderData_ladder_one Q.code (Q.labelEquiv x))

omit [DecidableEq ι] in
theorem BoundaryRealization.factorLadder_two_coefficient_eq_natural
    {K : Set ι} (Q : BoundaryRealization (σ := σ) AR K)
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ K)
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (x y : DeletedLabel K) :
    (AR.factorLadderData σ K).ladder x 2 y =
      (naturalLadderTwo Q.code (Q.labelEquiv x)
        (Q.labelEquiv y) : ℤ) :=
  Q.factorLadder_coefficient_eq_of_code_eq (AR := AR) σ hunit hroot
    x y 2 _ (codeFactorLadderData_ladder_two Q.code (Q.labelEquiv x))

omit [DecidableEq ι] in
theorem BoundaryRealization.factorLadder_three_coefficient_eq_natural
    {K : Set ι} (Q : BoundaryRealization (σ := σ) AR K)
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ K)
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (x y : DeletedLabel K) :
    (AR.factorLadderData σ K).ladder x 3 y =
      (naturalLadderThree Q.code (Q.labelEquiv x)
        (Q.labelEquiv y) : ℤ) :=
  Q.factorLadder_coefficient_eq_of_code_eq (AR := AR) σ hunit hroot
    x y 3 _ (codeFactorLadderData_ladder_three Q.code (Q.labelEquiv x))

omit [DecidableEq ι] in
theorem BoundaryRealization.factorLadder_four_coefficient_eq_natural
    {K : Set ι} (Q : BoundaryRealization (σ := σ) AR K)
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ K)
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (x y : DeletedLabel K) :
    (AR.factorLadderData σ K).ladder x 4 y =
      (naturalLadderFour Q.code (Q.labelEquiv x)
        (Q.labelEquiv y) : ℤ) :=
  Q.factorLadder_coefficient_eq_of_code_eq (AR := AR) σ hunit hroot
    x y 4 _ (codeFactorLadderData_ladder_four Q.code (Q.labelEquiv x))

private theorem exists_apply_ne_of_ne
    {α β : Type*} {f g : α → β} (h : f ≠ g) :
    ∃ x, f x ≠ g x := by
  by_contra hall
  push Not at hall
  exact h (funext hall)

omit [DecidableEq ι] in
/-- An exact four-step certificate for the actual multiplicity-free factor
ladder transports to the natural-number conditions of the normalized
Boolean witness. -/
theorem BoundaryRealization.boundaryWitnessConditions_of_fourStep
    {K : Set ι} (Q : BoundaryRealization (σ := σ) AR K)
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ K)
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (x : DeletedLabel K)
    (H : (AR.factorLadderData σ K).FourStepAvoidingCertificate
      (deletedProjectiveSet σ K) x) :
    BoundaryWitnessConditions Q.code Q.additionalBoundary
      (Q.labelEquiv x) := by
  have hxnp : ¬ Projective (σ.obj x.1) := by
    intro hx
    apply H.start_not_mem
    simpa [deletedProjectiveSet] using hx
  have hstart : boundaryAt Q.additionalBoundary (Q.labelEquiv x) = false := by
    cases hb : boundaryAt Q.additionalBoundary (Q.labelEquiv x)
    · rfl
    · exact (hxnp ((Q.projective_iff_boundary x).2 hb)).elim
  have projectiveOfBoundary : ∀ p : Vertex,
      boundaryAt Q.additionalBoundary p = true →
        Projective (σ.obj (Q.labelEquiv.symm p).1) := by
    intro p hp
    exact (Q.projective_iff_boundary (Q.labelEquiv.symm p)).2 (by
      simpa using hp)
  have hzero0 : ∀ p, boundaryAt Q.additionalBoundary p = true →
      naturalLadderZero (Q.labelEquiv x) p = 0 := by
    intro p hp
    let p' := Q.labelEquiv.symm p
    have hpP : p' ∈ deletedProjectiveSet σ K := by
      simpa [p', deletedProjectiveSet] using projectiveOfBoundary p hp
    have hz := H.boundary_zero_through_four 0 (by omega) p' hpP
    have heq := Q.factorLadder_zero_coefficient_eq_natural
      (AR := AR) σ hunit hroot x p'
    rw [hz] at heq
    have : (naturalLadderZero (Q.labelEquiv x) p : ℤ) = 0 := by
      simpa [p'] using heq.symm
    exact_mod_cast this
  have hzero1 : ∀ p, boundaryAt Q.additionalBoundary p = true →
      naturalLadderOne Q.code (Q.labelEquiv x) p = 0 := by
    intro p hp
    let p' := Q.labelEquiv.symm p
    have hpP : p' ∈ deletedProjectiveSet σ K := by
      simpa [p', deletedProjectiveSet] using projectiveOfBoundary p hp
    have hz := H.boundary_zero_through_four 1 (by omega) p' hpP
    have heq := Q.factorLadder_one_coefficient_eq_natural
      (AR := AR) σ hunit hroot x p'
    rw [hz] at heq
    have : (naturalLadderOne Q.code (Q.labelEquiv x) p : ℤ) = 0 := by
      simpa [p'] using heq.symm
    exact_mod_cast this
  have hzero2 : ∀ p, boundaryAt Q.additionalBoundary p = true →
      naturalLadderTwo Q.code (Q.labelEquiv x) p = 0 := by
    intro p hp
    let p' := Q.labelEquiv.symm p
    have hpP : p' ∈ deletedProjectiveSet σ K := by
      simpa [p', deletedProjectiveSet] using projectiveOfBoundary p hp
    have hz := H.boundary_zero_through_four 2 (by omega) p' hpP
    have heq := Q.factorLadder_two_coefficient_eq_natural
      (AR := AR) σ hunit hroot x p'
    rw [hz] at heq
    have : (naturalLadderTwo Q.code (Q.labelEquiv x) p : ℤ) = 0 := by
      simpa [p'] using heq.symm
    exact_mod_cast this
  have hzero3 : ∀ p, boundaryAt Q.additionalBoundary p = true →
      naturalLadderThree Q.code (Q.labelEquiv x) p = 0 := by
    intro p hp
    let p' := Q.labelEquiv.symm p
    have hpP : p' ∈ deletedProjectiveSet σ K := by
      simpa [p', deletedProjectiveSet] using projectiveOfBoundary p hp
    have hz := H.boundary_zero_through_four 3 (by omega) p' hpP
    have heq := Q.factorLadder_three_coefficient_eq_natural
      (AR := AR) σ hunit hroot x p'
    rw [hz] at heq
    have : (naturalLadderThree Q.code (Q.labelEquiv x) p : ℤ) = 0 := by
      simpa [p'] using heq.symm
    exact_mod_cast this
  have hzero4 : ∀ p, boundaryAt Q.additionalBoundary p = true →
      naturalLadderFour Q.code (Q.labelEquiv x) p = 0 := by
    intro p hp
    let p' := Q.labelEquiv.symm p
    have hpP : p' ∈ deletedProjectiveSet σ K := by
      simpa [p', deletedProjectiveSet] using projectiveOfBoundary p hp
    have hz := H.boundary_zero_through_four 4 (by omega) p' hpP
    have heq := Q.factorLadder_four_coefficient_eq_natural
      (AR := AR) σ hunit hroot x p'
    rw [hz] at heq
    have : (naturalLadderFour Q.code (Q.labelEquiv x) p : ℤ) = 0 := by
      simpa [p'] using heq.symm
    exact_mod_cast this
  refine
    { start_not_boundary := hstart
      boundary_zero_zero := ?_
      boundary_zero_one := ?_
      boundary_zero_two := ?_
      boundary_zero_three := ?_
      boundary_zero_four := ?_
      pair_zero_two := ?_
      pair_zero_three := ?_ }
  · intro p hp
    rw [ladderCoefficientZero_eq_natural]
    exact hzero0 p hp
  · intro p hp
    rw [ladderCoefficientOne_eq_natural]
    exact hzero1 p hp
  · intro p hp
    rw [ladderCoefficientTwo_eq_natural]
    exact hzero2 p hp
  · intro p hp
    rw [ladderCoefficientThree_eq_natural]
    exact hzero3 p hp
  · intro p hp
    rw [ladderCoefficientFour_eq_natural]
    exact hzero4 p hp
  · rcases H.pair_zero_two with h02 | h13
    · left
      rcases exists_apply_ne_of_ne h02 with ⟨y, hy⟩
      refine ⟨Q.labelEquiv y, ?_⟩
      rw [ladderCoefficientZero_eq_natural,
        ladderCoefficientTwo_eq_natural]
      intro hnat
      apply hy
      have h0 := Q.factorLadder_zero_coefficient_eq_natural
        (AR := AR) σ hunit hroot x y
      have h2 := Q.factorLadder_two_coefficient_eq_natural
        (AR := AR) σ hunit hroot x y
      exact h0.trans ((congrArg (fun n : ℕ ↦ (n : ℤ)) hnat).trans h2.symm)
    · right
      rcases exists_apply_ne_of_ne h13 with ⟨y, hy⟩
      refine ⟨Q.labelEquiv y, ?_⟩
      rw [ladderCoefficientOne_eq_natural,
        ladderCoefficientThree_eq_natural]
      intro hnat
      apply hy
      have h1 := Q.factorLadder_one_coefficient_eq_natural
        (AR := AR) σ hunit hroot x y
      have h3 := Q.factorLadder_three_coefficient_eq_natural
        (AR := AR) σ hunit hroot x y
      exact h1.trans ((congrArg (fun n : ℕ ↦ (n : ℤ)) hnat).trans h3.symm)
  · rcases H.pair_zero_three with h03 | h14
    · left
      rcases exists_apply_ne_of_ne h03 with ⟨y, hy⟩
      refine ⟨Q.labelEquiv y, ?_⟩
      rw [ladderCoefficientZero_eq_natural,
        ladderCoefficientThree_eq_natural]
      intro hnat
      apply hy
      have h0 := Q.factorLadder_zero_coefficient_eq_natural
        (AR := AR) σ hunit hroot x y
      have h3 := Q.factorLadder_three_coefficient_eq_natural
        (AR := AR) σ hunit hroot x y
      exact h0.trans ((congrArg (fun n : ℕ ↦ (n : ℤ)) hnat).trans h3.symm)
    · right
      rcases exists_apply_ne_of_ne h14 with ⟨y, hy⟩
      refine ⟨Q.labelEquiv y, ?_⟩
      rw [ladderCoefficientOne_eq_natural,
        ladderCoefficientFour_eq_natural]
      intro hnat
      apply hy
      have h1 := Q.factorLadder_one_coefficient_eq_natural
        (AR := AR) σ hunit hroot x y
      have h4 := Q.factorLadder_four_coefficient_eq_natural
        (AR := AR) σ hunit hroot x y
      exact h1.trans ((congrArg (fun n : ℕ ↦ (n : ℤ)) hnat).trans h4.symm)

omit [DecidableEq ι] in
/-- Boolean form of the exact four-step certificate transport. -/
theorem BoundaryRealization.boundaryWitness_eq_true_of_fourStep
    {K : Set ι} (Q : BoundaryRealization (σ := σ) AR K)
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ K)
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (x : DeletedLabel K)
    (H : (AR.factorLadderData σ K).FourStepAvoidingCertificate
      (deletedProjectiveSet σ K) x) :
    BoundaryWitness Q.code Q.additionalBoundary (Q.labelEquiv x) = true :=
  boundaryWitness_eq_true_of_conditions
    (Q.boundaryWitnessConditions_of_fourStep
      (AR := AR) σ hunit hroot x H)

include k in
omit [DecidableEq ι] in
/-- Over an algebraically closed field, failure of an actual factor ladder
to reach a retained projective supplies the normalized Boolean witness. -/
theorem BoundaryRealization.boundaryWitness_eq_true_of_not_reachesBoundary
    {K : Set ι}
    (Q : BoundaryRealization (σ := σ)
      (σ.finiteDimensionalARTranslationData k R) K)
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (x : DeletedLabel K)
    (hnot :
      ¬ (σ.finiteDimensionalFactorLadderData k R K).ReachesBoundary
        (deletedProjectiveSet σ K) x) :
    BoundaryWitness Q.code Q.additionalBoundary (Q.labelEquiv x) = true := by
  have hunit := (σ.finiteDimensionalARTranslationData k R).hasUnitDeletedMiddleMultiplicities_of_isAlgClosed
    (k := k) (R := R) σ K
  apply Q.boundaryWitness_eq_true_of_fourStep
    (AR := σ.finiteDimensionalARTranslationData k R) σ
    hunit hroot x
  exact σ.finiteDimensionalFactorLadder_fourStepAvoidingCertificate
    (k := k) (R := R) K x hnot

omit [DecidableEq ι] in
/-- Boundary uniqueness followed by the normalized classifier turns an
actual hookless four-step witness into row `F` or row `T`. -/
theorem BoundaryRealization.nonempty_fixedPacket_or_trianglePacket_of_fourStep
    {K : Set ι} (Q : BoundaryRealization (σ := σ) AR K)
    [IsEmpty (AR.AdmissibleHook σ K)]
    (hunit : AR.HasUnitDeletedMiddleMultiplicities σ K)
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (hBoundaryAxioms :
      BoundaryAxioms Q.code Q.additionalBoundary = true)
    (x : DeletedLabel K)
    (H : (AR.factorLadderData σ K).FourStepAvoidingCertificate
      (deletedProjectiveSet σ K) x) :
    Nonempty (AR.FixedPacket σ K) ∨
      Nonempty (AR.TrianglePacket σ K) := by
  have hBoundaryWitness := Q.boundaryWitness_eq_true_of_fourStep
    (AR := AR) σ hunit hroot x H
  have hNoAdditional := Q.noAdditionalBoundary_of_isEmpty
    σ hBoundaryAxioms hBoundaryWitness
  let Q' := Q.toRealization σ hNoAdditional
  have hAxioms := axioms_of_boundaryAxioms_of_noAdditionalBoundary
    Q.code Q.additionalBoundary hBoundaryAxioms hNoAdditional
  have hWitness := witness_of_boundaryWitness_of_noAdditionalBoundary
    Q.code Q.additionalBoundary (Q.labelEquiv x)
      hBoundaryWitness hNoAdditional
  rcases fixed_or_triangle_of_axioms_of_hookless_of_witness
      Q.code (Q.labelEquiv x) hAxioms
        (Q'.hasHook_eq_false_of_isEmpty σ) hWitness with hF | hT
  · exact Or.inl (Q'.nonempty_fixedPacket_of_hasFixedPacket σ hF)
  · exact Or.inr (Q'.nonempty_trianglePacket_of_hasTrianglePacket σ hT)

include k in
omit [DecidableEq ι] in
/-- Algebraic closedness, the local AR restrictions, and failure to reach a
projective specialize the preceding exact hookless classification. -/
theorem BoundaryRealization.nonempty_fixedPacket_or_trianglePacket_of_not_reachesBoundary
    {K : Set ι}
    (Q : BoundaryRealization (σ := σ)
      (σ.finiteDimensionalARTranslationData k R) K)
    [IsEmpty
      ((σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ K)]
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (x : DeletedLabel K)
    (hnot :
      ¬ (σ.finiteDimensionalFactorLadderData k R K).ReachesBoundary
        (deletedProjectiveSet σ K) x) :
    Nonempty
        ((σ.finiteDimensionalARTranslationData k R).FixedPacket σ K) ∨
      Nonempty
        ((σ.finiteDimensionalARTranslationData k R).TrianglePacket σ K) := by
  have hunit := (σ.finiteDimensionalARTranslationData k R).hasUnitDeletedMiddleMultiplicities_of_isAlgClosed
    (k := k) (R := R) σ K
  apply Q.nonempty_fixedPacket_or_trianglePacket_of_fourStep
    (AR := σ.finiteDimensionalARTranslationData k R) σ
    hunit hroot (Q.boundaryAxioms_eq_true_of_rooted
      (k := k) (AR := σ.finiteDimensionalARTranslationData k R) σ hroot) x
  exact σ.finiteDimensionalFactorLadder_fourStepAvoidingCertificate
    (k := k) (R := R) K x hnot

include k in
/-- Actual four-vertex classification used by the manuscript: a
projectively rooted bad support contains an admissible hook, row `F`, or row
`T`.  The proof uses only the general AR restrictions and the exact ladder
recurrence, not a classification of algebras or modules. -/
theorem hook_or_fixed_or_triangle_of_bad_rooted_four
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (hroot : QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (hbad : QuotientFactorLadderBad (k := k) (R := R) σ Deleted) :
    let K : Set ι := ((Deleted : Finset ι) : Set ι)ᶜ
    let AR := σ.finiteDimensionalARTranslationData k R
    Nonempty (AR.AdmissibleHook σ K) ∨
      Nonempty (AR.FixedPacket σ K) ∨
        Nonempty (AR.TrianglePacket σ K) := by
  let K : Set ι := ((Deleted : Finset ι) : Set ι)ᶜ
  let AR := σ.finiteDimensionalARTranslationData k R
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
    · simpa [AR, K, fourVertexHookData, deletedProjectiveSet] using hp
    · simpa [AR, K, fourVertexHookData] using hpy
  rcases hroot' x with ⟨p, hp, _⟩
  let Q := BoundaryRealization.ofDeletedFour
    (σ := σ) (AR := AR) Deleted hcard p hp
  by_cases hHook : Nonempty (AR.AdmissibleHook σ K)
  · exact Or.inl hHook
  · haveI : IsEmpty (AR.AdmissibleHook σ K) :=
      ⟨fun H ↦ hHook ⟨H⟩⟩
    right
    exact Q.nonempty_fixedPacket_or_trianglePacket_of_not_reachesBoundary
      (k := k) (R := R) σ hroot' x (by simpa [AR, K] using hnot)

end NormalizedFour
end FiniteARTranslationData
end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
