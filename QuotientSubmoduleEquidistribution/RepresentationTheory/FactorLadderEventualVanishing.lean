import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorCategoryFactorLadderRecurrence
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderTermination
import QuotientSubmoduleEquidistribution.RepresentationTheory.ReverseFactorLadderRecurrence

/-!
# Eventual vanishing for the actual forward and reverse factor ladders

The categorical radical of the finite factor category is nilpotent.  The
literal Iyama radical-layer comparison therefore makes every forward factor
ladder eventually zero.  Relabeling across the maintained biduality gives
the same statement for the reverse ladder.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {k R : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The complete unconditional Iyama radical-layer input for the literal
factor quotient. -/
def finiteDimensionalFactorLadderIyamaInput (K : Set ι) :
    FactorLadder.IyamaRadicalLayerInput
      (σ.finiteDimensionalFactorLadderData k R K)
      (factorHomNonzero σ K) := by
  classical
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  letI : HasFiniteBiproducts (σ.FactorCategory K) :=
    σ.factorQuotientHasFiniteBiproducts Set.univ K
  letI : HasBinaryBiproducts (σ.FactorCategory K) :=
    HasBinaryBiproducts.of_hasBinaryCoproducts
  let hidem : IsIdempotentComplete (σ.FactorCategory K) :=
    σ.factorCategory_isIdempotentComplete (k := k) (R := R) K
  letI : IsIdempotentComplete (σ.FactorCategory K) := hidem
  letI : Fintype (DeletedLabel K) := Fintype.ofFinite _
  letI : DecidableEq (DeletedLabel K) := Classical.decEq _
  let T := σ.finiteDimensionalFactorCategoryRightTauData
    (k := k) (R := R) K hidem
  let E := σ.finiteDimensionalFactorCategoryTauExtension
    (k := k) (R := R) K
  apply σ.finiteDimensionalFactorLadderIyamaInput_of_rightLadderOrthogonality
    (k := k) (R := R) K hidem
  intro x
  dsimp only
  intro n q
  exact
    Iyama.RightLadder.FiniteTauCategoryExtension.zeroInitialRightLadder_discarded_radicalOrthogonal
      T E (σ.factorObject K x) n q

/-- Every actual forward factor ladder in a finite-dimensional
representation-finite skeleton is eventually zero. -/
theorem finiteDimensionalFactorLadder_eventuallyZero
    (K : Set ι) (x : DeletedLabel K) :
    (σ.finiteDimensionalFactorLadderData k R K).EventuallyZero x :=
  (σ.finiteDimensionalFactorLadderIyamaInput
    (k := k) (R := R) K).eventually_ladder_zero x

/-- Hence a forward ladder terminates without a deleted projective exactly
when it does not reach the deleted projective boundary. -/
theorem finiteDimensionalFactorLadder_terminatesWithoutProjective_iff
    (K : Set ι) (x : DeletedLabel K) :
    (σ.finiteDimensionalFactorLadderData k R K).TerminatesWithoutBoundary
        (deletedProjectiveSet σ K) x ↔
      ¬ (σ.finiteDimensionalFactorLadderData k R K).ReachesBoundary
        (deletedProjectiveSet σ K) x :=
  (σ.finiteDimensionalFactorLadderIyamaInput
    (k := k) (R := R) K).terminatesWithoutBoundary_iff_not_reachesBoundary
      (deletedProjectiveSet σ K) x

/-- Failure to reach a deleted projective supplies the exact four-step
finite certificate used by the normalized colevel-four classifier. -/
theorem finiteDimensionalFactorLadder_fourStepAvoidingCertificate
    (K : Set ι) (x : DeletedLabel K)
    (hnot :
      ¬ (σ.finiteDimensionalFactorLadderData k R K).ReachesBoundary
        (deletedProjectiveSet σ K) x) :
    (σ.finiteDimensionalFactorLadderData k R K).FourStepAvoidingCertificate
      (deletedProjectiveSet σ K) x := by
  apply FactorLadder.Data.fourStepAvoidingCertificate_of_terminatesWithoutBoundary
    (σ.finiteDimensionalFactorLadderData k R K)
  · intro n d
    exact (σ.finiteDimensionalARTranslationData k R).factorLadderData_ladder_nonneg
      σ K x n d
  · exact (σ.finiteDimensionalFactorLadder_terminatesWithoutProjective_iff
      (k := k) (R := R) K x).2 hnot

section Reverse

variable {S : Type u} [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing S]
  {κ : Type w} [Fintype κ]
  (τ : IndecomposableSkeleton.{u, w, u} S κ)
  (D : AlignedBiduality σ τ)

omit [Algebra k R] [FiniteDimensional k R] [Fintype ι] in
/-- Eventual vanishing transports through the deleted-label equivalence, so
the actual reverse factor ladder is eventually zero as well. -/
theorem AlignedBiduality.finiteDimensionalReverseFactorLadder_eventuallyZero
    (K : Set ι) (x : DeletedLabel K) :
    (D.finiteDimensionalReverseFactorLadderData
      (k := k) (S := S) σ τ K).EventuallyZero x := by
  let e := D.forward.deletedLabelEquiv σ τ K
  let A := D.finiteDimensionalReverseFactorLadderData
    (k := k) (S := S) σ τ K
  let B := τ.finiteDimensionalFactorLadderData k S
    (D.forward.labelEquiv '' K)
  have hrel : FactorLadder.Data.Relabeling A B e :=
    D.finiteDimensionalReverseFactorLadderData_relabeling
      (k := k) (S := S) σ τ K
  obtain ⟨N, hN⟩ := τ.finiteDimensionalFactorLadder_eventuallyZero
    (k := k) (R := S) (D.forward.labelEquiv '' K) (e x)
  refine ⟨N, fun n hn ↦ ?_⟩
  apply (FactorLadder.Data.reindex e).injective
  simpa using (hrel.reindex_ladder x n).trans (hN n hn)

omit [Algebra k R] [FiniteDimensional k R] [Fintype ι] in
/-- Reverse termination without a deleted injective is exactly failure to
reach the deleted injective boundary. -/
theorem AlignedBiduality.finiteDimensionalReverseFactorLadder_terminatesWithoutInjective_iff
    (K : Set ι) (x : DeletedLabel K) :
    (D.finiteDimensionalReverseFactorLadderData
      (k := k) (S := S) σ τ K).TerminatesWithoutBoundary
        (deletedInjectiveSet σ K) x ↔
      ¬ (D.finiteDimensionalReverseFactorLadderData
        (k := k) (S := S) σ τ K).ReachesBoundary
          (deletedInjectiveSet σ K) x := by
  apply FactorLadder.Data.terminatesWithoutBoundary_iff_not_reachesBoundary
  exact D.finiteDimensionalReverseFactorLadder_eventuallyZero
    (k := k) (S := S) σ τ K x

end Reverse

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
