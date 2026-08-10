import QuotientSubmoduleEquidistribution.RepresentationTheory.A2SeparatedCore
import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulCoreMoritaTransport
import QuotientSubmoduleEquidistribution.RepresentationTheory.MoritaA2ForwardRecognition

/-!
# Closing the fixed Morita-`A₂` boundary

The separated one-arrow algebra supplies the fixed node required by the
abstract bottom-three boundary.  Its intrinsic classification gives three
indecomposables and two simples, while its faithful quotient core has size
two.  Morita invariance transports the last fact to every factor recognized
by the boundary theorem.  Thus all inputs to the paper-shaped bottom-three
classification and cardinality formulas are automatic for this fixed node.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.A2MoritaBoundaryClosure

universe u

open QuotientSubmoduleEquidistribution.AnnihilatorInflation
open QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore

variable (K : Type u) [Field K] [IsAlgClosed K]
  {R : Type u} [Ring R] [Algebra K R]
  [IsArtinianRing R] [IsNoetherianRing Rᵐᵒᵖ]

variable {iota : Type (u + 1)}
  (sigma : IndecomposableSkeleton.{u, u + 1, u} R iota)

omit [IsAlgClosed K] [IsNoetherianRing Rᵐᵒᵖ] in
/-- Every factor Morita equivalent to the fixed separated `A₂` node has
quotient faithful core of cardinality two. -/
theorem quotientCore_ncard_eq_two_of_isMoritaA2Factor
    [FiniteDimensional K R]
    (I : TwoSidedIdeal R)
    (hI : QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary.IsMoritaA2Factor
      K (QuotientSubmoduleEquidistribution.A2Separated.node K) I) :
    (quotientCore
        (QuotientSubmoduleEquidistribution.ArtinBottomThree.factorSkeleton (R := R) I) :
      Set (CanonicalIndecomposableIndex.{u, u}
        (Quotient.Factor I))).ncard = 2 := by
  obtain ⟨m⟩ := hI
  letI : IsArtinianRing (Quotient.Factor I) :=
    IsArtinianRing.of_finite K (Quotient.Factor I)
  letI : IsNoetherianRing (Quotient.Factor I) :=
    IsNoetherianRing.of_finite K (Quotient.Factor I)
  letI : IsArtinianRing (QuotientSubmoduleEquidistribution.A2Separated.node K).Carrier :=
    IsArtinianRing.of_finite K (QuotientSubmoduleEquidistribution.A2Separated.node K).Carrier
  let E := MoritaEquivalence.alignedFgEquivalence m
    (QuotientSubmoduleEquidistribution.ArtinBottomThree.factorSkeleton (R := R) I)
    (QuotientSubmoduleEquidistribution.A2Separated.node K).skeleton
  calc
    (quotientCore
        (QuotientSubmoduleEquidistribution.ArtinBottomThree.factorSkeleton (R := R) I) :
      Set (CanonicalIndecomposableIndex.{u, u}
        (Quotient.Factor I))).ncard =
        (quotientCore (QuotientSubmoduleEquidistribution.A2Separated.node K).skeleton :
          Set (QuotientSubmoduleEquidistribution.A2Separated.node K).Index).ncard :=
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.quotientCore_ncard_eq
        (QuotientSubmoduleEquidistribution.ArtinBottomThree.factorSkeleton (R := R) I)
        (QuotientSubmoduleEquidistribution.A2Separated.node K).skeleton E
    _ = 2 := by
      change
        (quotientCore (QuotientSubmoduleEquidistribution.A2Separated.sigma K) :
          Set (CanonicalIndecomposableIndex.{u, u}
            (QuotientSubmoduleEquidistribution.A2Separated.Triangular K))).ncard = 2
      exact QuotientSubmoduleEquidistribution.A2Separated.quotientCore_ncard_eq_two K

variable (duality : ∀ I : TwoSidedIdeal R,
  ArtinDuality.Data (Quotient.Factor I))

/-- All local classification data required at the bottom-three boundary,
specialized to the fixed separated one-arrow node. -/
def classificationData
    [FiniteDimensional K R] [Finite iota] :
    QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary.ClassificationData
      K (QuotientSubmoduleEquidistribution.A2Separated.node K) (R := R) :=
  QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary.ClassificationData.ofTriangularRecognition
    K (QuotientSubmoduleEquidistribution.A2Separated.node K) sigma duality
    (by
      change Nat.card
        (CanonicalIndecomposableIndex.{u, u}
          (QuotientSubmoduleEquidistribution.A2Separated.Triangular K)) = 3
      exact QuotientSubmoduleEquidistribution.A2Separated.natCard_canonicalIndex_eq_three K)
    (by
      change Nat.card (QuotientSubmoduleEquidistribution.A2Separated.sigma K).SimpleIndex = 2
      exact QuotientSubmoduleEquidistribution.A2Separated.natCard_simpleIndex_eq_two K)
    ⟨by
      change QuotientSubmoduleEquidistribution.A2Triangular.Model K ≃ₐ[K]
        QuotientSubmoduleEquidistribution.A2Separated.Triangular K
      exact QuotientSubmoduleEquidistribution.A2Separated.modelAlgEquiv K⟩
    (quotientCore_ncard_eq_two_of_isMoritaA2Factor K)

/-- Paper-shaped quotient parametrization with no residual local
classification premise. -/
def quotientTripleIdealEquiv
    [FiniteDimensional K R] [Finite iota] :
    ArtinQTriple sigma ≃
      QuotientSubmoduleEquidistribution.ArtinBottomThree.CoreThreeFactorIdeal (R := R) ⊕
        QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary.MoritaA2FactorIdeal
          K (QuotientSubmoduleEquidistribution.A2Separated.node K) (R := R) :=
  QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary.quotientTripleIdealEquiv
    K (QuotientSubmoduleEquidistribution.A2Separated.node K) sigma duality
      (classificationData K sigma duality)

/-- Paper-shaped submodule parametrization with the same two ideal
summands. -/
def submoduleTripleIdealEquiv
    [FiniteDimensional K R] [Finite iota] :
    ArtinSTriple sigma ≃
      QuotientSubmoduleEquidistribution.ArtinBottomThree.CoreThreeFactorIdeal (R := R) ⊕
        QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary.MoritaA2FactorIdeal
          K (QuotientSubmoduleEquidistribution.A2Separated.node K) (R := R) :=
  QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary.submoduleTripleIdealEquiv
    K (QuotientSubmoduleEquidistribution.A2Separated.node K) sigma duality
      (classificationData K sigma duality)

/-- Direct quotient--submodule equivalence at level three. -/
def tripleEquiv
    [FiniteDimensional K R] [Finite iota] :
    ArtinQTriple sigma ≃ ArtinSTriple sigma :=
  QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary.tripleEquiv
    K (QuotientSubmoduleEquidistribution.A2Separated.node K) sigma duality
      (classificationData K sigma duality)

include duality in
/-- Exact quotient-side bottom-three formula for the fixed node. -/
theorem quotientTriple_natCard_formula
    [FiniteDimensional K R] [Finite iota] :
    Nat.card (ArtinQTriple sigma) =
      Nat.card (QuotientSubmoduleEquidistribution.ArtinBottomThree.CoreThreeFactorIdeal (R := R)) +
        Nat.card
          (QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary.MoritaA2FactorIdeal
            K (QuotientSubmoduleEquidistribution.A2Separated.node K) (R := R)) :=
  QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary.quotientTriple_natCard_formula
    K (QuotientSubmoduleEquidistribution.A2Separated.node K) sigma duality
      (classificationData K sigma duality)

include duality in
/-- Exact submodule-side bottom-three formula for the fixed node. -/
theorem submoduleTriple_natCard_formula
    [FiniteDimensional K R] [Finite iota] :
    Nat.card (ArtinSTriple sigma) =
      Nat.card (QuotientSubmoduleEquidistribution.ArtinBottomThree.CoreThreeFactorIdeal (R := R)) +
        Nat.card
          (QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary.MoritaA2FactorIdeal
            K (QuotientSubmoduleEquidistribution.A2Separated.node K) (R := R)) :=
  QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary.submoduleTriple_natCard_formula
    K (QuotientSubmoduleEquidistribution.A2Separated.node K) sigma duality
      (classificationData K sigma duality)

include duality in
/-- Numerical equality of the two level-three sides. -/
theorem triple_natCard_eq
    [FiniteDimensional K R] [Finite iota] :
    Nat.card (ArtinQTriple sigma) = Nat.card (ArtinSTriple sigma) :=
  QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary.triple_natCard_eq
    K (QuotientSubmoduleEquidistribution.A2Separated.node K) sigma duality
      (classificationData K sigma duality)

end QuotientSubmoduleEquidistribution.A2MoritaBoundaryClosure
