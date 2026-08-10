import OpConjecture.RepresentationTheory.ArtinBottomTwo
import OpConjecture.RepresentationTheory.ArtinFaithfulTriples

/-!
# Direct bottom-three assembly over an Artinian ring

This file specializes the abstract faithful-triple split to the canonical
skeletons of all two-sided factors.  It isolates the sole remaining
size-three input: a common parametrization of faithful triples over factors
whose Ringel core has size two.  In the paper that common parameter type is
the subtype of ideals whose factor is Morita equivalent to `kA₂`.

No concrete factor classification is assumed or carried out here.
-/

noncomputable section

open Set

namespace OpConjecture.ArtinBottomThree

universe u w

open OpConjecture.AnnihilatorInflation
open OpConjecture.IndecomposableSkeleton
open OpConjecture.IndecomposableSkeleton.FaithfulCore

variable {R : Type u} [Ring R] [IsArtinianRing R]
  [IsNoetherianRing Rᵐᵒᵖ]

local instance (I : TwoSidedIdeal R) :
    IsNoetherianRing (Quotient.Factor I)ᵐᵒᵖ :=
  OpConjecture.ArtinBottomTwo.factorOppositeNoetherian_of_oppositeNoetherian
    R I

/-- The canonical factor skeleton used throughout the direct formula. -/
abbrev factorSkeleton (I : TwoSidedIdeal R) :=
  OpConjecture.ArtinBottomTwo.factorSkeleton (R := R) I

/-- Ideals whose canonical factor has common Ringel core size three. -/
abbrev CoreThreeFactorIdeal :=
  CoreThreeIdeal (fun I : TwoSidedIdeal R ↦ factorSkeleton (R := R) I)

/-- The still-unclassified faithful quotient triples over core-two factors. -/
abbrev CoreTwoFaithfulQTripleFiber :=
  CoreTwoFaithfulQTriples
    (fun I : TwoSidedIdeal R ↦ factorSkeleton (R := R) I)

/-- The still-unclassified faithful submodule triples over core-two factors. -/
abbrev CoreTwoFaithfulSTripleFiber :=
  CoreTwoFaithfulSTriples
    (fun I : TwoSidedIdeal R ↦ factorSkeleton (R := R) I)

variable {ι : Type (u + 1)}
  (σ : IndecomposableSkeleton.{u, u + 1, u} R ι)
  (duality : ∀ I : TwoSidedIdeal R,
    OpConjecture.ArtinDuality.Data (Quotient.Factor I))

/-- Ringel's core equivalence on every canonical factor skeleton. -/
def factorRingelCoreEquiv (I : TwoSidedIdeal R) :=
  OpConjecture.ArtinDuality.ringelCoreEquiv
    (duality I) (factorSkeleton (R := R) I)

/-- The quotient-closed third level splits into core-three factor ideals and
the residual faithful triples over core-two factors. -/
def quotientTripleCoreSplitEquiv :
    ArtinQTriple σ ≃
      CoreThreeFactorIdeal (R := R) ⊕
        CoreTwoFaithfulQTripleFiber (R := R) :=
  qTripleCoreSplitEquiv σ
    (fun I : TwoSidedIdeal R ↦ factorSkeleton (R := R) I)
    (fun I ↦
      OpConjecture.QuotientSkeletonAlignment.artinInflationData σ I)
    (fun I ↦
      OpConjecture.ArtinDuality.faithfulNormalForm
        (duality I) (factorSkeleton (R := R) I))
    (factorRingelCoreEquiv duality)

/-- The identical direct split on the submodule side. -/
def submoduleTripleCoreSplitEquiv :
    ArtinSTriple σ ≃
      CoreThreeFactorIdeal (R := R) ⊕
        CoreTwoFaithfulSTripleFiber (R := R) :=
  sTripleCoreSplitEquiv σ
    (fun I : TwoSidedIdeal R ↦ factorSkeleton (R := R) I)
    (fun I ↦
      OpConjecture.QuotientSkeletonAlignment.artinInflationData σ I)
    (fun I ↦
      OpConjecture.ArtinDuality.faithfulNormalForm
        (duality I) (factorSkeleton (R := R) I))
    (factorRingelCoreEquiv duality)

include duality in
/-- Before the core-two classification, the quotient-side count already has
the exact two-summand form. -/
theorem quotientTriple_natCard_split [Finite ι] :
    Nat.card (ArtinQTriple σ) =
      Nat.card (CoreThreeFactorIdeal (R := R)) +
        Nat.card (CoreTwoFaithfulQTripleFiber (R := R)) :=
  qTriple_natCard_split σ
    (fun I : TwoSidedIdeal R ↦ factorSkeleton (R := R) I)
    (fun I ↦
      OpConjecture.QuotientSkeletonAlignment.artinInflationData σ I)
    (fun I ↦
      OpConjecture.ArtinDuality.faithfulNormalForm
        (duality I) (factorSkeleton (R := R) I))
    (factorRingelCoreEquiv duality)

include duality in
/-- The corresponding exact submodule-side count. -/
theorem submoduleTriple_natCard_split [Finite ι] :
    Nat.card (ArtinSTriple σ) =
      Nat.card (CoreThreeFactorIdeal (R := R)) +
        Nat.card (CoreTwoFaithfulSTripleFiber (R := R)) :=
  sTriple_natCard_split σ
    (fun I : TwoSidedIdeal R ↦ factorSkeleton (R := R) I)
    (fun I ↦
      OpConjecture.QuotientSkeletonAlignment.artinInflationData σ I)
    (fun I ↦
      OpConjecture.ArtinDuality.faithfulNormalForm
        (duality I) (factorSkeleton (R := R) I))
    (factorRingelCoreEquiv duality)

/-- A quotient-side classification of the residual stratum by `P` produces
the exact paper-shaped ideal parametrization. -/
def quotientTripleIdealEquiv
    {P : Type w}
    (small : CoreTwoFaithfulQTripleFiber (R := R) ≃ P) :
    ArtinQTriple σ ≃ CoreThreeFactorIdeal (R := R) ⊕ P :=
  qTripleIdealEquivOfCoreTwoParametrization σ
    (fun I : TwoSidedIdeal R ↦ factorSkeleton (R := R) I)
    (fun I ↦
      OpConjecture.QuotientSkeletonAlignment.artinInflationData σ I)
    (fun I ↦
      OpConjecture.ArtinDuality.faithfulNormalForm
        (duality I) (factorSkeleton (R := R) I))
    (factorRingelCoreEquiv duality) small

/-- The submodule-side version of the same classification interface. -/
def submoduleTripleIdealEquiv
    {P : Type w}
    (small : CoreTwoFaithfulSTripleFiber (R := R) ≃ P) :
    ArtinSTriple σ ≃ CoreThreeFactorIdeal (R := R) ⊕ P :=
  sTripleIdealEquivOfCoreTwoParametrization σ
    (fun I : TwoSidedIdeal R ↦ factorSkeleton (R := R) I)
    (fun I ↦
      OpConjecture.QuotientSkeletonAlignment.artinInflationData σ I)
    (fun I ↦
      OpConjecture.ArtinDuality.faithfulNormalForm
        (duality I) (factorSkeleton (R := R) I))
    (factorRingelCoreEquiv duality) small

include σ duality in
/-- Any parameter type classifying the quotient residual stratum is finite
when the ambient skeleton is finite. -/
theorem finite_quotientTripleParameter
    [Finite ι] {P : Type w}
    (small : CoreTwoFaithfulQTripleFiber (R := R) ≃ P) :
    Finite P :=
  small.finite_iff.mp <|
    finite_coreTwoFaithfulQTriples σ
      (fun I : TwoSidedIdeal R ↦ factorSkeleton (R := R) I)
      (fun I ↦
        OpConjecture.QuotientSkeletonAlignment.artinInflationData σ I)
      (fun I ↦
        OpConjecture.ArtinDuality.faithfulNormalForm
          (duality I) (factorSkeleton (R := R) I))
      (factorRingelCoreEquiv duality)

include duality in
/-- The quotient-side paper-shaped third-level count for any supplied
classification parameter type. -/
theorem quotientTriple_natCard_formula
    [Finite ι] {P : Type w}
    (small : CoreTwoFaithfulQTripleFiber (R := R) ≃ P) :
    Nat.card (ArtinQTriple σ) =
      Nat.card (CoreThreeFactorIdeal (R := R)) + Nat.card P := by
  rw [quotientTriple_natCard_split σ duality, Nat.card_congr small]

include duality in
/-- The submodule-side formula with the same prospective parameter type. -/
theorem submoduleTriple_natCard_formula
    [Finite ι] {P : Type w}
    (small : CoreTwoFaithfulSTripleFiber (R := R) ≃ P) :
    Nat.card (ArtinSTriple σ) =
      Nat.card (CoreThreeFactorIdeal (R := R)) + Nat.card P := by
  rw [submoduleTriple_natCard_split σ duality, Nat.card_congr small]

/-- Common residual parametrizations give the direct bottom-three
quotient--submodule equivalence. -/
def tripleEquiv
    {P : Type w}
    (qSmall : CoreTwoFaithfulQTripleFiber (R := R) ≃ P)
    (sSmall : CoreTwoFaithfulSTripleFiber (R := R) ≃ P) :
    ArtinQTriple σ ≃ ArtinSTriple σ :=
  (quotientTripleIdealEquiv σ duality qSmall).trans
    (submoduleTripleIdealEquiv σ duality sSmall).symm

include duality in
/-- The corresponding numerical equality at level three. -/
theorem triple_natCard_eq
    {P : Type w}
    (qSmall : CoreTwoFaithfulQTripleFiber (R := R) ≃ P)
    (sSmall : CoreTwoFaithfulSTripleFiber (R := R) ≃ P) :
    Nat.card (ArtinQTriple σ) = Nat.card (ArtinSTriple σ) :=
  Nat.card_congr (tripleEquiv σ duality qSmall sSmall)

end OpConjecture.ArtinBottomThree
