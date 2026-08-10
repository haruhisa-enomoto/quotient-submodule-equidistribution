import OpConjecture.RepresentationTheory.ArtinDualityInterface
import OpConjecture.RepresentationTheory.QuotientSkeletonCore

/-!
# The bottom-two theorem over an Artinian ring

This file combines exact-annihilator inflation, faithful-core rigidity, and
the abstract Artin-duality interface.  It provides the paper's general
annihilator-preserving size-two endpoint relative to that explicit interface,
without classifying any concrete algebra or any of its modules.

The one explicit input is the standard finite-module anti-equivalence for
every factor ring.  Generic stable descent derives the stable equivalence
from it.  Mathlib currently has no construction of that finite-module
duality for an arbitrary Artin algebra over a commutative Artinian base; the
maintained finite-dimensional vector-space duality is one instance.

At the weaker bare-left-Artinian-ring level the API also names ambient
opposite-Noetherianity.  It descends automatically to all factors, and the
conventional module-finite Artin-algebra hypotheses discharge it below.
-/

noncomputable section

open Set

namespace OpConjecture.ArtinBottomTwo

universe u

open OpConjecture.AnnihilatorInflation
open OpConjecture.IndecomposableSkeleton
open OpConjecture.IndecomposableSkeleton.FaithfulCore

/-- Opposite-Noetherianity descends through a two-sided quotient. -/
theorem factorOppositeNoetherian_of_oppositeNoetherian
    (R : Type u) [Ring R] [IsNoetherianRing Rᵐᵒᵖ]
    (I : TwoSidedIdeal R) :
    IsNoetherianRing (Quotient.Factor I)ᵐᵒᵖ := by
  exact isNoetherianRing_of_surjective Rᵐᵒᵖ _
    (RingHom.op (Ideal.Quotient.mk I.asIdeal))
    (by
      intro y
      obtain ⟨x, hx⟩ :=
        Ideal.Quotient.mk_surjective (MulOpposite.unop y)
      exact ⟨MulOpposite.op x, by
        simpa using congrArg MulOpposite.op hx⟩)

variable {R : Type u} [Ring R] [IsArtinianRing R]
  [IsNoetherianRing Rᵐᵒᵖ]

local instance (I : TwoSidedIdeal R) :
    IsNoetherianRing (Quotient.Factor I)ᵐᵒᵖ :=
  factorOppositeNoetherian_of_oppositeNoetherian R I

/-- The canonical factor skeleton used in the Artin-level theorem. -/
abbrev factorSkeleton (I : TwoSidedIdeal R) :=
  OpConjecture.QuotientSkeletonAlignment.artinFactorSkeleton R I

/-- The paper's ideal parameter space
`{I | d(R/I) = 2}`, expressed using the cotorsionless Ringel core. -/
abbrev CoreTwoIdeal :=
  FaithfulCore.CoreTwoIdeal
    (fun I : TwoSidedIdeal R ↦ factorSkeleton (R := R) I)

variable {ι : Type (u + 1)}
  (σ : IndecomposableSkeleton.{u, u + 1, u} R ι)
  (duality : ∀ I : TwoSidedIdeal R,
    OpConjecture.ArtinDuality.Data (Quotient.Factor I))

/-- Ringel's correspondence on every canonical factor skeleton. -/
def factorRingelCoreEquiv (I : TwoSidedIdeal R) :=
  OpConjecture.ArtinDuality.ringelCoreEquiv
    (duality I) (factorSkeleton (R := R) I)

/-- Every quotient-closed pair is parametrized by its exact annihilator,
which is precisely a factor whose common Ringel core has size two. -/
def quotientPairIdealEquiv :
    ArtinQPair σ ≃ CoreTwoIdeal (R := R) :=
  qPairCoreTwoIdealEquiv σ
    (fun I : TwoSidedIdeal R ↦ factorSkeleton (R := R) I)
    (fun I ↦
      OpConjecture.QuotientSkeletonAlignment.artinInflationData σ I)
    (fun I ↦
      OpConjecture.ArtinDuality.faithfulNormalForm
        (duality I) (factorSkeleton (R := R) I))
    (factorRingelCoreEquiv duality)

/-- Every submodule-closed pair has the same ideal parametrization. -/
def submodulePairIdealEquiv :
    ArtinSPair σ ≃ CoreTwoIdeal (R := R) :=
  sPairCoreTwoIdealEquiv σ
    (fun I : TwoSidedIdeal R ↦ factorSkeleton (R := R) I)
    (fun I ↦
      OpConjecture.QuotientSkeletonAlignment.artinInflationData σ I)
    (fun I ↦
      OpConjecture.ArtinDuality.faithfulNormalForm
        (duality I) (factorSkeleton (R := R) I))
    (factorRingelCoreEquiv duality)

/-- The general bottom-two bijection, obtained by keeping the exact
annihilator fixed and interchanging the two factor cores. -/
def pairEquiv : ArtinQPair σ ≃ ArtinSPair σ :=
  (quotientPairIdealEquiv σ duality).trans
    (submodulePairIdealEquiv σ duality).symm

@[simp]
theorem quotientPairIdealEquiv_ideal (C : ArtinQPair σ) :
    (quotientPairIdealEquiv σ duality C).1 =
      supportAnnihilator σ.obj
        ((C.1 : σ.qClosure.Closeds) : Set ι) :=
  rfl

@[simp]
theorem submodulePairIdealEquiv_ideal (C : ArtinSPair σ) :
    (submodulePairIdealEquiv σ duality C).1 =
      supportAnnihilator σ.obj
        ((C.1 : σ.sClosure.Closeds) : Set ι) :=
  rfl

/-- The bottom-two bijection preserves the common annihilator literally. -/
theorem pairEquiv_annihilator (C : ArtinQPair σ) :
    supportAnnihilator σ.obj
        (((pairEquiv σ duality C).1 : σ.sClosure.Closeds) : Set ι) =
      supportAnnihilator σ.obj
        ((C.1 : σ.qClosure.Closeds) : Set ι) := by
  have h := congrArg Subtype.val
    ((submodulePairIdealEquiv σ duality).apply_symm_apply
      (quotientPairIdealEquiv σ duality C))
  simpa only [pairEquiv, Equiv.trans_apply,
    submodulePairIdealEquiv_ideal,
    quotientPairIdealEquiv_ideal] using h

/-- For a conventional Artin algebra, ambient opposite-Noetherianity is
automatic.  More generally, a commutative Noetherian base and
module-finiteness suffice. -/
theorem oppositeNoetherian_of_finiteOverCommNoetherian
    (k R : Type u) [CommRing k] [IsNoetherianRing k]
    [Ring R] [Algebra k R] [Module.Finite k R] :
    IsNoetherianRing Rᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- The same module-finite hypotheses therefore supply opposite-Noetherianity
for every two-sided factor. -/
theorem factorOppositeNoetherian_of_finiteOverCommNoetherian
    (k R : Type u) [CommRing k] [IsNoetherianRing k]
    [Ring R] [Algebra k R] [Module.Finite k R]
    (I : TwoSidedIdeal R) :
    IsNoetherianRing (Quotient.Factor I)ᵐᵒᵖ := by
  letI : IsNoetherianRing Rᵐᵒᵖ :=
    oppositeNoetherian_of_finiteOverCommNoetherian k R
  exact factorOppositeNoetherian_of_oppositeNoetherian R I

section FiniteDimensional

/-- Finite-dimensionality over a field supplies the opposite-Noetherian
factor instance. -/
theorem factorOppositeNoetherian_of_finiteDimensional
    (K R : Type u) [Field K] [Ring R] [Algebra K R]
    [FiniteDimensional K R] (I : TwoSidedIdeal R) :
    IsNoetherianRing (Quotient.Factor I)ᵐᵒᵖ :=
  factorOppositeNoetherian_of_finiteOverCommNoetherian K R I

variable (K R : Type u) [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  {ι : Type (u + 1)}
  (σ : IndecomposableSkeleton.{u, u + 1, u} R ι)

/-- Unconditional finite-dimensional specialization of the bottom-two
bijection.  No duality package is supplied by the caller. -/
def finiteDimensionalPairEquiv : ArtinQPair σ ≃ ArtinSPair σ := by
  letI : IsArtinianRing R := IsArtinianRing.of_finite K R
  letI : IsNoetherianRing Rᵐᵒᵖ :=
    oppositeNoetherian_of_finiteOverCommNoetherian K R
  exact pairEquiv σ
    (fun _ ↦ OpConjecture.ArtinDuality.ofFiniteDimensional K)

/-- The finite-dimensional specialization preserves the annihilator. -/
theorem finiteDimensionalPairEquiv_annihilator (C : ArtinQPair σ) :
    supportAnnihilator σ.obj
        (((finiteDimensionalPairEquiv K R σ C).1 :
          σ.sClosure.Closeds) : Set ι) =
      supportAnnihilator σ.obj
        ((C.1 : σ.qClosure.Closeds) : Set ι) := by
  letI : IsArtinianRing R := IsArtinianRing.of_finite K R
  letI : IsNoetherianRing Rᵐᵒᵖ :=
    oppositeNoetherian_of_finiteOverCommNoetherian K R
  exact pairEquiv_annihilator σ
    (fun _ ↦ OpConjecture.ArtinDuality.ofFiniteDimensional K) C

end FiniteDimensional

end OpConjecture.ArtinBottomTwo
