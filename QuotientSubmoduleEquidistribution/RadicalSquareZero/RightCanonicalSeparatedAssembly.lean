import QuotientSubmoduleEquidistribution.RadicalSquareZero.CanonicalSeparatedAssembly
import QuotientSubmoduleEquidistribution.RepresentationTheory.MoritaConsequences
import QuotientSubmoduleEquidistribution.RepresentationTheory.SimpleEquivalenceTransport
import QuotientSubmoduleEquidistribution.RepresentationTheory.SkeletonAlignment
import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtOpposite

/-!
# Canonical separated assembly for right modules

The structural separated-data theorem is naturally phrased for left modules
over a trivial square-zero extension.  The paper counts right modules.  This
file crosses that convention seam: the opposite extension is identified with
the extension by the bimodule with exchanged actions, and the Boolean factor
is transported back through the induced equivalence of finite module
categories.
-/

set_option autoImplicit false

noncomputable section

namespace QuotientSubmoduleEquidistribution.RadicalSquareZero

open QuotientSubmoduleEquidistribution.TrivSqZeroExtOpposite

universe u v x y

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]
variable [Module.Finite Sᵐᵒᵖ J]
variable [IsSemisimpleRing S]
variable [IsNoetherianRing (TrivSqZeroExt S J)ᵐᵒᵖ]
variable [IsArtinianRing (TrivSqZeroExt S J)ᵐᵒᵖ]
variable [IsNoetherianRing
  (TrivSqZeroExt S (ReversedBimodule S J))]
variable [IsArtinianRing
  (TrivSqZeroExt S (ReversedBimodule S J))]
variable [IsNoetherianRing
  (SeparatedTriangularAlgebra.Algebra S (ReversedBimodule S J))]

/-- Right-module form of the canonical separated Boolean factor.  No
objectwise comparison data is assumed: the opposite-extension ring
equivalence, completeness of the two skeletons, and preservation of simple
objects construct all required alignments. -/
theorem rightSeparatedTargetLevelPolynomial_eq_original_mul
    {iota : Type x} [Finite iota]
    (rho : IndecomposableSkeleton.{max u v, x, max u v}
      (TrivSqZeroExt S J)ᵐᵒᵖ iota)
    {kappa : Type y} [Finite kappa]
    (tau : IndecomposableSkeleton.{max u v, y, max u v}
      (SeparatedTriangularAlgebra.Algebra S (ReversedBimodule S J))
      kappa) :
    tau.qClosure.levelPolynomial =
      rho.qClosure.levelPolynomial *
        (1 + Polynomial.X) ^ Nat.card rho.SimpleIndex := by
  let hfinite : ∀ X : FGModuleCat.{max u v}
      (TrivSqZeroExt S (ReversedBimodule S J)),
      IsFiniteLength
        (TrivSqZeroExt S (ReversedBimodule S J)) X :=
    fun X ↦ ((IsArtinianRing.tfae
      (TrivSqZeroExt S (ReversedBimodule S J)) X).out 0 3).mp
        (inferInstance : Module.Finite
          (TrivSqZeroExt S (ReversedBimodule S J)) X)
  let rhoReversed := indecomposableSkeletonOfFiniteLength hfinite
  let E : IndecomposableSkeleton.AlignedEquivalence rho rhoReversed :=
    IndecomposableSkeleton.Equivalence.alignedEquivalence
      rho rhoReversed
      (fgEquivalence (R := S) (M := J))
  letI : Finite
      (CanonicalIndecomposableIndex.{max u v, max u v}
        (TrivSqZeroExt S (ReversedBimodule S J))) :=
    E.labelEquiv.finite_iff.mp inferInstance
  calc
    tau.qClosure.levelPolynomial =
        rhoReversed.qClosure.levelPolynomial *
          (1 + Polynomial.X) ^
            Nat.card rhoReversed.SimpleIndex :=
      separatedTargetLevelPolynomial_eq_original_mul_ofSkeleton
        rhoReversed tau
    _ = rho.qClosure.levelPolynomial *
          (1 + Polynomial.X) ^ Nat.card rho.SimpleIndex := by
      rw [← E.quotientLevelPolynomial_eq,
        ← E.natCard_simpleIndex_eq]

end QuotientSubmoduleEquidistribution.RadicalSquareZero
