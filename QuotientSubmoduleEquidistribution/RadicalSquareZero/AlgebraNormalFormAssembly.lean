import QuotientSubmoduleEquidistribution.RadicalSquareZero.RightCanonicalSeparatedAssembly
import QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedTriangularFiniteness
import QuotientSubmoduleEquidistribution.RepresentationTheory.SquareZeroMoritaBasicization

/-!
# Algebra-level radical-square-zero normal-form assembly

This file instantiates the right-module separated construction for an
arbitrary finite-dimensional algebra with square-zero Jacobson radical.
After Morita basicization and split quotient coordinates, the basic algebra
is a trivial square-zero extension.  Its opposite is the right-module normal
form, and the separated triangular algebra is representation-finite whenever
the original algebra is.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.RadicalSquareZero

open QuotientSubmoduleEquidistribution.MoritaBasicizationInterface
open QuotientSubmoduleEquidistribution.TrivSqZeroExtOpposite

universe u v

variable {K A : Type u}
variable [Field K]
variable [Ring A] [Algebra K A] [FiniteDimensional K A]

namespace CoordinatizedSquareZeroMoritaModel

variable (P :
  MoritaBasicizationInterface.CoordinatizedSquareZeroMoritaModel
    (K := K) (A := A))

local instance :
    IsArtinianRing P.squareZeroModel.basicModel.Carrier :=
  IsArtinianRing.of_finite K P.squareZeroModel.basicModel.Carrier

local instance :
    IsArtinianRing P.squareZeroModel.basicModel.Carrierᵐᵒᵖ :=
  QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K
    P.squareZeroModel.basicModel.Carrier

/-- The right-module square-zero normal form is Artinian. -/
instance normalOppositeIsArtinian :
    IsArtinianRing
      (TrivSqZeroExt (Fin P.vertexCount → K) P.RadicalBimodule)ᵐᵒᵖ :=
  (AlgEquiv.op P.squareZeroAlgEquiv).symm.toRingEquiv.isArtinianRing

/-- The left-module square-zero normal form is Artinian. -/
instance normalIsArtinian :
    IsArtinianRing
      (TrivSqZeroExt (Fin P.vertexCount → K) P.RadicalBimodule) :=
  P.squareZeroAlgEquiv.symm.toRingEquiv.isArtinianRing

/-- Exchanging the two radical actions preserves Artinianness. -/
instance reversedNormalIsArtinian :
    IsArtinianRing
      (TrivSqZeroExt (Fin P.vertexCount → K)
        (ReversedBimodule (Fin P.vertexCount → K)
          P.RadicalBimodule)) :=
  (oppositeRingEquiv
    (R := Fin P.vertexCount → K)
    (M := P.RadicalBimodule)).isArtinianRing

/-- A finite-length skeleton of the right-module normal form. -/
def normalRightSkeleton :
    IndecomposableSkeleton
      (TrivSqZeroExt (Fin P.vertexCount → K)
        P.RadicalBimodule)ᵐᵒᵖ
      (CanonicalIndecomposableIndex
        (TrivSqZeroExt (Fin P.vertexCount → K)
          P.RadicalBimodule)ᵐᵒᵖ) :=
  indecomposableSkeletonOfFiniteLength fun X ↦
    ((IsArtinianRing.tfae
      (TrivSqZeroExt (Fin P.vertexCount → K)
        P.RadicalBimodule)ᵐᵒᵖ X).out 0 3).mp
      (inferInstance : Module.Finite
        (TrivSqZeroExt (Fin P.vertexCount → K)
          P.RadicalBimodule)ᵐᵒᵖ X)

/-- A finite-length skeleton of the left-module normal form. -/
def normalLeftSkeleton :
    IndecomposableSkeleton
      (TrivSqZeroExt (Fin P.vertexCount → K)
        P.RadicalBimodule)
      (CanonicalIndecomposableIndex
        (TrivSqZeroExt (Fin P.vertexCount → K)
          P.RadicalBimodule)) :=
  indecomposableSkeletonOfFiniteLength fun X ↦
    ((IsArtinianRing.tfae
      (TrivSqZeroExt (Fin P.vertexCount → K)
        P.RadicalBimodule) X).out 0 3).mp
      (inferInstance : Module.Finite
        (TrivSqZeroExt (Fin P.vertexCount → K)
          P.RadicalBimodule) X)

/-- A finite-length skeleton after exchanging the two radical actions. -/
def reversedNormalSkeleton :
    IndecomposableSkeleton
      (TrivSqZeroExt (Fin P.vertexCount → K)
        (ReversedBimodule (Fin P.vertexCount → K)
          P.RadicalBimodule))
      (CanonicalIndecomposableIndex
        (TrivSqZeroExt (Fin P.vertexCount → K)
          (ReversedBimodule (Fin P.vertexCount → K)
            P.RadicalBimodule))) :=
  indecomposableSkeletonOfFiniteLength fun X ↦
    ((IsArtinianRing.tfae
      (TrivSqZeroExt (Fin P.vertexCount → K)
        (ReversedBimodule (Fin P.vertexCount → K)
          P.RadicalBimodule)) X).out 0 3).mp
      (inferInstance : Module.Finite
        (TrivSqZeroExt (Fin P.vertexCount → K)
          (ReversedBimodule (Fin P.vertexCount → K)
            P.RadicalBimodule)) X)

/-- The original right-module skeleton and the square-zero normal-form
skeleton are aligned by Morita basicization and the explicit algebra
normal form. -/
def sourceNormalAlignedEquivalence :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    IndecomposableSkeleton.AlignedEquivalence
      (rightIndecomposableSkeleton K A)
      (normalRightSkeleton P) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  exact IndecomposableSkeleton.Equivalence.alignedEquivalence
    (rightIndecomposableSkeleton K A)
    (normalRightSkeleton P) P.sourceRightFgEquivalence

/-- Right modules over `Aᵐᵒᵖ` are left modules over the double
opposite of `A`; the canonical double-opposite equivalence followed by the
Morita normal form identifies them with modules over the unreversed trivial
extension. -/
def sourceOppositeLeftFgEquivalence :
    FGModuleCat (Aᵐᵒᵖ)ᵐᵒᵖ ≌
      FGModuleCat
        (TrivSqZeroExt (Fin P.vertexCount → K)
          P.RadicalBimodule) :=
  (MoritaEquivalence.ofAlgEquiv
      (AlgEquiv.opOp K A)).finiteDimensionalFgEquivalence.symm.trans
    P.sourceLeftFgEquivalence

/-- The canonical right-module skeleton of the opposite algebra aligns with
the unreversed square-zero normal form. -/
def sourceOppositeNormalAlignedEquivalence :
    letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
    IndecomposableSkeleton.AlignedEquivalence
      (rightIndecomposableSkeleton K Aᵐᵒᵖ)
      (normalLeftSkeleton P) := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  exact IndecomposableSkeleton.Equivalence.alignedEquivalence
    (rightIndecomposableSkeleton K Aᵐᵒᵖ)
    (normalLeftSkeleton P) (sourceOppositeLeftFgEquivalence P)

/-- Representation-finiteness passes from the original algebra to the
right-module square-zero normal form. -/
theorem normalRight_isRepresentationFinite
    (hA : IsRightRepresentationFinite.{u, u, u} K A) :
    IsRepresentationFinite.{u, u}
      (TrivSqZeroExt (Fin P.vertexCount → K)
        P.RadicalBimodule)ᵐᵒᵖ := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  exact ((sourceNormalAlignedEquivalence P).labelEquiv.finite_iff).mp hA

/-- Representation-finiteness of `A` also passes to the unreversed normal
form through the opposite algebra. -/
theorem normalLeft_isRepresentationFinite
    (hA : IsRightRepresentationFinite.{u, u, u} K A) :
    IsRepresentationFinite.{u, u}
      (TrivSqZeroExt (Fin P.vertexCount → K)
        P.RadicalBimodule) := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  let hAop : IsRightRepresentationFinite.{u, u, u} K Aᵐᵒᵖ :=
    (rightRepresentationFinite_op_iff K A).mp hA
  exact
    ((sourceOppositeNormalAlignedEquivalence P).labelEquiv.finite_iff).mp
      hAop

/-- The exchanged-action normal form is representation-finite whenever the
original algebra is. -/
theorem reversedNormal_isRepresentationFinite
    (hA : IsRightRepresentationFinite.{u, u, u} K A) :
    IsRepresentationFinite.{u, u}
      (TrivSqZeroExt (Fin P.vertexCount → K)
        (ReversedBimodule (Fin P.vertexCount → K)
          P.RadicalBimodule)) := by
  let E := IndecomposableSkeleton.Equivalence.alignedEquivalence
    (normalRightSkeleton P) (reversedNormalSkeleton P)
    (fgEquivalence
      (R := Fin P.vertexCount → K)
      (M := P.RadicalBimodule))
  exact E.labelEquiv.finite_iff.mp
    (normalRight_isRepresentationFinite P hA)

/-- The separated triangular algebra attached to the right-module normal
form is representation-finite. -/
theorem rightSeparated_isRepresentationFinite
    (hA : IsRightRepresentationFinite.{u, u, u} K A) :
    IsRepresentationFinite.{u, u}
      (SeparatedTriangularAlgebra.Algebra
        (Fin P.vertexCount → K)
        (ReversedBimodule (Fin P.vertexCount → K)
          P.RadicalBimodule)) := by
  letI : Finite
      (CanonicalIndecomposableIndex
        (TrivSqZeroExt (Fin P.vertexCount → K)
          (ReversedBimodule (Fin P.vertexCount → K)
            P.RadicalBimodule))) :=
    reversedNormal_isRepresentationFinite P hA
  exact separatedAlgebra_isRepresentationFinite_of_finiteSkeleton
    (reversedNormalSkeleton P) fun X ↦
      ((IsArtinianRing.tfae
        (SeparatedTriangularAlgebra.Algebra
          (Fin P.vertexCount → K)
          (ReversedBimodule (Fin P.vertexCount → K)
            P.RadicalBimodule)) X).out 0 3).mp
        (inferInstance : Module.Finite
          (SeparatedTriangularAlgebra.Algebra
            (Fin P.vertexCount → K)
            (ReversedBimodule (Fin P.vertexCount → K)
              P.RadicalBimodule)) X)

/-- The separated triangular algebra for the unreversed normal form is also
representation-finite. -/
theorem leftSeparated_isRepresentationFinite
    (hA : IsRightRepresentationFinite.{u, u, u} K A) :
    IsRepresentationFinite.{u, u}
      (SeparatedTriangularAlgebra.Algebra
        (Fin P.vertexCount → K) P.RadicalBimodule) := by
  letI : Finite
      (CanonicalIndecomposableIndex
        (TrivSqZeroExt (Fin P.vertexCount → K)
          P.RadicalBimodule)) :=
    normalLeft_isRepresentationFinite P hA
  exact separatedAlgebra_isRepresentationFinite_of_finiteSkeleton
    (normalLeftSkeleton P) fun X ↦
      ((IsArtinianRing.tfae
        (SeparatedTriangularAlgebra.Algebra
          (Fin P.vertexCount → K) P.RadicalBimodule) X).out 0 3).mp
        (inferInstance : Module.Finite
          (SeparatedTriangularAlgebra.Algebra
            (Fin P.vertexCount → K) P.RadicalBimodule) X)

/-- Algebra-level Boolean-factor formula.  Any complete finite skeleton of
the separated triangular algebra has quotient polynomial equal to that of
the original algebra times one Boolean factor for every original simple. -/
theorem rightSeparatedLevelPolynomial_eq_source_mul
    (hA : IsRightRepresentationFinite.{u, u, u} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite
        (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
    ∀ {kappa : Type v} [Finite kappa]
      (tau : IndecomposableSkeleton.{u, v, u}
        (SeparatedTriangularAlgebra.Algebra
          (Fin P.vertexCount → K)
          (ReversedBimodule (Fin P.vertexCount → K)
            P.RadicalBimodule)) kappa),
      tau.qClosure.levelPolynomial =
        (rightIndecomposableSkeleton.{u, u, u} K A).qClosure.levelPolynomial *
          (1 + Polynomial.X) ^
            Nat.card
              (IndecomposableSkeleton.SimpleIndex
                (rightIndecomposableSkeleton.{u, u, u} K A)) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  intro kappa _ tau
  letI : Finite
      (CanonicalIndecomposableIndex
        (TrivSqZeroExt (Fin P.vertexCount → K)
          P.RadicalBimodule)ᵐᵒᵖ) :=
    normalRight_isRepresentationFinite P hA
  have hfactor :=
    rightSeparatedTargetLevelPolynomial_eq_original_mul
      (normalRightSkeleton P) tau
  have hpoly :=
    (sourceNormalAlignedEquivalence P).quotientLevelPolynomial_eq
  have hsimp :=
    (sourceNormalAlignedEquivalence P).natCard_simpleIndex_eq
  rw [← hpoly, ← hsimp] at hfactor
  exact hfactor

/-- Opposite-algebra form of the Boolean factor.  The unreversed triangular
model has quotient polynomial equal to that of `Aᵐᵒᵖ`, with the same
number of simple labels. -/
theorem leftSeparatedLevelPolynomial_eq_sourceOpposite_mul
    (hA : IsRightRepresentationFinite.{u, u, u} K A) :
    letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
    letI : Finite
        (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
      (rightRepresentationFinite_op_iff K A).mp hA
    ∀ {kappa : Type v} [Finite kappa]
      (tau : IndecomposableSkeleton.{u, v, u}
        (SeparatedTriangularAlgebra.Algebra
          (Fin P.vertexCount → K) P.RadicalBimodule) kappa),
      tau.qClosure.levelPolynomial =
        (rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ).qClosure.levelPolynomial *
          (1 + Polynomial.X) ^
            Nat.card
              (IndecomposableSkeleton.SimpleIndex
                (rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ)) := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
    (rightRepresentationFinite_op_iff K A).mp hA
  intro kappa _ tau
  letI : Finite
      (CanonicalIndecomposableIndex
        (TrivSqZeroExt (Fin P.vertexCount → K)
          P.RadicalBimodule)) :=
    normalLeft_isRepresentationFinite P hA
  have hfactor := separatedTargetLevelPolynomial_eq_original_mul_ofSkeleton
    (normalLeftSkeleton P) tau
  have hpoly :=
    (sourceOppositeNormalAlignedEquivalence P).quotientLevelPolynomial_eq
  have hsimp :=
    (sourceOppositeNormalAlignedEquivalence P).natCard_simpleIndex_eq
  rw [← hpoly, ← hsimp] at hfactor
  exact hfactor

end CoordinatizedSquareZeroMoritaModel

end QuotientSubmoduleEquidistribution.RadicalSquareZero
