import QuotientSubmoduleEquidistribution.RadicalSquareZero.AlgebraNormalFormAssembly
import QuotientSubmoduleEquidistribution.RepresentationDirected.AlgebraEndpoint
import QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedTriangularProjectiveBoundary
import QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedTriangularOpposite

/-!
# Representation-directed interface for radical-square-zero algebras

The separated triangular algebra of a representation-finite
radical-square-zero algebra is finite.  Its projective radicals are supported
on the semisimple sink side, so a classification-free Auslander--Reiten
argument proves that it is representation-directed.  The general directed
theorem then identifies its quotient and submodule polynomials.
Contragredient duality and the explicit opposite triangular-algebra
equivalence identify the quotient polynomials for the two separated
orientations.

No root system, Dynkin classification, Weyl-group polynomial, longest
element, or ORT parametrization is used.
-/

set_option autoImplicit false

noncomputable section

open scoped RightActions

namespace QuotientSubmoduleEquidistribution.RadicalSquareZero

open Polynomial
open QuotientSubmoduleEquidistribution.MoritaBasicizationInterface
open QuotientSubmoduleEquidistribution.TrivSqZeroExtOpposite

universe u

variable {K A : Type u}
variable [Field K] [IsAlgClosed K]
variable [Ring A] [Algebra K A] [FiniteDimensional K A]

namespace CoordinatizedSquareZeroMoritaModel

variable (P : CoordinatizedSquareZeroMoritaModel (K := K) (A := A))

local instance :
    IsArtinianRing P.squareZeroModel.basicModel.Carrier :=
  IsArtinianRing.of_finite K P.squareZeroModel.basicModel.Carrier

/-- The unreversed separated triangular algebra. -/
abbrev OriginalSeparatedAlgebra :=
  SeparatedTriangularAlgebra.Algebra
    (Fin P.vertexCount → K) P.RadicalBimodule

/-- The separated triangular algebra after exchanging the radical actions. -/
abbrev ReversedSeparatedAlgebra :=
  SeparatedTriangularAlgebra.Algebra
    (Fin P.vertexCount → K)
    (ReversedBimodule (Fin P.vertexCount → K) P.RadicalBimodule)

local instance originalSeparatedIdealKModule :
    Module K
      (SeparatedTriangularAlgebra.SeparatedIdeal
        (Fin P.vertexCount → K) P.RadicalBimodule) :=
  SeparatedTriangularAlgebra.SeparatedIdeal.equiv.module K

local instance reversedBimoduleKModule :
    Module K
      (ReversedBimodule (Fin P.vertexCount → K)
        P.RadicalBimodule) :=
  ReversedBimodule.equiv.module K

local instance reversedSeparatedIdealKModule :
    Module K
      (SeparatedTriangularAlgebra.SeparatedIdeal
        (Fin P.vertexCount → K)
        (ReversedBimodule (Fin P.vertexCount → K)
          P.RadicalBimodule)) :=
  SeparatedTriangularAlgebra.SeparatedIdeal.equiv.module K

local instance originalSeparatedIdealLeftTower :
    IsScalarTower K
      ((Fin P.vertexCount → K) × (Fin P.vertexCount → K))
      (SeparatedTriangularAlgebra.SeparatedIdeal
        (Fin P.vertexCount → K) P.RadicalBimodule) where
  smul_assoc k s j := by
    apply SeparatedTriangularAlgebra.SeparatedIdeal.ext
    change (k • s.1) • j.val = k • (s.1 • j.val)
    exact smul_assoc k s.1 j.val

local instance originalSeparatedIdealRightTower :
    IsScalarTower K
      (((Fin P.vertexCount → K) × (Fin P.vertexCount → K))ᵐᵒᵖ)
      (SeparatedTriangularAlgebra.SeparatedIdeal
        (Fin P.vertexCount → K) P.RadicalBimodule) where
  smul_assoc k s j := by
    apply SeparatedTriangularAlgebra.SeparatedIdeal.ext
    change j.val <• (k • (MulOpposite.unop s).2) =
      k • (j.val <• (MulOpposite.unop s).2)
    exact smul_assoc k (MulOpposite.op (MulOpposite.unop s).2) j.val

local instance reversedSeparatedIdealLeftTower :
    IsScalarTower K
      ((Fin P.vertexCount → K) × (Fin P.vertexCount → K))
      (SeparatedTriangularAlgebra.SeparatedIdeal
        (Fin P.vertexCount → K)
        (ReversedBimodule (Fin P.vertexCount → K)
          P.RadicalBimodule)) where
  smul_assoc k s j := by
    apply SeparatedTriangularAlgebra.SeparatedIdeal.ext
    apply ReversedBimodule.ext'
    change j.val.val <• (k • s.1) = k • (j.val.val <• s.1)
    exact smul_assoc k (MulOpposite.op s.1) j.val.val

local instance reversedSeparatedIdealRightTower :
    IsScalarTower K
      (((Fin P.vertexCount → K) × (Fin P.vertexCount → K))ᵐᵒᵖ)
      (SeparatedTriangularAlgebra.SeparatedIdeal
        (Fin P.vertexCount → K)
        (ReversedBimodule (Fin P.vertexCount → K)
          P.RadicalBimodule)) where
  smul_assoc k s j := by
    apply SeparatedTriangularAlgebra.SeparatedIdeal.ext
    apply ReversedBimodule.ext'
    change (k • (MulOpposite.unop s).2) • j.val.val =
      k • ((MulOpposite.unop s).2 • j.val.val)
    exact smul_assoc k (MulOpposite.unop s).2 j.val.val

local instance originalSeparatedFiniteDimensional :
    FiniteDimensional K (OriginalSeparatedAlgebra P) := by
  apply Module.Finite.trans
    ((Fin P.vertexCount → K) × (Fin P.vertexCount → K))
    (OriginalSeparatedAlgebra P)

local instance reversedSeparatedFiniteDimensional :
    FiniteDimensional K (ReversedSeparatedAlgebra P) := by
  apply Module.Finite.trans
    ((Fin P.vertexCount → K) × (Fin P.vertexCount → K))
    (ReversedSeparatedAlgebra P)

local instance originalSeparatedOppositeIsArtinian :
    IsArtinianRing (OriginalSeparatedAlgebra P)ᵐᵒᵖ :=
  isArtinianRing_op_of_finiteDimensional K (OriginalSeparatedAlgebra P)

local instance originalSeparatedOppositeIsNoetherian :
    IsNoetherianRing (OriginalSeparatedAlgebra P)ᵐᵒᵖ :=
  isNoetherianRing_op_of_finiteDimensional K (OriginalSeparatedAlgebra P)

/-- A canonical complete skeleton of the unreversed separated algebra. -/
def originalSeparatedSkeleton :
    IndecomposableSkeleton
      (OriginalSeparatedAlgebra P)
      (CanonicalIndecomposableIndex (OriginalSeparatedAlgebra P)) :=
  indecomposableSkeletonOfFiniteLength fun X ↦
    ((IsArtinianRing.tfae (OriginalSeparatedAlgebra P) X).out 0 3).mp
      (inferInstance : Module.Finite (OriginalSeparatedAlgebra P) X)

/-- A canonical complete skeleton of the reversed separated algebra. -/
def reversedSeparatedSkeleton :
    IndecomposableSkeleton
      (ReversedSeparatedAlgebra P)
      (CanonicalIndecomposableIndex (ReversedSeparatedAlgebra P)) :=
  indecomposableSkeletonOfFiniteLength fun X ↦
    ((IsArtinianRing.tfae (ReversedSeparatedAlgebra P) X).out 0 3).mp
      (inferInstance : Module.Finite (ReversedSeparatedAlgebra P) X)

/-- A canonical complete skeleton over the opposite unreversed separated
algebra. -/
def originalOppositeSeparatedSkeleton :
    IndecomposableSkeleton
      (OriginalSeparatedAlgebra P)ᵐᵒᵖ
      (CanonicalIndecomposableIndex (OriginalSeparatedAlgebra P)ᵐᵒᵖ) :=
  indecomposableSkeletonOfFiniteLength fun X ↦
    ((IsArtinianRing.tfae (OriginalSeparatedAlgebra P)ᵐᵒᵖ X).out 0 3).mp
      (inferInstance : Module.Finite (OriginalSeparatedAlgebra P)ᵐᵒᵖ X)

/-- The exact cycle-free input needed from the finite hereditary separated
algebra. -/
def OriginalSeparatedDirected : Prop :=
  RepresentationDirected.HasAcyclicNonzeroNonisomorphisms
    (originalSeparatedSkeleton P)

omit [IsAlgClosed K] in
/-- The representation-finite separated triangular algebra is directed.
Its projective radicals live entirely on the semisimple radical-side
diagonal, so the classification-free AR argument applies. -/
theorem originalSeparatedDirected
    (hA : IsRightRepresentationFinite.{u, u, u} K A) :
    OriginalSeparatedDirected P := by
  letI : Finite
      (CanonicalIndecomposableIndex (OriginalSeparatedAlgebra P)) :=
    leftSeparated_isRepresentationFinite P hA
  letI : Fintype
      (CanonicalIndecomposableIndex (OriginalSeparatedAlgebra P)) :=
    Fintype.ofFinite _
  let sigma := originalSeparatedSkeleton P
  apply
    IndecomposableSkeleton.hasAcyclicNonzeroNonisomorphisms_of_irreduciblePredecessorsOfProjectivesAreProjective
      (K := K) sigma
  let AR := sigma.finiteDimensionalARTranslationData K
    (OriginalSeparatedAlgebra P)
  change ∀ {x p}, CategoryTheory.Projective (sigma.obj p) →
    sigma.irreducibleEdge x p → CategoryTheory.Projective (sigma.obj x)
  exact
    SeparatedTriangularAlgebra.irreduciblePredecessorsOfProjectivesAreProjective
      sigma AR

/-- Representation-directed equidistribution on the unreversed separated
algebra identifies its quotient polynomial with that of the reversed
separated algebra. -/
theorem reversedLevelPolynomial_eq_original_of_originalDirected
    (hA : IsRightRepresentationFinite.{u, u, u} K A)
    (hDirected : OriginalSeparatedDirected P) :
    letI : Finite
        (CanonicalIndecomposableIndex (OriginalSeparatedAlgebra P)) :=
      leftSeparated_isRepresentationFinite P hA
    letI : Finite
        (CanonicalIndecomposableIndex (ReversedSeparatedAlgebra P)) :=
      rightSeparated_isRepresentationFinite P hA
    (reversedSeparatedSkeleton P).qClosure.levelPolynomial =
      (originalSeparatedSkeleton P).qClosure.levelPolynomial := by
  letI : Finite
      (CanonicalIndecomposableIndex (OriginalSeparatedAlgebra P)) :=
    leftSeparated_isRepresentationFinite P hA
  letI : Finite
      (CanonicalIndecomposableIndex (ReversedSeparatedAlgebra P)) :=
    rightSeparated_isRepresentationFinite P hA
  let sigma := originalSeparatedSkeleton P
  let tau := originalOppositeSeparatedSkeleton P
  let rho := reversedSeparatedSkeleton P
  let D := Contragredient.alignedBiduality K
    (OriginalSeparatedAlgebra P) sigma tau
  letI : Finite
      (CanonicalIndecomposableIndex (OriginalSeparatedAlgebra P)ᵐᵒᵖ) :=
    D.forward.labelEquiv.finite_iff.mp inferInstance
  letI : Fintype
      (CanonicalIndecomposableIndex (OriginalSeparatedAlgebra P)) :=
    Fintype.ofFinite _
  letI : Fintype
      (CanonicalIndecomposableIndex (OriginalSeparatedAlgebra P)ᵐᵒᵖ) :=
    Fintype.ofFinite _
  let Ddual : tau.AlignedBiduality sigma :=
    { forward := D.backward
      backward := D.forward
      backward_label := by
        rw [D.backward_label]
        rfl }
  let Tsigma := sigma.finiteDimensionalARTranslationData K
    (OriginalSeparatedAlgebra P)
  let Ttau := tau.finiteDimensionalARTranslationData K
    (OriginalSeparatedAlgebra P)ᵐᵒᵖ
  have hSigma : sigma.HasQuotientSubmoduleEquidistribution :=
    RepresentationDirected.IyamaMesh.WordMesh.DirectedEndpoint.quotientSubmoduleEquidistribution_of_directed
      (FSource := K) (FTarget := K)
      sigma tau Ddual hDirected Tsigma Ttau
  have hDual : sigma.sClosure.levelPolynomial =
      tau.qClosure.levelPolynomial :=
    IndecomposableSkeleton.AlignedBiduality.submoduleToQuotientLevelPolynomial_eq
      sigma tau D
  let E : tau.AlignedEquivalence rho :=
    IndecomposableSkeleton.Equivalence.alignedEquivalence tau rho
      (SeparatedTriangularAlgebra.oppositeFgEquivalence
        (S := Fin P.vertexCount → K) (J := P.RadicalBimodule))
  have hEquiv : tau.qClosure.levelPolynomial =
      rho.qClosure.levelPolynomial := E.quotientLevelPolynomial_eq
  exact (hSigma.trans hDual |>.trans hEquiv).symm

/-- Cycle-freeness of the finite hereditary separated algebra is sufficient
for quotient--submodule equidistribution of the original algebra. -/
theorem rightQuotientSubmoduleEquidistribution_of_originalSeparatedDirected
    (hA : IsRightRepresentationFinite.{u, u, u} K A)
    (hDirected : OriginalSeparatedDirected P) :
    RightQuotientSubmoduleEquidistribution K A hA := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  let hAop : IsRightRepresentationFinite.{u, u, u} K Aᵐᵒᵖ :=
    (rightRepresentationFinite_op_iff K A).mp hA
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
  letI : Finite
      (CanonicalIndecomposableIndex (OriginalSeparatedAlgebra P)) :=
    leftSeparated_isRepresentationFinite P hA
  letI : Finite
      (CanonicalIndecomposableIndex (ReversedSeparatedAlgebra P)) :=
    rightSeparated_isRepresentationFinite P hA
  let sigma := rightIndecomposableSkeleton.{u, u, u} K A
  let sigmaOp := rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
  let original := originalSeparatedSkeleton P
  let reversed := reversedSeparatedSkeleton P
  let factor : ℕ[X] :=
    (1 + X) ^ Nat.card sigma.SimpleIndex
  have hright :=
    rightSeparatedLevelPolynomial_eq_source_mul P hA reversed
  have hleft :=
    leftSeparatedLevelPolynomial_eq_sourceOpposite_mul P hA original
  have hsimple :
      Nat.card sigma.SimpleIndex = Nat.card sigmaOp.SimpleIndex :=
    Nat.card_congr
      (DualFixedSocleTransport.simpleIndexEquiv sigma sigmaOp
        (rightOppositeAlignedBiduality K A).forward)
  rw [← hsimple] at hleft
  have hSeparated : reversed.qClosure.levelPolynomial =
      original.qClosure.levelPolynomial :=
    reversedLevelPolynomial_eq_original_of_originalDirected P hA hDirected
  have hmul :
      sigma.qClosure.levelPolynomial * factor =
        sigmaOp.qClosure.levelPolynomial * factor := by
    rw [← hright, ← hleft]
    exact hSeparated
  have hfactor : factor ≠ 0 := by
    apply pow_ne_zero
    intro hzero
    have hcoeff := congrArg (fun p : ℕ[X] ↦ p.coeff 0) hzero
    simp at hcoeff
  have hquotient :
      sigma.qClosure.levelPolynomial =
        sigmaOp.qClosure.levelPolynomial :=
    mul_right_cancel₀ hfactor hmul
  have hduality :
      sigma.sClosure.levelPolynomial =
        sigmaOp.qClosure.levelPolynomial :=
    IndecomposableSkeleton.AlignedBiduality.submoduleToQuotientLevelPolynomial_eq
      sigma sigmaOp (rightOppositeAlignedBiduality K A)
  change sigma.HasQuotientSubmoduleEquidistribution
  exact hquotient.trans hduality.symm

end CoordinatizedSquareZeroMoritaModel

/-- Radical-square-zero equidistribution from the standard fact that the
finite hereditary separated algebra is representation-directed. -/
theorem rightQuotientSubmoduleEquidistribution_of_squareZero_of_separatedDirected
    (K A : Type u)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hA : IsRightRepresentationFinite.{u, u, u} K A)
    (hJ : (Ring.jacobson A) ^ 2 = ⊥)
    (directed :
      ∀ P : CoordinatizedSquareZeroMoritaModel (K := K) (A := A),
        CoordinatizedSquareZeroMoritaModel.OriginalSeparatedDirected P) :
    RightQuotientSubmoduleEquidistribution K A hA := by
  obtain ⟨P⟩ := exists_coordinatizedSquareZeroMoritaModel
    (K := K) (A := A) hJ
  exact
    CoordinatizedSquareZeroMoritaModel.rightQuotientSubmoduleEquidistribution_of_originalSeparatedDirected
      P hA (directed P)

/-- Unconditional radical-square-zero case of the quotient-submodule equidistribution conjecture.  The
separated triangular algebra is representation-finite by the normal-form
construction and directed by its semisimple projective boundary. -/
theorem rightQuotientSubmoduleEquidistribution_of_squareZero
    (K A : Type u)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hA : IsRightRepresentationFinite.{u, u, u} K A)
    (hJ : (Ring.jacobson A) ^ 2 = ⊥) :
    RightQuotientSubmoduleEquidistribution K A hA := by
  obtain ⟨P⟩ := exists_coordinatizedSquareZeroMoritaModel
    (K := K) (A := A) hJ
  exact
    CoordinatizedSquareZeroMoritaModel.rightQuotientSubmoduleEquidistribution_of_originalSeparatedDirected
      P hA (CoordinatizedSquareZeroMoritaModel.originalSeparatedDirected P hA)

end QuotientSubmoduleEquidistribution.RadicalSquareZero
