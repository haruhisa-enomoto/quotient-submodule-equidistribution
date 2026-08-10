import QuotientSubmoduleEquidistribution.RadicalSquareZero.TopCoverageAdapter
import QuotientSubmoduleEquidistribution.RepresentationTheory.Conjecture
import QuotientSubmoduleEquidistribution.RepresentationTheory.OppositeDuality

/-!
# Separated-quiver endpoint

This file packages the exact representation-theoretic input of the
radical-square-zero argument and connects it to the already formalized
top-coverage enumeration.

A `SeparatedQuotientModel` labels the indecomposables of an original module
category as nonsimples plus one copy of the simple vertices, and those of its
separated hereditary category as nonsimples plus two copies of the same
vertices.  The two `TopCoverageData` fields assert precisely the closedness
criteria proved in the manuscript.  They share a common core family, which is
the formal content of the separated-representation comparison.

The endpoint proves the universal Boolean factor and then combines the models
for an algebra and its opposite with contragredient duality.  No division of
polynomials is used.  Constructing these data from `rad(A)^2 = 0` remains the
separated-representation theorem; it is deliberately not assumed under a
weaker name here.
-/

set_option autoImplicit false

noncomputable section

namespace QuotientSubmoduleEquidistribution.RadicalSquareZero

open Polynomial
open RadicalSquareZeroCombinatorics
open RadicalSquareZeroCombinatorics.CoreFamily
open RadicalSquareZeroCombinatorics.CoreFamily.TopCoverage

universe uR uS vI vJ wR wS uV uC uN₁ uN₂

/-- The exact quotient-closure comparison between an original finite module
skeleton and its separated side.

The label equivalences record the nonsimple/simple decompositions.  The two
top-coverage fields say that quotient-closed supports on both sides are
parametrized by the same nonsimple cores and mandatory top vertices. -/
structure SeparatedQuotientModel
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {S : Type uS} [Ring S] [IsNoetherianRing S]
    {I : Type vI} {J : Type vJ}
    [Fintype I] [Fintype J]
    (sigma : IndecomposableSkeleton.{uR, vI, wR} R I)
    (tau : IndecomposableSkeleton.{uS, vJ, wS} S J)
    (Vertex : Type uV) (Core : Type uC)
    (NonsimpleOriginal : Type uN₁)
    (NonsimpleSeparated : Type uN₂)
    [Fintype Vertex] [DecidableEq Vertex] [Fintype Core]
    [Fintype NonsimpleOriginal] [Fintype NonsimpleSeparated] where
  /-- The original indecomposables are its nonsimples and one simple for each
  vertex. -/
  originalLabels : I ≃ NonsimpleOriginal ⊕ Vertex
  /-- The separated indecomposables are its common nonsimples and two simple
  copies for each original vertex. -/
  separatedLabels : J ≃ NonsimpleSeparated ⊕ (Vertex ⊕ Vertex)
  /-- Common nonsimple closed cores and their top supports. -/
  coreFamily :
    RadicalSquareZeroCombinatorics.CoreFamily Core Vertex
  /-- Exact original-side top-coverage criterion after relabeling the actual
  quotient closure. -/
  originalTopCoverage :
    TopCoverage.ATopCoverageData coreFamily
      (SetClosure.transport sigma.qClosure originalLabels)
  /-- Exact separated-side top-coverage criterion after relabeling the actual
  quotient closure. -/
  separatedTopCoverage :
    TopCoverage.BTopCoverageData coreFamily
      (SetClosure.transport tau.qClosure separatedLabels)

namespace SeparatedQuotientModel

variable
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {S : Type uS} [Ring S] [IsNoetherianRing S]
    {I : Type vI} {J : Type vJ}
    [Fintype I] [Fintype J]
    {sigma : IndecomposableSkeleton.{uR, vI, wR} R I}
    {tau : IndecomposableSkeleton.{uS, vJ, wS} S J}
    {Vertex : Type uV} {Core : Type uC}
    {NonsimpleOriginal : Type uN₁}
    {NonsimpleSeparated : Type uN₂}
    [Fintype Vertex] [DecidableEq Vertex] [Fintype Core]
    [Fintype NonsimpleOriginal] [Fintype NonsimpleSeparated]

/-- The separated-side quotient polynomial is the original quotient
polynomial times one Boolean factor for each simple vertex. -/
theorem separatedLevelPolynomial_eq_original_mul
    (M : SeparatedQuotientModel sigma tau Vertex Core
      NonsimpleOriginal NonsimpleSeparated) :
    tau.qClosure.levelPolynomial =
      sigma.qClosure.levelPolynomial *
        (1 + X) ^ Fintype.card Vertex := by
  have hOriginal :
      sigma.qClosure.levelPolynomial =
        (SetClosure.transport sigma.qClosure
          M.originalLabels).levelPolynomial :=
    SetClosure.RelabelingEquiv.levelPolynomial_eq
      (SetClosure.transportRelabeling sigma.qClosure
        M.originalLabels)
  have hSeparated :
      tau.qClosure.levelPolynomial =
        (SetClosure.transport tau.qClosure
          M.separatedLabels).levelPolynomial :=
    SetClosure.RelabelingEquiv.levelPolynomial_eq
      (SetClosure.transportRelabeling tau.qClosure
        M.separatedLabels)
  calc
    tau.qClosure.levelPolynomial =
        (SetClosure.transport tau.qClosure
          M.separatedLabels).levelPolynomial := hSeparated
    _ = (SetClosure.transport sigma.qClosure
          M.originalLabels).levelPolynomial *
          (1 + X) ^ Fintype.card Vertex :=
      TopCoverage.levelPolynomial_B_eq_levelPolynomial_A_mul
        M.originalTopCoverage M.separatedTopCoverage
    _ = sigma.qClosure.levelPolynomial *
          (1 + X) ^ Fintype.card Vertex := by
      rw [← hOriginal]

end SeparatedQuotientModel

universe uT uU vK vL wT wU uC₂ uM₁ uM₂

/-- Opposite separated models with the same vertex set and the same
separated-side quotient polynomial imply quotient--submodule
equidistribution on the original skeleton.

For a radical-square-zero algebra, equality of the two separated-side
polynomials comes from exchanging the `+` and `-` copies in the separated
quiver.  The aligned biduality is the formal counterpart of vector-space
duality. -/
theorem quotientSubmoduleEquidistribution_of_oppositeSeparatedModels
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {Rop : Type uS} [Ring Rop] [IsNoetherianRing Rop]
    {B : Type uT} [Ring B] [IsNoetherianRing B]
    {Bop : Type uU} [Ring Bop] [IsNoetherianRing Bop]
    {I : Type vI} {Iop : Type vJ}
    {J : Type vK} {Jop : Type vL}
    [Fintype I] [Fintype Iop] [Fintype J] [Fintype Jop]
    (sigma : IndecomposableSkeleton.{uR, vI, wR} R I)
    (sigmaOp : IndecomposableSkeleton.{uS, vJ, wS} Rop Iop)
    (separated : IndecomposableSkeleton.{uT, vK, wT} B J)
    (separatedOp : IndecomposableSkeleton.{uU, vL, wU} Bop Jop)
    (D : sigma.AlignedBiduality sigmaOp)
    {Vertex : Type uV} [Fintype Vertex] [DecidableEq Vertex]
    {Core : Type uC} [Fintype Core]
    {CoreOp : Type uC₂} [Fintype CoreOp]
    {NonsimpleOriginal : Type uN₁} [Fintype NonsimpleOriginal]
    {NonsimpleSeparated : Type uN₂} [Fintype NonsimpleSeparated]
    {NonsimpleOriginalOp : Type uM₁} [Fintype NonsimpleOriginalOp]
    {NonsimpleSeparatedOp : Type uM₂} [Fintype NonsimpleSeparatedOp]
    (M : SeparatedQuotientModel sigma separated Vertex Core
      NonsimpleOriginal NonsimpleSeparated)
    (Mop : SeparatedQuotientModel sigmaOp separatedOp Vertex CoreOp
      NonsimpleOriginalOp NonsimpleSeparatedOp)
    (hSeparated : separated.qClosure.levelPolynomial =
      separatedOp.qClosure.levelPolynomial) :
    sigma.HasQuotientSubmoduleEquidistribution := by
  let factor : ℕ[X] := (1 + X) ^ Fintype.card Vertex
  have hOriginal := M.separatedLevelPolynomial_eq_original_mul
  have hOpposite := Mop.separatedLevelPolynomial_eq_original_mul
  have hmul :
      sigma.qClosure.levelPolynomial * factor =
        sigmaOp.qClosure.levelPolynomial * factor := by
    rw [← hOriginal, ← hOpposite]
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
      sigma sigmaOp D
  exact hquotient.trans hduality.symm

namespace AlgebraEndpoint

universe u

/-- Paper-facing algebra endpoint for the radical-square-zero strategy.

Once separated-quiver quotient models have been constructed for `A` and
`Aᵐᵒᵖ`, and the two separated hereditary sides have the same quotient
polynomial, canonical vector-space duality proves the strong conjecture for
`A`.  In the manuscript the last equality is induced by exchanging the two
copies of every separated-quiver vertex. -/
theorem rightQuotientSubmoduleEquidistribution_of_separatedQuiverModels
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hA : IsRightRepresentationFinite.{u, u, u} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
    letI : Finite
        (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
    letI : Finite
        (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
      (rightRepresentationFinite_op_iff K A).1 hA
    letI : Fintype
        (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
      Fintype.ofFinite _
    letI : Fintype
        (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
      Fintype.ofFinite _
    ∀ {B Bop : Type u}
      [Ring B] [IsNoetherianRing B]
      [Ring Bop] [IsNoetherianRing Bop]
      {J Jop : Type u} [Fintype J] [Fintype Jop]
      (separated : IndecomposableSkeleton.{u, u, u} B J)
      (separatedOp : IndecomposableSkeleton.{u, u, u} Bop Jop)
      {Vertex Core CoreOp : Type u}
      [Fintype Vertex] [DecidableEq Vertex]
      [Fintype Core] [Fintype CoreOp]
      {NonsimpleOriginal NonsimpleSeparated : Type u}
      {NonsimpleOriginalOp NonsimpleSeparatedOp : Type u}
      [Fintype NonsimpleOriginal] [Fintype NonsimpleSeparated]
      [Fintype NonsimpleOriginalOp] [Fintype NonsimpleSeparatedOp]
      (_M : SeparatedQuotientModel
        (rightIndecomposableSkeleton.{u, u, u} K A)
        separated Vertex Core NonsimpleOriginal NonsimpleSeparated)
      (_Mop : SeparatedQuotientModel
        (rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ)
        separatedOp Vertex CoreOp NonsimpleOriginalOp
          NonsimpleSeparatedOp),
      separated.qClosure.levelPolynomial =
          separatedOp.qClosure.levelPolynomial →
        RightQuotientSubmoduleEquidistribution K A hA := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
    (rightRepresentationFinite_op_iff K A).1 hA
  letI : Fintype
      (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
    Fintype.ofFinite _
  letI : Fintype
      (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
    Fintype.ofFinite _
  intro B Bop _ _ _ _ J Jop _ _ separated separatedOp
    Vertex Core CoreOp _ _ _ _ NonsimpleOriginal
    NonsimpleSeparated NonsimpleOriginalOp NonsimpleSeparatedOp
    _ _ _ _ M Mop hSeparated
  let sigma := rightIndecomposableSkeleton.{u, u, u} K A
  let sigmaOp := rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
  change sigma.HasQuotientSubmoduleEquidistribution
  exact quotientSubmoduleEquidistribution_of_oppositeSeparatedModels
    sigma sigmaOp separated separatedOp
    (rightOppositeAlignedBiduality K A) M Mop hSeparated

end AlgebraEndpoint

end QuotientSubmoduleEquidistribution.RadicalSquareZero
