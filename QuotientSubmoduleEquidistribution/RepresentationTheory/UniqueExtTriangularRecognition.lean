import QuotientSubmoduleEquidistribution.RepresentationTheory.UniqueExtSingleCrossRadical
import QuotientSubmoduleEquidistribution.RepresentationTheory.SingleCrossTriangularEquivalence

/-!
# Recognition of the triangular A2 algebra from one Ext arrow

This file composes the exact Peirce-cotangent--Ext bridge with the abstract
single-cross algebra equivalence.  It remains entirely intrinsic: no quiver
presentation or classification of modules over a model algebra is used.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData

open QuotientSubmoduleEquidistribution.GabrielArrowBridge

universe u v

variable {K B : Type u} {kappa : Type v}
  [Field K] [Ring B] [Algebra K B]
  [IsArtinianRing B] [FiniteDimensional K B]
  [Small.{u} Bᵐᵒᵖ] [IsNoetherianRing Bᵐᵒᵖ]

variable (D : QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData
  (K := K) (B := B))
variable (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u}
  Bᵐᵒᵖ kappa)

include D in
/-- A chosen unique cross Ext--Gabriel arrow forces the algebra itself to
be the three-dimensional triangular model. -/
theorem uniqueCrossExtArrow_singleCrossTriangularAlgEquiv
    (a : ExtGabrielArrowIndex (K := K) tau)
    (hCard : Nat.card (ExtGabrielArrowIndex (K := K) tau) = 1)
    (hCross : ExtGabrielArrowIndex.source tau a ≠
      ExtGabrielArrowIndex.target tau a) :
    Nonempty (QuotientSubmoduleEquidistribution.A2Triangular.Model K ≃ₐ[K] B) := by
  obtain ⟨hij, _hCornerOne, _hCornerZero, _hTotal,
      c, _hcJ, hcL, hcR, hc2, _hspan, hnormal⟩ :=
    QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData.uniqueCrossExtArrow_singleCrossRadicalData
      D tau a hCard hCross
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hc2
    rw [hzero]
    exact (Ring.jacobson B ^ 2).zero_mem
  exact ⟨QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData.singleCrossTriangularAlgEquiv
    D hij c hc0 hcL hcR hnormal⟩

include D in
/-- Vanishing simple self-extensions supplies the crossness premise in the
preceding recognition theorem. -/
theorem uniqueExtArrow_singleCrossTriangularAlgEquiv_of_selfExt_subsingleton
    (a : ExtGabrielArrowIndex (K := K) tau)
    (hCard : Nat.card (ExtGabrielArrowIndex (K := K) tau) = 1)
    (hNoSelf : ∀ s : tau.SimpleIndex, Subsingleton (ExtOne tau s s)) :
    Nonempty (QuotientSubmoduleEquidistribution.A2Triangular.Model K ≃ₐ[K] B) :=
  QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData.uniqueCrossExtArrow_singleCrossTriangularAlgEquiv
    D tau a hCard
    (extGabrielArrow_source_ne_target_of_selfExt_subsingleton
      tau hNoSelf a)

include D in
/-- Cardinality one already provides the arrow needed by the preceding
theorem. -/
theorem extArrowCardOne_singleCrossTriangularAlgEquiv_of_selfExt_subsingleton
    (hCard : Nat.card (ExtGabrielArrowIndex (K := K) tau) = 1)
    (hNoSelf : ∀ s : tau.SimpleIndex, Subsingleton (ExtOne tau s s)) :
    Nonempty (QuotientSubmoduleEquidistribution.A2Triangular.Model K ≃ₐ[K] B) := by
  have hUnique := Nat.card_eq_one_iff_unique.mp hCard
  let a : ExtGabrielArrowIndex (K := K) tau :=
    Classical.choice hUnique.2
  exact
    QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData.uniqueExtArrow_singleCrossTriangularAlgEquiv_of_selfExt_subsingleton
      D tau a hCard hNoSelf

end QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData
