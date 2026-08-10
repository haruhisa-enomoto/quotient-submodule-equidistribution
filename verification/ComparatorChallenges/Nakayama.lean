import QuotientSubmoduleEquidistribution.RepresentationTheory.NakayamaProductFormula
import QuotientSubmoduleEquidistribution.RepresentationTheory.SerialBoundaryTheorem

noncomputable section

namespace QuotientSubmoduleEquidistribution.NakayamaAlgebraProductFormula

universe u

def IsRightNakayamaAlgebra
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] : Prop :=
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  let σA :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K A
  QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton σA ∧
    QuotientSubmoduleEquidistribution.SerialRingBridge.IsInjectiveNakayamaSkeleton σA

theorem rightQuotientSubmoduleEquidistribution
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hA : QuotientSubmoduleEquidistribution.IsRightRepresentationFinite.{u, u, u} K A)
    (hNakayama : IsRightNakayamaAlgebra K A) :
    QuotientSubmoduleEquidistribution.RightQuotientSubmoduleEquidistribution K A hA := by
  sorry

end QuotientSubmoduleEquidistribution.NakayamaAlgebraProductFormula

