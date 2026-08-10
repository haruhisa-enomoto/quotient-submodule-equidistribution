import OpConjecture.RepresentationTheory.NakayamaProductFormula
import OpConjecture.RepresentationTheory.SerialBoundaryTheorem

noncomputable section

namespace OpConjecture.NakayamaAlgebraProductFormula

universe u

def IsRightNakayamaAlgebra
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] : Prop :=
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
  let σA :=
    OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A
  OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton σA ∧
    OpConjecture.SerialRingBridge.IsInjectiveNakayamaSkeleton σA

theorem rightQuotientSubmoduleEquidistribution
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hA : OpConjecture.IsRightRepresentationFinite.{u, u, u} K A)
    (hNakayama : IsRightNakayamaAlgebra K A) :
    OpConjecture.RightQuotientSubmoduleEquidistribution K A hA := by
  sorry

end OpConjecture.NakayamaAlgebraProductFormula

