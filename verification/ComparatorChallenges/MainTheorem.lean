import QuotientSubmoduleEquidistribution.RepresentationTheory.FirstLastFourEndpoint
import QuotientSubmoduleEquidistribution.RepresentationTheory.MainTheoremClassCases

set_option autoImplicit false
noncomputable section

namespace QuotientSubmoduleEquidistribution.MainTheoremEndpoint

universe u

variable (K A : Type u)
variable [Field K] [IsAlgClosed K]
variable [Ring A] [Algebra K A] [FiniteDimensional K A]

inductive MainTheoremWitness : Prop where
  | atMostNine
      (hcard :
        letI : IsNoetherianRing Aᵐᵒᵖ :=
          isNoetherianRing_op_of_finiteDimensional K A
        Nat.card (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) ≤ 9)
  | nakayama
      (h : NakayamaAlgebraProductFormula.IsRightNakayamaAlgebra K A)
  | radicalSquareZero
      (hJ : (Ring.jacobson A) ^ 2 = ⊥)
  | representationDirected
      (h : IsRightRepresentationDirected K A)

include K in
theorem rightQuotientSubmoduleEquidistribution
    (hA : IsRightRepresentationFinite.{u, u, u} K A)
    (h : MainTheoremWitness K A) :
    RightQuotientSubmoduleEquidistribution K A hA := by
  sorry

end QuotientSubmoduleEquidistribution.MainTheoremEndpoint

