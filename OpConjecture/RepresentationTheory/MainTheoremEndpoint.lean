import OpConjecture.RepresentationTheory.FirstLastFourEndpoint
import OpConjecture.RepresentationTheory.MainTheoremClassCases

/-!
# Main theorem endpoint

This file collects the four branches of the manuscript's main theorem:
at most nine indecomposables, Nakayama, radical-square-zero, and
representation-directed.
-/

set_option autoImplicit false
noncomputable section

namespace OpConjecture.MainTheoremEndpoint

universe u

variable (K A : Type u)
variable [Field K] [IsAlgClosed K]
variable [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- The four alternatives in the manuscript's main theorem. -/
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
/-- The paper-facing aggregation theorem.  Every nonformalized assumption
appears explicitly in `MainTheoremWitness`; all four deductions are checked
in Lean. -/
theorem rightQuotientSubmoduleEquidistribution
    (hA : IsRightRepresentationFinite.{u, u, u} K A)
    (h : MainTheoremWitness K A) :
    RightQuotientSubmoduleEquidistribution K A hA := by
  cases h with
  | atMostNine hcard =>
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        isNoetherianRing_op_of_finiteDimensional K A
      letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
        isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
      letI : Finite
          (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
      let B : BottomLevels.FiniteDimensionalRecurrence.AlgebraNode K :=
        { Carrier := Aᵐᵒᵖ
          Index := CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ
          skeleton := rightIndecomposableSkeleton.{u, u, u} K A }
      have hB :
          (B.skeleton : IndecomposableSkeleton Aᵐᵒᵖ
            (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ)).QuotientSubmoduleEquidistribution :=
        BottomLevels.FiniteDimensionalRecurrence.FirstLastFourEndpoint.equidistribution_of_card_le_nine
          B hcard
      exact hB
  | nakayama hNakayama =>
      exact MainTheoremClassCases.rightQuotientSubmoduleEquidistribution
        K A hA (.nakayama hNakayama)
  | radicalSquareZero hJ =>
      exact MainTheoremClassCases.rightQuotientSubmoduleEquidistribution
        K A hA (.radicalSquareZero hJ)
  | representationDirected hDirected =>
      exact MainTheoremClassCases.rightQuotientSubmoduleEquidistribution
        K A hA (.representationDirected hDirected)

end OpConjecture.MainTheoremEndpoint
