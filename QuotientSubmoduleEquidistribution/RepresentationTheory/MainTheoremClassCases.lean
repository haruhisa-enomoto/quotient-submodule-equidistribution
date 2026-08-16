import QuotientSubmoduleEquidistribution.RadicalSquareZero.SeparatedDirectedInterface
import QuotientSubmoduleEquidistribution.RepresentationDirected.AlgebraEndpoint
import QuotientSubmoduleEquidistribution.RepresentationTheory.NakayamaAlgebraProductFormula

/-!
# The three general algebra classes in the main theorem

This file combines the Nakayama, radical-square-zero, and
representation-directed theorems under a single three-way hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace QuotientSubmoduleEquidistribution.MainTheoremClassCases

universe u

variable (K A : Type u)
variable [Field K] [IsAlgClosed K]
variable [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- Evidence that `A` belongs to one of the three general algebra classes in
the manuscript's main theorem. -/
inductive GeneralClassWitness : Prop where
  | nakayama
      (h : QuotientSubmoduleEquidistribution.NakayamaAlgebraProductFormula.IsRightNakayamaAlgebra
        K A)
  | radicalSquareZero
      (hJ : (Ring.jacobson A) ^ 2 = ⊥)
  | representationDirected
      (h : QuotientSubmoduleEquidistribution.IsRightRepresentationDirected K A)

/-- Main-theorem aggregation for the three general algebra classes. -/
theorem rightQuotientSubmoduleEquidistribution
    (hA : QuotientSubmoduleEquidistribution.IsRightRepresentationFinite.{u, u, u} K A)
    (hClass : GeneralClassWitness K A) :
    QuotientSubmoduleEquidistribution.RightQuotientSubmoduleEquidistribution K A hA := by
  cases hClass with
  | nakayama hNakayama =>
      exact
        QuotientSubmoduleEquidistribution.NakayamaAlgebraProductFormula.rightQuotientSubmoduleEquidistribution
          K A hA hNakayama
  | radicalSquareZero hJ =>
      exact
        QuotientSubmoduleEquidistribution.RadicalSquareZero.rightQuotientSubmoduleEquidistribution_of_squareZero
          K A hA hJ
  | representationDirected hDirected =>
      let hDirected' : QuotientSubmoduleEquidistribution.IsRightRepresentationDirected K A :=
        ⟨hA, by simpa using hDirected.2⟩
      exact
        QuotientSubmoduleEquidistribution.rightRepresentationDirected_quotientSubmoduleEquidistribution
          K A hDirected'

end QuotientSubmoduleEquidistribution.MainTheoremClassCases
