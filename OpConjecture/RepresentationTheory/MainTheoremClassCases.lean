import OpConjecture.RadicalSquareZero.SeparatedDirectedInterface
import OpConjecture.RepresentationDirected.AlgebraEndpoint
import OpConjecture.RepresentationTheory.NakayamaAlgebraProductFormula

/-!
# The three general algebra classes in the main theorem

This file collects the paper-facing endpoints for Nakayama,
radical-square-zero, and representation-directed algebras.  All three
branches are unconditional.
-/

set_option autoImplicit false

noncomputable section

namespace OpConjecture.MainTheoremClassCases

universe u

variable (K A : Type u)
variable [Field K] [IsAlgClosed K]
variable [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- Evidence that `A` belongs to one of the three general algebra classes in
the manuscript's main theorem. -/
inductive GeneralClassWitness : Prop where
  | nakayama
      (h : OpConjecture.NakayamaAlgebraProductFormula.IsRightNakayamaAlgebra
        K A)
  | radicalSquareZero
      (hJ : (Ring.jacobson A) ^ 2 = ⊥)
  | representationDirected
      (h : OpConjecture.IsRightRepresentationDirected K A)

/-- Main-theorem aggregation for the three general algebra classes. -/
theorem rightQuotientSubmoduleEquidistribution
    (hA : OpConjecture.IsRightRepresentationFinite.{u, u, u} K A)
    (hClass : GeneralClassWitness K A) :
    OpConjecture.RightQuotientSubmoduleEquidistribution K A hA := by
  cases hClass with
  | nakayama hNakayama =>
      exact
        OpConjecture.NakayamaAlgebraProductFormula.rightQuotientSubmoduleEquidistribution
          K A hA hNakayama
  | radicalSquareZero hJ =>
      exact
        OpConjecture.RadicalSquareZero.rightQuotientSubmoduleEquidistribution_of_squareZero
          K A hA hJ
  | representationDirected hDirected =>
      let hDirected' : OpConjecture.IsRightRepresentationDirected K A :=
        ⟨hA, by simpa using hDirected.2⟩
      exact
        OpConjecture.rightRepresentationDirected_quotientSubmoduleEquidistribution
          K A hDirected'

end OpConjecture.MainTheoremClassCases
