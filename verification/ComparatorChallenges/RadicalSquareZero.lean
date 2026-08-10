import OpConjecture.RadicalSquareZero.AlgebraNormalFormAssembly
import OpConjecture.RepresentationDirected.AlgebraEndpoint
import OpConjecture.RepresentationTheory.SeparatedTriangularProjectiveBoundary
import OpConjecture.RepresentationTheory.SeparatedTriangularOpposite

set_option autoImplicit false
noncomputable section

namespace OpConjecture.RadicalSquareZero

universe u

theorem rightQuotientSubmoduleEquidistribution_of_squareZero
    (K A : Type u)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hA : IsRightRepresentationFinite.{u, u, u} K A)
    (hJ : (Ring.jacobson A) ^ 2 = ⊥) :
    RightQuotientSubmoduleEquidistribution K A hA := by
  sorry

end OpConjecture.RadicalSquareZero

