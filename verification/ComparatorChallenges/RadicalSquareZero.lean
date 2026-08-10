import QuotientSubmoduleEquidistribution.RadicalSquareZero.AlgebraNormalFormAssembly
import QuotientSubmoduleEquidistribution.RepresentationDirected.AlgebraEndpoint
import QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedTriangularProjectiveBoundary
import QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedTriangularOpposite

set_option autoImplicit false
noncomputable section

namespace QuotientSubmoduleEquidistribution.RadicalSquareZero

universe u

theorem rightQuotientSubmoduleEquidistribution_of_squareZero
    (K A : Type u)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hA : IsRightRepresentationFinite.{u, u, u} K A)
    (hJ : (Ring.jacobson A) ^ 2 = ⊥) :
    RightQuotientSubmoduleEquidistribution K A hA := by
  sorry

end QuotientSubmoduleEquidistribution.RadicalSquareZero

