import OpConjecture.RepresentationDirected.IyamaWordMeshDirectedEndpoint
import OpConjecture.RepresentationTheory.FiniteDimensionalARNonvanishing
import OpConjecture.RepresentationTheory.OppositeDuality

set_option autoImplicit false
noncomputable section

namespace OpConjecture

open RepresentationDirected

universe u

def IsRightRepresentationDirected
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] : Prop :=
  IsRightRepresentationFinite.{u, u, u} K A ∧
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    HasAcyclicNonzeroNonisomorphisms
      (rightIndecomposableSkeleton.{u, u, u} K A)

theorem rightRepresentationDirected_quotientSubmoduleEquidistribution
    (K A : Type u)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A]
    (h : IsRightRepresentationDirected K A) :
    RightQuotientSubmoduleEquidistribution K A h.1 := by
  sorry

end OpConjecture

