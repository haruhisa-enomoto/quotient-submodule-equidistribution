import OpConjecture.RepresentationTheory.LoewyTwoOneArrowReduction
import OpConjecture.RepresentationTheory.NoParallelExtOne

noncomputable section

namespace OpConjecture.LoewyTwoGabrielClassification

universe u

/--
For a representation-finite finite-dimensional algebra over an
algebraically closed field, every indecomposable with isotypic semisimple
top and isotypic semisimple radical has simple top.

This is the complete Gabriel/one-arrow input used in the second-level
quotient-closure argument.
-/
theorem isotypicLoewyTwoIndecomposablesHaveSimpleTop
    (K A : Type u)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {ι : Type u} [Finite ι]
      (σ : OpConjecture.IndecomposableSkeleton.{u, u, u} Aᵐᵒᵖ ι),
      OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        σ := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
  intro ι _ σ
  exact
    OpConjecture.LoewyTwoRankCore.isotypicLoewyTwoClassification_of_noParallelExtOneArrowReduction
      σ K
      (OpConjecture.NoParallelExtOne.noParallelExtOne_of_finiteDimensional_of_finiteSkeleton
        K A σ)
      (OpConjecture.YonedaOneArrowReduction.noParallelExtOneArrowReduction
        σ K)

/--
The chosen length-two indecomposable together with its simple top is
collectively quotient closed under the paper's hypotheses.
-/
theorem qClosure_isClosed_length_two_top_pair
    (K A : Type u)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {ι : Type u} [Finite ι]
      (σ : OpConjecture.IndecomposableSkeleton.{u, u, u} Aᵐᵒᵖ ι)
      {x : ι} (_hx : σ.compositionLength x = 2)
      (Q : σ.SimpleQuotient x) (_T : σ.SimpleSubmodule x),
      σ.qClosure.IsClosed ({x, Q.index} : Set ι) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
  intro ι _ σ x hx Q T
  exact
    OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.qClosure_isClosed_length_two_top_pair_of_isotypicLoewyTwo
      σ
      (isotypicLoewyTwoIndecomposablesHaveSimpleTop K A σ)
      hx Q T

end OpConjecture.LoewyTwoGabrielClassification
