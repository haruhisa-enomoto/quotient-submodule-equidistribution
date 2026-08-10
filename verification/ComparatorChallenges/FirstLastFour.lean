import OpConjecture.RepresentationTheory.CofiniteRooted
import OpConjecture.RepresentationTheory.CofiniteTwoSimpleRank
import OpConjecture.RepresentationTheory.Conjecture
import OpConjecture.RepresentationTheory.FiniteDimensionalRecurrenceAssembly
import OpConjecture.RepresentationTheory.FiniteTypeARTranslation
import OpConjecture.RepresentationTheory.HereditaryThreeSimpleUnconditional
import OpConjecture.RepresentationTheory.SimpleLevels
import OpConjecture.RepresentationTheory.ThreeVertexFactorLadderEndpoint

noncomputable section

namespace OpConjecture.BottomLevels.FiniteDimensionalRecurrence

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]

namespace FirstLastFourEndpoint

variable {K} (B : AlgebraNode K)

theorem bottom_top_four :
    (∀ i ≤ 4,
        (AlgebraNode.qClosure K B).levelCount i =
          (AlgebraNode.sClosure K B).levelCount i) ∧
      (∀ i ≤ 4,
        (AlgebraNode.qClosure K B).levelCount (Nat.card B.Index - i) =
          (AlgebraNode.sClosure K B).levelCount (Nat.card B.Index - i)) := by
  sorry

theorem equidistribution_of_card_le_nine
    (hcard : Nat.card B.Index ≤ 9) :
    B.skeleton.QuotientSubmoduleEquidistribution := by
  sorry

end FirstLastFourEndpoint

end OpConjecture.BottomLevels.FiniteDimensionalRecurrence

