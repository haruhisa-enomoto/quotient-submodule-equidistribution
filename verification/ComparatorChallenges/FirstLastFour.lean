import QuotientSubmoduleEquidistribution.RepresentationTheory.CofiniteRooted
import QuotientSubmoduleEquidistribution.RepresentationTheory.CofiniteTwoSimpleRank
import QuotientSubmoduleEquidistribution.RepresentationTheory.Conjecture
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalRecurrenceAssembly
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteTypeARTranslation
import QuotientSubmoduleEquidistribution.RepresentationTheory.HereditaryThreeSimpleUnconditional
import QuotientSubmoduleEquidistribution.RepresentationTheory.SimpleLevels
import QuotientSubmoduleEquidistribution.RepresentationTheory.ThreeVertexFactorLadderEndpoint

noncomputable section

namespace QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence

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
    B.skeleton.HasQuotientSubmoduleEquidistribution := by
  sorry

end FirstLastFourEndpoint

end QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence

