import QuotientSubmoduleEquidistribution.RepresentationTheory.CofiniteRooted
import QuotientSubmoduleEquidistribution.RepresentationTheory.CofiniteTwoSimpleRank
import QuotientSubmoduleEquidistribution.RepresentationTheory.Conjecture
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalRecurrenceAssembly
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteTypeARTranslation
import QuotientSubmoduleEquidistribution.RepresentationTheory.HereditaryThreeSimpleUnconditional
import QuotientSubmoduleEquidistribution.RepresentationTheory.SimpleLevels
import QuotientSubmoduleEquidistribution.RepresentationTheory.ThreeVertexFactorLadderEndpoint

/-!
# The exact first/last-four endpoint

This file assembles the manuscript's coefficient theorem through the first and
last four levels.  The bottom-three and bottom-four connected small-core
statements, the colevel-three factor-ladder classification, and the
colevel-four packet calculation are all unconditional.

No algebra presentation or classification of concrete modules is used here.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]

namespace FirstLastFourEndpoint

variable {K} (B : AlgebraNode K)

/-- The assembled coefficient theorem through the first and last four
levels.  When a requested colevel exceeds the number of indecomposable
labels, truncated subtraction reduces it to the already-proved level zero. -/
theorem bottom_top_four :
    (∀ i ≤ 4,
        (AlgebraNode.qClosure K B).levelCount i =
          (AlgebraNode.sClosure K B).levelCount i) ∧
      (∀ i ≤ 4,
        (AlgebraNode.qClosure K B).levelCount (Nat.card B.Index - i) =
          (AlgebraNode.sClosure K B).levelCount (Nat.card B.Index - i)) := by
  classical
  letI : Fintype B.Index := Fintype.ofFinite B.Index
  letI : DecidableEq B.Index := Classical.decEq B.Index
  let τ :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K B.Carrier
  let dual :=
    QuotientSubmoduleEquidistribution.Contragredient.alignedBiduality
      K B.Carrier B.skeleton τ
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
        B.Carrierᵐᵒᵖ) :=
    dual.forward.labelEquiv.finite_iff.mp inferInstance
  letI : Fintype
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
        B.Carrierᵐᵒᵖ) := Fintype.ofFinite _
  letI : DecidableEq
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
        B.Carrierᵐᵒᵖ) := Classical.decEq _
  have hthreeFour :=
    QuotientSubmoduleEquidistribution.HereditaryThreeSimpleUnconditional.levelCount_three_and_four_eq_unconditional
      K B
  constructor
  · intro i hi
    interval_cases i
    · exact B.skeleton.qLevelCount_zero_eq_sLevelCount_zero
    · exact B.skeleton.qLevelCount_one_eq_sLevelCount_one
    · exact QuotientSubmoduleEquidistribution.BlockDecomposition.Node.levelCount_two_eq K B
    · exact hthreeFour.1
    · exact hthreeFour.2
  · intro i hi
    by_cases hiCard : i ≤ Nat.card B.Index
    · interval_cases i
      · simp only [Nat.sub_zero]
        calc
          (AlgebraNode.qClosure K B).levelCount (Nat.card B.Index) = 1 :=
            QuotientSubmoduleEquidistribution.SetClosure.levelCount_card_eq_one _
          _ = (AlgebraNode.sClosure K B).levelCount (Nat.card B.Index) :=
            (QuotientSubmoduleEquidistribution.SetClosure.levelCount_card_eq_one _).symm
      · exact
          (B.skeleton.finiteDimensional_colevelOne_formula
            (K := K) hiCard).1
      · rw [← B.skeleton.qCofiniteTwoCount_eq_levelCount_card_sub_two
              hiCard,
            ← B.skeleton.sCofiniteTwoCount_eq_levelCount_card_sub_two
              hiCard]
        exact
          B.skeleton.finiteDimensional_qCofiniteTwoCount_eq_sCofiniteTwoCount
            (K := K)
      · exact
          QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData.ThreeVertex.levelCount_card_sub_three_eq_of_alignedBiduality
            (k := K) B.skeleton τ dual hiCard
      · exact
          QuotientSubmoduleEquidistribution.IndecomposableSkeleton.levelCount_card_sub_four_eq_of_alignedBiduality
            (K := K) B.skeleton τ dual hiCard
    · have hzero : Nat.card B.Index - i = 0 :=
        Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hiCard)
      rw [hzero]
      exact B.skeleton.qLevelCount_zero_eq_sLevelCount_zero

/-- The at-most-nine case of the paper follows formally from the assembled
first/last-four coefficients. -/
theorem equidistribution_of_card_le_nine
    (hcard : Nat.card B.Index ≤ 9) :
    B.skeleton.HasQuotientSubmoduleEquidistribution := by
  obtain ⟨hbottom, htop⟩ := bottom_top_four B
  exact
    B.skeleton.quotientSubmoduleEquidistribution_of_bottom_top_four
      hcard hbottom htop

end FirstLastFourEndpoint

end QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence
