import OpConjecture.RepresentationTheory.BlockDecomposition
import OpConjecture.RepresentationTheory.RingelEtaCoreCardinality

/-!
# Assembly of the repaired finite-dimensional recurrence

The Ringel and disconnected fields of
`FiniteDimensionalRecurrence.RemainingData` are now theorems.  This file
assembles them and exposes the connected small-core classification as the
only remaining input to the simultaneous degree-three/degree-four
recurrence.
-/

noncomputable section

open Set

namespace OpConjecture.BottomLevels.FiniteDimensionalRecurrence

open OpConjecture.IndecomposableSkeleton.FaithfulCore

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- Ringel's stable equivalence and central-idempotent block decomposition
supply every recurrence field except the connected small-core cases. -/
theorem remainingData_of_smallCore
    (smallCore :
      ∀ (B : AlgebraNode K) (n : ℕ), n = 3 ∨ n = 4 →
        OpConjecture.BlockDecomposition.Node.IsBlockConnected K B →
        (((AlgebraNode.quotientCoreData K B).core : Set B.Index).ncard <
          n) →
        (AlgebraNode.faithfulQCount K B n =
            AlgebraNode.faithfulSCount K B n) ∨
          (AlgebraNode.qClosure K B).levelCount n =
            (AlgebraNode.sClosure K B).levelCount n) :
    AlgebraNode.RemainingData K
      (OpConjecture.BlockDecomposition.Node.IsBlockConnected K) :=
  OpConjecture.BlockDecomposition.Node.remainingData_of_ringel_and_smallCore
    K
    (fun B ↦
      OpConjecture.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
        B.skeleton K)
    smallCore

/-- Final concrete endpoint conditional only on the connected
hereditary/Nakayama/lollipop small-core classification. -/
theorem levelCount_three_and_four_eq_of_smallCore
    (smallCore :
      ∀ (B : AlgebraNode K) (n : ℕ), n = 3 ∨ n = 4 →
        OpConjecture.BlockDecomposition.Node.IsBlockConnected K B →
        (((AlgebraNode.quotientCoreData K B).core : Set B.Index).ncard <
          n) →
        (AlgebraNode.faithfulQCount K B n =
            AlgebraNode.faithfulSCount K B n) ∨
          (AlgebraNode.qClosure K B).levelCount n =
            (AlgebraNode.sClosure K B).levelCount n)
    (B : AlgebraNode K) :
    (AlgebraNode.qClosure K B).levelCount 3 =
        (AlgebraNode.sClosure K B).levelCount 3 ∧
      (AlgebraNode.qClosure K B).levelCount 4 =
        (AlgebraNode.sClosure K B).levelCount 4 :=
  AlgebraNode.levelCount_three_and_four_eq K
    (OpConjecture.BlockDecomposition.Node.IsBlockConnected K)
    (remainingData_of_smallCore K smallCore) B

end OpConjecture.BottomLevels.FiniteDimensionalRecurrence
