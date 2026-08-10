import QuotientSubmoduleEquidistribution.RepresentationTheory.ArtinBottomThreeCardinalityBoundary
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalRecurrence

/-!
# Unconditional bottom-level-three endpoint

The classification-free Artin-duality cardinality theorem is restated at
the finite-dimensional algebra-node interface used by the main endpoint.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- Quotient-closed and submodule-closed subsets with three labels are
equinumerous for every finite-dimensional algebra node. -/
theorem levelCount_three_eq (B : AlgebraNode K) :
    (qClosure K B).levelCount 3 = (sClosure K B).levelCount 3 := by
  letI : IsArtinianRing B.Carrier :=
    IsArtinianRing.of_finite K B.Carrier
  have h :=
    QuotientSubmoduleEquidistribution.ArtinBottomThree.CardinalityBoundary.triple_natCard_eq
      K B.skeleton
        (fun _ => QuotientSubmoduleEquidistribution.ArtinDuality.ofFiniteDimensional K)
  unfold QuotientSubmoduleEquidistribution.SetClosure.levelCount
  calc
    {C : B.skeleton.qClosure.Closeds |
        (C : Set B.Index).ncard = 3}.ncard =
        Nat.card {C : B.skeleton.qClosure.Closeds //
          (C : Set B.Index).ncard = 3} :=
      (Nat.card_coe_set_eq _).symm
    _ = Nat.card {C : B.skeleton.sClosure.Closeds //
          (C : Set B.Index).ncard = 3} := h
    _ = {C : B.skeleton.sClosure.Closeds |
        (C : Set B.Index).ncard = 3}.ncard :=
      Nat.card_coe_set_eq _

end QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode
