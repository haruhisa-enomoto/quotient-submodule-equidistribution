import QuotientSubmoduleEquidistribution.ConvexGeometry.CofiniteLevel
import QuotientSubmoduleEquidistribution.RepresentationTheory.CofiniteTwo

/-!
# The `(N - 2)` level for quotient and submodule closure
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe uK uR v w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{uR, v, w} R ι)

/-- Chosen-skeleton quotient-side complement-count bridge. -/
theorem qCofiniteTwoCount_eq_levelCount_card_sub_two
    (hcard : 2 ≤ Nat.card ι) :
    σ.qClosure.cofiniteTwoCount =
      σ.qClosure.levelCount (Nat.card ι - 2) :=
  QuotientSubmoduleEquidistribution.SetClosure.cofiniteTwoCount_eq_levelCount_card_sub_two
    σ.qClosure hcard

/-- Chosen-skeleton submodule-side complement-count bridge. -/
theorem sCofiniteTwoCount_eq_levelCount_card_sub_two
    (hcard : 2 ≤ Nat.card ι) :
    σ.sClosure.cofiniteTwoCount =
      σ.sClosure.levelCount (Nat.card ι - 2) :=
  QuotientSubmoduleEquidistribution.SetClosure.cofiniteTwoCount_eq_levelCount_card_sub_two
    σ.sClosure hcard

variable {K : Type uK}
  [Field K] [Algebra K R]
  [∀ i : ι, Module K (σ.obj i)]
  [∀ i : ι, IsScalarTower K R (σ.obj i)]
  [∀ i : ι, FiniteDimensional K (σ.obj i)]

include K in
/-- Quotient-side formula now stated literally at the chosen skeleton's
`(Nat.card ι - 2)` level. -/
theorem qLevelCount_card_sub_two_eq_choose_add_mixedBoundaryCount
    (hcard : 2 ≤ Nat.card ι) :
    σ.qClosure.levelCount (Nat.card ι - 2) =
      Nat.choose σ.topSplitProjectiveIndices.card 2 +
        σ.qClosure.mixedBoundaryCount := by
  rw [← qCofiniteTwoCount_eq_levelCount_card_sub_two σ hcard]
  exact
    qCofiniteTwoCount_eq_choose_add_mixedBoundaryCount
      (K := K) σ

include K in
/-- Submodule-side formula at the chosen skeleton's `(N - 2)` level. -/
theorem sLevelCount_card_sub_two_eq_choose_add_mixedBoundaryCount
    (hcard : 2 ≤ Nat.card ι) :
    σ.sClosure.levelCount (Nat.card ι - 2) =
      Nat.choose σ.topSplitInjectiveIndices.card 2 +
        σ.sClosure.mixedBoundaryCount := by
  rw [← sCofiniteTwoCount_eq_levelCount_card_sub_two σ hcard]
  exact
    sCofiniteTwoCount_eq_choose_add_mixedBoundaryCount
      (K := K) σ

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton

