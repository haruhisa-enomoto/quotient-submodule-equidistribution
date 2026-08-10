import QuotientSubmoduleEquidistribution.ConvexGeometry.CofiniteRooted
import QuotientSubmoduleEquidistribution.RepresentationTheory.LiteralLevelCount

/-!
# Literal additive-subcategory endpoint for rooted cofinite counts

This module transports the pure finite rooted/bad-rooted count to the paper's
literal quotient-closed and subobject-closed additive subcategories. The
Auslander--Reiten and factor-ladder content remains the explicit
`RootedBadCofiniteInput`.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe uR uι w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{uR, uι, w} R ι)

/-- Rooted and bad-rooted balance at deletion size `j` gives the exact
literal additive-subcategory equality at level `|ι| - j`. -/
theorem literalLevelCounts_card_sub_eq_of_rootedBadCofiniteInput
    (j : ℕ) (hj : j ≤ Nat.card ι)
    (input :
      QuotientSubmoduleEquidistribution.SetClosure.RootedBadCofiniteInput
        σ.qClosure σ.sClosure j) :
    σ.literalQuotientLevelCount (Nat.card ι - j) =
      σ.literalSubobjectLevelCount (Nat.card ι - j) := by
  rw [literalQuotientLevelCount_eq_levelCount,
    literalSubobjectLevelCount_eq_levelCount]
  exact
    QuotientSubmoduleEquidistribution.SetClosure.levelCount_card_sub_eq_of_rootedBadCofiniteInput
      σ.qClosure σ.sClosure j hj input

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
