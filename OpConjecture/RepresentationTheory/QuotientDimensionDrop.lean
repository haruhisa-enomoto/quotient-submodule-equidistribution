import OpConjecture.RepresentationTheory.AnnihilatorInflation
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Strict dimension drop for nonzero factor ideals

This is the well-founded measure needed by annihilator induction: a proper
nontrivial quotient of a finite-dimensional algebra has strictly smaller
ground-field dimension.
-/

noncomputable section

namespace OpConjecture.QuotientSkeletonAlignment

universe u v w

open OpConjecture.AnnihilatorInflation

variable (K R : Type u) [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R]

/-- Quotienting by a nonzero two-sided ideal strictly lowers the finite
dimension over the ground field. -/
theorem factor_finrank_lt (I : TwoSidedIdeal R) (hI : I ≠ ⊥) :
    Module.finrank K (Quotient.Factor I) < Module.finrank K R := by
  let J : Submodule K R := I.asIdeal.restrictScalars K
  have hJ : J ≠ ⊥ := by
    intro hzero
    apply hI
    apply TwoSidedIdeal.ext
    intro r
    have hr : r ∈ J ↔ r ∈ I := Iff.rfl
    rw [← hr, hzero]
    simp
  have hpos : 0 < Module.finrank K J :=
    (Submodule.one_le_finrank_iff.mpr hJ)
  have hsum := J.finrank_quotient_add_finrank
  change Module.finrank K (Quotient.Factor I) + Module.finrank K J =
    Module.finrank K R at hsum
  omega

/-- Specialized measure drop for the exact proper-factor index used by the
finite realized-annihilator recurrence. -/
theorem properRealized_factor_finrank_lt
    [IsNoetherianRing R]
    {ι : Type v}
    (σ : IndecomposableSkeleton.{u, v, w} R ι)
    (I : AnnihilatorInflation.Skeleton.ProperRealizedAnnihilator σ) :
    Module.finrank K (Quotient.Factor I.1.1) < Module.finrank K R :=
  factor_finrank_lt K R I.1.1 I.2

end OpConjecture.QuotientSkeletonAlignment
