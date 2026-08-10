import QuotientSubmoduleEquidistribution.RepresentationTheory.AnnihilatorFactorFamily
import QuotientSubmoduleEquidistribution.RepresentationTheory.QuotientSkeletonCore

/-!
# Canonical annihilator-factor family

For a finite-dimensional algebra with a finite complete indecomposable
skeleton, every proper realized support annihilator has a canonical finite
factor skeleton.  The quotient-inflation alignment assembles these dependent
skeletons into the exact finite recurrence family.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.QuotientSkeletonAlignment

open QuotientSubmoduleEquidistribution.AnnihilatorInflation
open QuotientSubmoduleEquidistribution.AnnihilatorInflation.Skeleton

universe u

variable (K R : Type u) [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R]

include K in
/-- Every factor of a finite-dimensional algebra is Noetherian. -/
theorem factorNoetherian
    (I : TwoSidedIdeal R) : IsNoetherianRing (Quotient.Factor I) := by
  letI : IsArtinianRing (Quotient.Factor I) :=
    IsArtinianRing.of_finite K _
  infer_instance

/-- The canonical factor skeleton with its finite-dimensional Noetherian
instance supplied explicitly. -/
noncomputable def canonicalFactorSkeleton (I : TwoSidedIdeal R) :=
  @factorSkeleton K R _ _ _ _ I (factorNoetherian K R I)

/-- The quotient closure of the canonical factor skeleton, with its class
argument hidden from downstream statements. -/
noncomputable def canonicalFactorQClosure (I : TwoSidedIdeal R) := by
  letI : IsNoetherianRing (Quotient.Factor I) :=
    factorNoetherian K R I
  exact (factorSkeleton K R I).qClosure

/-- The submodule closure of the canonical factor skeleton. -/
noncomputable def canonicalFactorSClosure (I : TwoSidedIdeal R) := by
  letI : IsNoetherianRing (Quotient.Factor I) :=
    factorNoetherian K R I
  exact (factorSkeleton K R I).sClosure

/-- The object family of the canonical factor skeleton. -/
noncomputable def canonicalFactorObj (I : TwoSidedIdeal R) := by
  letI : IsNoetherianRing (Quotient.Factor I) :=
    factorNoetherian K R I
  exact (factorSkeleton K R I).obj

variable [IsNoetherianRing R]
  {iota : Type (u + 1)} [Finite iota]
  (sigma : IndecomposableSkeleton.{u, u + 1, u} R iota)

omit [Finite iota] in
include K in
theorem factorFamilyNoetherian :
    ∀ I : ProperRealizedAnnihilator sigma,
      IsNoetherianRing (Quotient.Factor I.1.1) :=
  fun I ↦ factorNoetherian K R I.1.1

/-- Fully explicit canonical factor family; its dependent Noetherian
instance is supplied by finite dimensionality rather than assumed. -/
noncomputable def canonicalFactorFamilyData :
    @FactorFamilyData R _ _ iota sigma
      (factorFamilyNoetherian K R sigma) := by
  letI : ∀ I : ProperRealizedAnnihilator sigma,
      IsNoetherianRing (Quotient.Factor I.1.1) :=
    factorFamilyNoetherian K R sigma
  exact
    { Index := fun I ↦ FactorIndex R I.1.1
      finiteIndex := fun I ↦
        Finite.of_injective
          (inflationLabelEmbedding sigma I.1.1
            (canonicalFactorSkeleton K R I.1.1))
          (inflationLabel_injective sigma I.1.1
            (canonicalFactorSkeleton K R I.1.1))
      skeleton := fun I ↦ canonicalFactorSkeleton K R I.1.1
      inflation := fun I ↦
        inflationData sigma I.1.1 (canonicalFactorSkeleton K R I.1.1) }

/-- Exact quotient-side recurrence over the canonical proper factor
skeletons, with all quotient Noetherian instances discharged by finite
dimensionality. -/
theorem canonical_qLevelCount_eq_faithful_add_sum_factorFaithful
    (n : ℕ) :
    sigma.qClosure.levelCount n =
      QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
          sigma.qClosure (IsFaithfulSupport sigma.obj) n +
        ∑ I : ProperRealizedAnnihilator sigma,
          QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
            (canonicalFactorQClosure K R I.1.1)
            (IsFaithfulSupport
              (canonicalFactorObj K R I.1.1)) n := by
  letI : ∀ I : ProperRealizedAnnihilator sigma,
      IsNoetherianRing (Quotient.Factor I.1.1) :=
    factorFamilyNoetherian K R sigma
  simpa [canonicalFactorQClosure, canonicalFactorObj,
    canonicalFactorSkeleton,
    canonicalFactorFamilyData] using
    FactorFamilyData.qLevelCount_eq_faithful_add_sum_factorFaithful
      sigma (canonicalFactorFamilyData K R sigma) n

/-- Exact submodule-side recurrence over the same canonical family. -/
theorem canonical_sLevelCount_eq_faithful_add_sum_factorFaithful
    (n : ℕ) :
    sigma.sClosure.levelCount n =
      QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
          sigma.sClosure (IsFaithfulSupport sigma.obj) n +
        ∑ I : ProperRealizedAnnihilator sigma,
          QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
            (canonicalFactorSClosure K R I.1.1)
            (IsFaithfulSupport
              (canonicalFactorObj K R I.1.1)) n := by
  letI : ∀ I : ProperRealizedAnnihilator sigma,
      IsNoetherianRing (Quotient.Factor I.1.1) :=
    factorFamilyNoetherian K R sigma
  simpa [canonicalFactorSClosure, canonicalFactorObj,
    canonicalFactorSkeleton,
    canonicalFactorFamilyData] using
    FactorFamilyData.sLevelCount_eq_faithful_add_sum_factorFaithful
      sigma (canonicalFactorFamilyData K R sigma) n

end QuotientSubmoduleEquidistribution.QuotientSkeletonAlignment
