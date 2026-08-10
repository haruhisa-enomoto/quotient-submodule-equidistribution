import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0Classification
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0FaithfulCoreIdentification

/-!
# Unconditional dead-path lollipop assembly

This file combines the five-object classification with the exact
identification of the quotient and submodule faithful cores.  It removes all
remaining hypotheses from the concrete dead-path recurrence table and its
degree-four equality.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.B0Assembly

open FiveObjectAdapter
open FiveObjectAdapter.CoreIdentification

universe u

variable (K : Type u) [Field K]

/-- The unconditional duplicate-free five-object indecomposable skeleton. -/
def indecomposableSkeleton :=
  FiveObjectAdapter.skeleton K (B0Classification.classification K)

/-- The actual minimal faithful quotient core for the classified skeleton. -/
def quotientCoreData :=
  actualQuotientCoreData K (B0Classification.classification K)

/-- The actual minimal faithful submodule core for the classified skeleton. -/
def submoduleCoreData :=
  actualSubmoduleCoreData K (B0Classification.classification K)

theorem quotientCoreData_core_eq :
    ((quotientCoreData K).core : Set Label) = quotientCore :=
  actualQuotientCore_eq K (B0Classification.classification K)

theorem submoduleCoreData_core_eq :
    ((submoduleCoreData K).core : Set Label) = submoduleCore :=
  actualSubmoduleCore_eq K (B0Classification.classification K)

/-- Unconditional row certificates for the actual faithful cores. -/
def deadPathCertificates :=
  FiveObjectAdapter.actualDeadPathCertificates K
    (B0Classification.classification K)
    (quotientCoreData K) (submoduleCoreData K)
    (AnnihilatorInflation.isFaithfulSupport_monotone
      (FiveObjectAdapter.skeleton K
        (B0Classification.classification K)).obj)
    (AnnihilatorInflation.isFaithfulSupport_monotone
      (FiveObjectAdapter.skeleton K
        (B0Classification.classification K)).obj)
    (quotientCoreData_core_eq K)
    (submoduleCoreData_core_eq K)

/-- Unconditional literal recurrence data for the actual faithfulness
predicates. -/
def tableData :=
  FiveObjectAdapter.actualTableData K
    (B0Classification.classification K)
    (quotientCoreData K) (submoduleCoreData K)
    (AnnihilatorInflation.isFaithfulSupport_monotone
      (FiveObjectAdapter.skeleton K
        (B0Classification.classification K)).obj)
    (AnnihilatorInflation.isFaithfulSupport_monotone
      (FiveObjectAdapter.skeleton K
        (B0Classification.classification K)).obj)
    (quotientCoreData_core_eq K)
    (submoduleCoreData_core_eq K)

/-- The actual quotient- and submodule-faithful degree-four counts agree for
the dead-path lollipop algebra. -/
theorem faithfulLevelCount_four_eq :
    BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        (FiveObjectAdapter.skeleton K
          (B0Classification.classification K)).qClosure
        (AnnihilatorInflation.IsFaithfulSupport
          (FiveObjectAdapter.skeleton K
            (B0Classification.classification K)).obj) 4 =
      BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        (FiveObjectAdapter.skeleton K
          (B0Classification.classification K)).sClosure
        (AnnihilatorInflation.IsFaithfulSupport
          (FiveObjectAdapter.skeleton K
            (B0Classification.classification K)).obj) 4 :=
  FiveObjectAdapter.actual_faithfulLevelCount_four_eq K
    (B0Classification.classification K)
    (quotientCoreData K) (submoduleCoreData K)
    (AnnihilatorInflation.isFaithfulSupport_monotone
      (FiveObjectAdapter.skeleton K
        (B0Classification.classification K)).obj)
    (AnnihilatorInflation.isFaithfulSupport_monotone
      (FiveObjectAdapter.skeleton K
        (B0Classification.classification K)).obj)
    (quotientCoreData_core_eq K)
    (submoduleCoreData_core_eq K)

end QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.B0Assembly
