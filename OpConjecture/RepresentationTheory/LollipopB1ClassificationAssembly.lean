import OpConjecture.RepresentationTheory.LollipopB1FaithfulCoreIdentification

/-!
# Live-path lollipop assembly from an exhaustive classification

The coordinate calculations, named-module properties, faithful-core
identification, and all eight relation-table rows are already unconditional.
This file packages their consequence from the sole remaining input: an
exhaustive seven-object `Classification`.
-/

noncomputable section

open Set

namespace OpConjecture.LollipopConcrete.B1.ModuleLayer.B1ClassificationAssembly

open SevenObjectAdapter
open SevenObjectAdapter.CoreIdentification

universe u

variable (K : Type u) [Field K]

/-- The duplicate-free seven-object indecomposable skeleton supplied by an
exhaustive classification. -/
def indecomposableSkeleton (C : Classification K) :=
  SevenObjectAdapter.skeleton K C

/-- The actual minimal faithful quotient core. -/
def quotientCoreData (C : Classification K) :=
  actualQuotientCoreData K C

/-- The actual minimal faithful submodule core. -/
def submoduleCoreData (C : Classification K) :=
  actualSubmoduleCoreData K C

theorem quotientCoreData_core_eq (C : Classification K) :
    ((quotientCoreData K C).core : Set Label) = quotientCore :=
  actualQuotientCore_eq K C

theorem submoduleCoreData_core_eq (C : Classification K) :
    ((submoduleCoreData K C).core : Set Label) = submoduleCore :=
  actualSubmoduleCore_eq K C

/-- All live-path relation-table rows for the actual faithful cores. -/
def livePathCertificates (C : Classification K) :=
  SevenObjectAdapter.actualLivePathCertificates K C
    (SevenObjectAdapter.quotientBadPresentations K C)
    (quotientCoreData K C) (submoduleCoreData K C)
    (AnnihilatorInflation.isFaithfulSupport_monotone
      (SevenObjectAdapter.skeleton K C).obj)
    (AnnihilatorInflation.isFaithfulSupport_monotone
      (SevenObjectAdapter.skeleton K C).obj)
    (quotientCoreData_core_eq K C)
    (submoduleCoreData_core_eq K C)

/-- Literal connected-small-core table data for the actual faithfulness
predicates. -/
def tableData (C : Classification K) :=
  SevenObjectAdapter.actualTableData K C
    (SevenObjectAdapter.quotientBadPresentations K C)
    (quotientCoreData K C) (submoduleCoreData K C)
    (AnnihilatorInflation.isFaithfulSupport_monotone
      (SevenObjectAdapter.skeleton K C).obj)
    (AnnihilatorInflation.isFaithfulSupport_monotone
      (SevenObjectAdapter.skeleton K C).obj)
    (quotientCoreData_core_eq K C)
    (submoduleCoreData_core_eq K C)

/-- Once the seven displayed objects exhaust the indecomposables, the actual
quotient- and submodule-faithful degree-four counts agree. -/
theorem faithfulLevelCount_four_eq (C : Classification K) :
    BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        (SevenObjectAdapter.skeleton K C).qClosure
        (AnnihilatorInflation.IsFaithfulSupport
          (SevenObjectAdapter.skeleton K C).obj) 4 =
      BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        (SevenObjectAdapter.skeleton K C).sClosure
        (AnnihilatorInflation.IsFaithfulSupport
          (SevenObjectAdapter.skeleton K C).obj) 4 :=
  SevenObjectAdapter.actual_faithfulLevelCount_four_eq K C
    (SevenObjectAdapter.quotientBadPresentations K C)
    (quotientCoreData K C) (submoduleCoreData K C)
    (AnnihilatorInflation.isFaithfulSupport_monotone
      (SevenObjectAdapter.skeleton K C).obj)
    (AnnihilatorInflation.isFaithfulSupport_monotone
      (SevenObjectAdapter.skeleton K C).obj)
    (quotientCoreData_core_eq K C)
    (submoduleCoreData_core_eq K C)

end OpConjecture.LollipopConcrete.B1.ModuleLayer.B1ClassificationAssembly
