import QuotientSubmoduleEquidistribution.RepresentationTheory.CofiniteTwoIrreducible
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveInjectiveBoundary
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveSimpleRank

/-!
# The simple-rank form of the cofinite-two formulas

This file replaces the projective or injective boundary cardinality in the
finite-skeleton cofinite-two formulas by the number of simple-module labels.
The quotient replacement uses the projective-top bijection.  The submodule
replacement additionally uses the projective--injective boundary equivalence
for a finite-dimensional algebra over a field.
-/

noncomputable section

open Set CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore

universe uK u v

section BoundaryRanks

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

omit [DecidableEq ι] in
/-- The quotient top boundary has one label for each simple module. -/
theorem topSplitProjectiveIndices_card_eq_natCard_simpleIndex :
    σ.topSplitProjectiveIndices.card = Nat.card σ.SimpleIndex := by
  calc
    σ.topSplitProjectiveIndices.card =
        ((↑σ.topSplitProjectiveIndices : Set ι)).ncard :=
      (Set.ncard_coe_finset _).symm
    _ = (projectiveLabels σ).ncard := by
      congr 1
      ext i
      simp [projectiveLabels,
        σ.projective_iff_isRelativeSplitProjective_univ]
    _ = Nat.card σ.SimpleIndex :=
      ProjectiveSimpleRank.ncard_projectiveLabels_eq_natCard_simpleIndex σ

variable {K : Type u} [Field K] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing Rᵐᵒᵖ]

omit [DecidableEq ι] in
include K in
/-- For a finite-dimensional algebra, the submodule top boundary also has
one label for each simple module. -/
theorem topSplitInjectiveIndices_card_eq_natCard_simpleIndex :
    σ.topSplitInjectiveIndices.card = Nat.card σ.SimpleIndex := by
  calc
    σ.topSplitInjectiveIndices.card =
        ((↑σ.topSplitInjectiveIndices : Set ι)).ncard :=
      (Set.ncard_coe_finset _).symm
    _ = (QuotientSubmoduleEquidistribution.RingelStable.injectiveSet σ).ncard := by
      congr 1
      ext i
      simp [QuotientSubmoduleEquidistribution.RingelStable.injectiveSet,
        σ.injective_iff_isRelativeSplitInjective_univ]
    _ = (QuotientSubmoduleEquidistribution.RingelStable.projectiveSet σ).ncard :=
      (QuotientSubmoduleEquidistribution.RingelStable.projectiveSet_ncard_eq_injectiveSet_ncard
        (R := R) K σ).symm
    _ = (projectiveLabels σ).ncard := rfl
    _ = Nat.card σ.SimpleIndex :=
      ProjectiveSimpleRank.ncard_projectiveLabels_eq_natCard_simpleIndex σ

end BoundaryRanks

section QuotientFormula

variable {K : Type uK} [Field K]
  {R : Type u} [Ring R] [Algebra K R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  [∀ i : ι, Module K (σ.obj i)]
  [∀ i : ι, IsScalarTower K R (σ.obj i)]
  [∀ i : ι, FiniteDimensional K (σ.obj i)]

include K in
/-- The quotient colevel-one count is the number of simple-module labels. -/
theorem qLevelCount_card_sub_one_eq_simpleIndex
    (hcard : 1 ≤ Nat.card ι) :
    σ.qClosure.levelCount (Nat.card ι - 1) =
      Nat.card σ.SimpleIndex := by
  calc
    σ.qClosure.levelCount (Nat.card ι - 1) =
        Nat.card {p : ι // σ.qClosure.IsTopExtreme p} :=
      QuotientSubmoduleEquidistribution.SetClosure.levelCount_card_sub_one_eq_natCard_topExtreme
        σ.qClosure hcard
    _ = σ.qClosure.topExtremeFinset.card :=
      QuotientSubmoduleEquidistribution.SetClosure.natCard_topExtreme_eq_topExtremeFinset_card
        σ.qClosure
    _ = σ.topSplitProjectiveIndices.card := by
      congr 1
      ext p
      rw [QuotientSubmoduleEquidistribution.SetClosure.mem_topExtremeFinset,
        mem_topSplitProjectiveIndices]
      calc
        σ.qClosure.IsTopExtreme p ↔ Projective (σ.obj p) :=
          σ.qIsTopExtreme_iff_projective (K := K) p
        _ ↔ σ.IsRelativeSplitProjective Set.univ p :=
          σ.projective_iff_isRelativeSplitProjective_univ
    _ = Nat.card σ.SimpleIndex :=
      σ.topSplitProjectiveIndices_card_eq_natCard_simpleIndex

include K in
/-- The literal quotient-closed colevel-one count is the number of simple
modules. -/
theorem literalQuotientLevelCount_card_sub_one_eq_simpleIndex
    (hcard : 1 ≤ Nat.card ι) :
    σ.literalQuotientLevelCount (Nat.card ι - 1) =
      Nat.card σ.SimpleIndex := by
  rw [σ.literalQuotientLevelCount_eq_levelCount]
  exact σ.qLevelCount_card_sub_one_eq_simpleIndex (K := K) hcard

include K in
/-- The finite-skeleton specialization of the paper's quotient cofinite-two
formula, with the number of simple modules and the categorical `beta_q` pair
count. -/
theorem qCofiniteTwoCount_eq_choose_simpleIndex_add_irreducibleBoundary :
    σ.qClosure.cofiniteTwoCount =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.QIrreducibleBoundaryPair := by
  rw [σ.qCofiniteTwoCount_eq_choose_add_natCard_QIrreducibleBoundaryPair
      (K := K),
    σ.topSplitProjectiveIndices_card_eq_natCard_simpleIndex]

include K in
/-- The quotient cofinite-two formula with the manuscript's literal
`rad / rad²` boundary term. -/
theorem qCofiniteTwoCount_eq_choose_simpleIndex_add_radicalQuotientBoundary :
    σ.qClosure.cofiniteTwoCount =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.QRadicalQuotientBoundaryPair := by
  rw [σ.qCofiniteTwoCount_eq_choose_simpleIndex_add_irreducibleBoundary
      (K := K),
    σ.natCard_QRadicalQuotientBoundaryPair_eq_natCard_QIrreducibleBoundaryPair]

include K in
/-- The simple-rank quotient formula on the chosen skeleton's
`(Nat.card ι - 2)` level. -/
theorem qLevelCount_card_sub_two_eq_choose_simpleIndex_add_irreducibleBoundary
    (hcard : 2 ≤ Nat.card ι) :
    σ.qClosure.levelCount (Nat.card ι - 2) =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.QIrreducibleBoundaryPair := by
  rw [σ.qLevelCount_card_sub_two_eq_choose_add_natCard_QIrreducibleBoundaryPair
      (K := K) hcard,
    σ.topSplitProjectiveIndices_card_eq_natCard_simpleIndex]

include K in
/-- The simple-rank quotient formula for literal quotient-closed additive
subcategories. -/
theorem
    literalQuotientLevelCount_card_sub_two_eq_choose_simpleIndex_add_irreducibleBoundary
    (hcard : 2 ≤ Nat.card ι) :
    σ.literalQuotientLevelCount (Nat.card ι - 2) =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.QIrreducibleBoundaryPair := by
  rw [σ.literalQuotientLevelCount_card_sub_two_eq_choose_add_natCard_QIrreducibleBoundaryPair
      (K := K) hcard,
    σ.topSplitProjectiveIndices_card_eq_natCard_simpleIndex]

include K in
/-- The literal quotient-closed `N - 2` formula with the manuscript's
`rad / rad²` boundary term. -/
theorem
    literalQuotientLevelCount_card_sub_two_eq_choose_simpleIndex_add_radicalQuotientBoundary
    (hcard : 2 ≤ Nat.card ι) :
    σ.literalQuotientLevelCount (Nat.card ι - 2) =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.QRadicalQuotientBoundaryPair := by
  rw [σ.literalQuotientLevelCount_card_sub_two_eq_choose_simpleIndex_add_irreducibleBoundary
      (K := K) hcard,
    σ.natCard_QRadicalQuotientBoundaryPair_eq_natCard_QIrreducibleBoundaryPair]

end QuotientFormula

section SubmoduleFormula

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  [IsNoetherianRing Rᵐᵒᵖ]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  [∀ i : ι, Module K (σ.obj i)]
  [∀ i : ι, IsScalarTower K R (σ.obj i)]
  [∀ i : ι, FiniteDimensional K (σ.obj i)]

include K in
/-- The submodule colevel-one count is the number of simple-module labels. -/
theorem sLevelCount_card_sub_one_eq_simpleIndex
    (hcard : 1 ≤ Nat.card ι) :
    σ.sClosure.levelCount (Nat.card ι - 1) =
      Nat.card σ.SimpleIndex := by
  calc
    σ.sClosure.levelCount (Nat.card ι - 1) =
        Nat.card {i : ι // σ.sClosure.IsTopExtreme i} :=
      QuotientSubmoduleEquidistribution.SetClosure.levelCount_card_sub_one_eq_natCard_topExtreme
        σ.sClosure hcard
    _ = σ.sClosure.topExtremeFinset.card :=
      QuotientSubmoduleEquidistribution.SetClosure.natCard_topExtreme_eq_topExtremeFinset_card
        σ.sClosure
    _ = σ.topSplitInjectiveIndices.card := by
      congr 1
      ext i
      rw [QuotientSubmoduleEquidistribution.SetClosure.mem_topExtremeFinset,
        mem_topSplitInjectiveIndices]
      calc
        σ.sClosure.IsTopExtreme i ↔ Injective (σ.obj i) :=
          σ.sIsTopExtreme_iff_injective (K := K) i
        _ ↔ σ.IsRelativeSplitInjective Set.univ i :=
          σ.injective_iff_isRelativeSplitInjective_univ
    _ = Nat.card σ.SimpleIndex :=
      σ.topSplitInjectiveIndices_card_eq_natCard_simpleIndex (K := K)

include K in
/-- The literal subobject-closed colevel-one count is the number of simple
modules. -/
theorem literalSubobjectLevelCount_card_sub_one_eq_simpleIndex
    (hcard : 1 ≤ Nat.card ι) :
    σ.literalSubobjectLevelCount (Nat.card ι - 1) =
      Nat.card σ.SimpleIndex := by
  rw [σ.literalSubobjectLevelCount_eq_levelCount]
  exact σ.sLevelCount_card_sub_one_eq_simpleIndex (K := K) hcard

include K in
/-- Quotient-closed and subobject-closed colevel-one counts agree. -/
theorem qLevelCount_card_sub_one_eq_sLevelCount_card_sub_one
    (hcard : 1 ≤ Nat.card ι) :
    σ.qClosure.levelCount (Nat.card ι - 1) =
      σ.sClosure.levelCount (Nat.card ι - 1) := by
  rw [σ.qLevelCount_card_sub_one_eq_simpleIndex (K := K) hcard,
    σ.sLevelCount_card_sub_one_eq_simpleIndex (K := K) hcard]

include K in
/-- Literal quotient-closed and subobject-closed colevel-one counts agree. -/
theorem
    literalQuotientLevelCount_card_sub_one_eq_literalSubobjectLevelCount_card_sub_one
    (hcard : 1 ≤ Nat.card ι) :
    σ.literalQuotientLevelCount (Nat.card ι - 1) =
      σ.literalSubobjectLevelCount (Nat.card ι - 1) := by
  rw [σ.literalQuotientLevelCount_card_sub_one_eq_simpleIndex
      (K := K) hcard,
    σ.literalSubobjectLevelCount_card_sub_one_eq_simpleIndex
      (K := K) hcard]

include K in
/-- The finite-skeleton specialization of the paper's submodule cofinite-two
formula, with the number of simple modules and the categorical `beta_s` pair
count. -/
theorem sCofiniteTwoCount_eq_choose_simpleIndex_add_irreducibleBoundary :
    σ.sClosure.cofiniteTwoCount =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.SIrreducibleBoundaryPair := by
  rw [σ.sCofiniteTwoCount_eq_choose_add_natCard_SIrreducibleBoundaryPair
      (K := K),
    σ.topSplitInjectiveIndices_card_eq_natCard_simpleIndex (K := K)]

include K in
/-- The submodule cofinite-two formula with the manuscript's literal
`rad / rad²` boundary term. -/
theorem sCofiniteTwoCount_eq_choose_simpleIndex_add_radicalQuotientBoundary :
    σ.sClosure.cofiniteTwoCount =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.SRadicalQuotientBoundaryPair := by
  rw [σ.sCofiniteTwoCount_eq_choose_simpleIndex_add_irreducibleBoundary
      (K := K),
    σ.natCard_SRadicalQuotientBoundaryPair_eq_natCard_SIrreducibleBoundaryPair]

include K in
/-- The simple-rank submodule formula on the chosen skeleton's
`(Nat.card ι - 2)` level. -/
theorem sLevelCount_card_sub_two_eq_choose_simpleIndex_add_irreducibleBoundary
    (hcard : 2 ≤ Nat.card ι) :
    σ.sClosure.levelCount (Nat.card ι - 2) =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.SIrreducibleBoundaryPair := by
  rw [σ.sLevelCount_card_sub_two_eq_choose_add_natCard_SIrreducibleBoundaryPair
      (K := K) hcard,
    σ.topSplitInjectiveIndices_card_eq_natCard_simpleIndex (K := K)]

include K in
/-- The simple-rank submodule formula for literal subobject-closed additive
subcategories. -/
theorem
    literalSubobjectLevelCount_card_sub_two_eq_choose_simpleIndex_add_irreducibleBoundary
    (hcard : 2 ≤ Nat.card ι) :
    σ.literalSubobjectLevelCount (Nat.card ι - 2) =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.SIrreducibleBoundaryPair := by
  rw [σ.literalSubobjectLevelCount_card_sub_two_eq_choose_add_natCard_SIrreducibleBoundaryPair
      (K := K) hcard,
    σ.topSplitInjectiveIndices_card_eq_natCard_simpleIndex (K := K)]

include K in
/-- The literal subobject-closed `N - 2` formula with the manuscript's
`rad / rad²` boundary term. -/
theorem
    literalSubobjectLevelCount_card_sub_two_eq_choose_simpleIndex_add_radicalQuotientBoundary
    (hcard : 2 ≤ Nat.card ι) :
    σ.literalSubobjectLevelCount (Nat.card ι - 2) =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.SRadicalQuotientBoundaryPair := by
  rw [σ.literalSubobjectLevelCount_card_sub_two_eq_choose_simpleIndex_add_irreducibleBoundary
      (K := K) hcard,
    σ.natCard_SRadicalQuotientBoundaryPair_eq_natCard_SIrreducibleBoundaryPair]

end SubmoduleFormula

section FiniteDimensionalAlgebra

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  [IsNoetherianRing Rᵐᵒᵖ]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

include K in
/-- For a finite-dimensional algebra, the two colevel-one counts agree and
their common value is the number of simple-module labels. -/
theorem finiteDimensional_colevelOne_formula
    (hcard : 1 ≤ Nat.card ι) :
    σ.qClosure.levelCount (Nat.card ι - 1) =
        σ.sClosure.levelCount (Nat.card ι - 1) ∧
      σ.qClosure.levelCount (Nat.card ι - 1) =
        Nat.card σ.SimpleIndex := by
  letI (i : ι) : Module K (σ.obj i) :=
    Module.restrictScalars K R (σ.obj i)
  letI (i : ι) : IsScalarTower K R (σ.obj i) :=
    IsScalarTower.restrictScalars K R (σ.obj i)
  letI (i : ι) : FiniteDimensional K (σ.obj i) :=
    Module.Finite.trans R (σ.obj i)
  exact
    ⟨σ.qLevelCount_card_sub_one_eq_sLevelCount_card_sub_one
        (K := K) hcard,
      σ.qLevelCount_card_sub_one_eq_simpleIndex (K := K) hcard⟩

include K in
/-- Literal finite-dimensional version of the colevel-one formula. -/
theorem finiteDimensional_literalCofiniteOne_formula
    (hcard : 1 ≤ Nat.card ι) :
    σ.literalQuotientLevelCount (Nat.card ι - 1) =
        σ.literalSubobjectLevelCount (Nat.card ι - 1) ∧
      σ.literalQuotientLevelCount (Nat.card ι - 1) =
        Nat.card σ.SimpleIndex := by
  letI (i : ι) : Module K (σ.obj i) :=
    Module.restrictScalars K R (σ.obj i)
  letI (i : ι) : IsScalarTower K R (σ.obj i) :=
    IsScalarTower.restrictScalars K R (σ.obj i)
  letI (i : ι) : FiniteDimensional K (σ.obj i) :=
    Module.Finite.trans R (σ.obj i)
  exact
    ⟨σ.literalQuotientLevelCount_card_sub_one_eq_literalSubobjectLevelCount_card_sub_one
        (K := K) hcard,
      σ.literalQuotientLevelCount_card_sub_one_eq_simpleIndex
        (K := K) hcard⟩

end FiniteDimensionalAlgebra

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
