import QuotientSubmoduleEquidistribution.ConvexGeometry.CofiniteTwo
import QuotientSubmoduleEquidistribution.RepresentationTheory.ConvexStructure

/-!
# Two-point complements for quotient and submodule closure

This file specializes the abstract two-deletion theorem to the two
module-theoretic closure operators already formalized in the project.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe uK uR v w

variable {K : Type uK} {R : Type uR}
  [Field K] [Ring R] [Algebra K R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{uR, v, w} R ι)
  [∀ i : ι, Module K (σ.obj i)]
  [∀ i : ι, IsScalarTower K R (σ.obj i)]
  [∀ i : ι, FiniteDimensional K (σ.obj i)]

include K in
/-- At the top of the quotient closure, closure-theoretic extreme points
are exactly relative split projectives. -/
theorem qIsTopExtreme_iff_isRelativeSplitProjective (x : ι) :
    σ.qClosure.IsTopExtreme x ↔
      σ.IsRelativeSplitProjective Set.univ x := by
  letI : ∀ i : ι,
      IsArtinianRing (Module.End R (σ.obj i)) :=
    fun i ↦
      QuotientSubmoduleEquidistribution.isArtinianRing_moduleEnd_of_finiteDimensional
        (K := K) (B := R) (M := σ.obj i)
  change
    x ∈ σ.qClosure.extremePoints Set.univ ↔
      σ.IsRelativeSplitProjective Set.univ x
  rw [qExtremePoints_eq_relativeSplitProjectives σ]
  simp

include K in
/-- At the top of the submodule closure, closure-theoretic extreme points
are exactly relative split injectives. -/
theorem sIsTopExtreme_iff_isRelativeSplitInjective (x : ι) :
    σ.sClosure.IsTopExtreme x ↔
      σ.IsRelativeSplitInjective Set.univ x := by
  letI : ∀ i : ι,
      IsArtinianRing (Module.End R (σ.obj i)) :=
    fun i ↦
      QuotientSubmoduleEquidistribution.isArtinianRing_moduleEnd_of_finiteDimensional
        (K := K) (B := R) (M := σ.obj i)
  change
    x ∈ σ.sClosure.extremePoints Set.univ ↔
      σ.IsRelativeSplitInjective Set.univ x
  rw [sExtremePoints_eq_relativeSplitInjectives σ]
  simp

include K in
/-- The part of `prop:cofinite-two` available without almost-split
sequences: a quotient-closed complement of two distinct indecomposables
must delete a relative split projective. -/
theorem isRelativeSplitProjective_or_of_qClosed_compl_pair
    {x y : ι} (hxy : x ≠ y)
    (hclosed : σ.qClosure.IsClosed ({x, y} : Set ι)ᶜ) :
    σ.IsRelativeSplitProjective Set.univ x ∨
      σ.IsRelativeSplitProjective Set.univ y := by
  have h :=
    QuotientSubmoduleEquidistribution.SetClosure.isTopExtreme_or_isTopExtreme_of_isClosed_compl_pair
      σ.qClosure
      (qClosure_isAntiExchange_of_finiteDimensional (K := K) σ)
      hxy hclosed
  exact h.imp
    ((qIsTopExtreme_iff_isRelativeSplitProjective (K := K) σ x).1)
    ((qIsTopExtreme_iff_isRelativeSplitProjective (K := K) σ y).1)

include K in
/-- Dual available part: a submodule-closed complement of two distinct
indecomposables must delete a relative split injective. -/
theorem isRelativeSplitInjective_or_of_sClosed_compl_pair
    {x y : ι} (hxy : x ≠ y)
    (hclosed : σ.sClosure.IsClosed ({x, y} : Set ι)ᶜ) :
    σ.IsRelativeSplitInjective Set.univ x ∨
      σ.IsRelativeSplitInjective Set.univ y := by
  have h :=
    QuotientSubmoduleEquidistribution.SetClosure.isTopExtreme_or_isTopExtreme_of_isClosed_compl_pair
      σ.sClosure
      (sClosure_isAntiExchange_of_finiteDimensional (K := K) σ)
      hxy hclosed
  exact h.imp
    ((sIsTopExtreme_iff_isRelativeSplitInjective (K := K) σ x).1)
    ((sIsTopExtreme_iff_isRelativeSplitInjective (K := K) σ y).1)

section Finite

variable [Fintype ι] [DecidableEq ι]

/-- Indecomposable indices which are relative split projective at the
whole module category. -/
def topSplitProjectiveIndices : Finset ι :=
  by
    classical
    exact Finset.univ.filter fun x ↦
      σ.IsRelativeSplitProjective Set.univ x

omit [DecidableEq ι] in
@[simp]
theorem mem_topSplitProjectiveIndices {x : ι} :
    x ∈ σ.topSplitProjectiveIndices ↔
      σ.IsRelativeSplitProjective Set.univ x := by
  classical
  simp [topSplitProjectiveIndices]

/-- Indecomposable indices which are relative split injective at the
whole module category. -/
def topSplitInjectiveIndices : Finset ι :=
  by
    classical
    exact Finset.univ.filter fun x ↦
      σ.IsRelativeSplitInjective Set.univ x

omit [DecidableEq ι] in
@[simp]
theorem mem_topSplitInjectiveIndices {x : ι} :
    x ∈ σ.topSplitInjectiveIndices ↔
      σ.IsRelativeSplitInjective Set.univ x := by
  classical
  simp [topSplitInjectiveIndices]

omit [DecidableEq ι] in
include K in
theorem qTopExtremeFinset_eq_topSplitProjectiveIndices :
    σ.qClosure.topExtremeFinset =
      σ.topSplitProjectiveIndices := by
  classical
  ext x
  rw [QuotientSubmoduleEquidistribution.SetClosure.mem_topExtremeFinset,
    mem_topSplitProjectiveIndices]
  exact qIsTopExtreme_iff_isRelativeSplitProjective
    (K := K) σ x

omit [DecidableEq ι] in
include K in
theorem sTopExtremeFinset_eq_topSplitInjectiveIndices :
    σ.sClosure.topExtremeFinset =
      σ.topSplitInjectiveIndices := by
  classical
  ext x
  rw [QuotientSubmoduleEquidistribution.SetClosure.mem_topExtremeFinset,
    mem_topSplitInjectiveIndices]
  exact sIsTopExtreme_iff_isRelativeSplitInjective
    (K := K) σ x

include K in
/-- Quotient-side cofinite-two formula with the strongest boundary term
currently definable in the package. -/
theorem qCofiniteTwoCount_eq_choose_add_mixedBoundaryCount :
    σ.qClosure.cofiniteTwoCount =
      Nat.choose σ.topSplitProjectiveIndices.card 2 +
        σ.qClosure.mixedBoundaryCount := by
  rw [← qTopExtremeFinset_eq_topSplitProjectiveIndices (K := K) σ]
  exact
    QuotientSubmoduleEquidistribution.SetClosure.cofiniteTwoCount_eq_choose_add_mixedBoundaryCount
      σ.qClosure
      (qClosure_isAntiExchange_of_finiteDimensional (K := K) σ)

include K in
/-- Submodule-side cofinite-two formula with the closure-theoretic mixed
boundary term. -/
theorem sCofiniteTwoCount_eq_choose_add_mixedBoundaryCount :
    σ.sClosure.cofiniteTwoCount =
      Nat.choose σ.topSplitInjectiveIndices.card 2 +
        σ.sClosure.mixedBoundaryCount := by
  rw [← sTopExtremeFinset_eq_topSplitInjectiveIndices (K := K) σ]
  exact
    QuotientSubmoduleEquidistribution.SetClosure.cofiniteTwoCount_eq_choose_add_mixedBoundaryCount
      σ.sClosure
      (sClosure_isAntiExchange_of_finiteDimensional (K := K) σ)

end Finite

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton

