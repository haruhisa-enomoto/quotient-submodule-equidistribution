import OpConjecture.ConvexGeometry.Structure
import OpConjecture.RepresentationTheory.SplitProjective
import OpConjecture.RepresentationTheory.SplitInjective

/-!
# Structural theorems for quotient and submodule closure

This file combines the abstract convex-geometry package with the direct
split-projective and split-injective bridges.  It supplies the
module-skeleton form of `thm:infinite-convex-structure` and
`cor:finite-convex-consequences` from the manuscript.
-/

noncomputable section

open Set

namespace OpConjecture.IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

/-- The relative split projective indecomposables which actually belong to
the selected class. -/
def relativeSplitProjectives (C : Set ι) : Set ι :=
  {x | x ∈ C ∧ σ.IsRelativeSplitProjective C x}

/-- The relative split injective indecomposables which actually belong to
the selected class. -/
def relativeSplitInjectives (C : Set ι) : Set ι :=
  {x | x ∈ C ∧ σ.IsRelativeSplitInjective C x}

@[simp]
theorem mem_relativeSplitProjectives {C : Set ι} {x : ι} :
    x ∈ σ.relativeSplitProjectives C ↔
      x ∈ C ∧ σ.IsRelativeSplitProjective C x :=
  Iff.rfl

@[simp]
theorem mem_relativeSplitInjectives {C : Set ι} {x : ι} :
    x ∈ σ.relativeSplitInjectives C ↔
      x ∈ C ∧ σ.IsRelativeSplitInjective C x :=
  Iff.rfl

/-- Quotient-side extreme points are exactly relative split projectives.
Closedness of `C` is not needed for this set identity. -/
theorem qExtremePoints_eq_relativeSplitProjectives
    [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]
    (C : Set ι) :
    σ.qClosure.extremePoints C =
      σ.relativeSplitProjectives C := by
  ext x
  rw [OpConjecture.SetClosure.mem_extremePoints,
    mem_relativeSplitProjectives]
  exact and_congr_right fun _ ↦
    not_mem_qClosure_sdiff_iff_isRelativeSplitProjective σ C x

/-- Submodule-side extreme points are exactly relative split injectives.
Closedness of `C` is not needed for this set identity. -/
theorem sExtremePoints_eq_relativeSplitInjectives
    [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]
    (C : Set ι) :
    σ.sClosure.extremePoints C =
      σ.relativeSplitInjectives C := by
  ext x
  rw [OpConjecture.SetClosure.mem_extremePoints,
    mem_relativeSplitInjectives]
  exact and_congr_right fun _ ↦
    not_mem_sClosure_diff_iff_relativeSplitInjective σ C x

/-- The quotient-closed lattice has the complete abstract infinite convex
structure under the manuscript's finite-dimensional hypotheses. -/
theorem qClosure_infiniteConvexStructure_of_finiteDimensional
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    σ.qClosure.InfiniteConvexStructure :=
  OpConjecture.SetClosure.infiniteConvexStructure
    (qClosure_isFinitary σ)
    (qClosure_isAntiExchange_of_finiteDimensional (K := K) σ)
    (qClosure_isClosed_empty σ)

/-- The submodule-closed lattice has the complete abstract infinite convex
structure under the manuscript's finite-dimensional hypotheses. -/
theorem sClosure_infiniteConvexStructure_of_finiteDimensional
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    σ.sClosure.InfiniteConvexStructure :=
  OpConjecture.SetClosure.infiniteConvexStructure
    (sClosure_isFinitary σ)
    (sClosure_isAntiExchange_of_finiteDimensional (K := K) σ)
    (sClosure_isClosed_empty σ)

/-- The two abstract infinite convex structures asserted together in the
manuscript. -/
theorem quotientSubmodule_infiniteConvexStructures_of_finiteDimensional
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    σ.qClosure.InfiniteConvexStructure ∧
      σ.sClosure.InfiniteConvexStructure :=
  ⟨qClosure_infiniteConvexStructure_of_finiteDimensional
      (K := K) σ,
    sClosure_infiniteConvexStructure_of_finiteDimensional
      (K := K) σ⟩

/-- A compact quotient-closed class has its finite, unique minimal basis
given by the relative split projectives. -/
theorem qCompact_relativeSplitProjectives_basis_of_finiteDimensional
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    {C : σ.qClosure.Closeds} (hcompact : IsCompactElement C) :
    (σ.relativeSplitProjectives (C : Set ι)).Finite ∧
      σ.qClosure.IsMinimalGenerator
        (σ.relativeSplitProjectives (C : Set ι)) (C : Set ι) := by
  letI : ∀ i : ι,
      IsArtinianRing (Module.End R (σ.obj i)) :=
    fun i ↦
      OpConjecture.isArtinianRing_moduleEnd_of_finiteDimensional
        (K := K) (B := R) (M := σ.obj i)
  have hbasis :=
    OpConjecture.SetClosure.compact_extremePoints_basis
      (qClosure_isFinitary σ)
      (qClosure_isAntiExchange σ) hcompact
  rwa [qExtremePoints_eq_relativeSplitProjectives σ] at hbasis

/-- The preceding relative split projective basis is the unique minimal
generating set of a compact quotient-closed class. -/
theorem qCompact_isMinimalGenerator_iff_eq_relativeSplitProjectives
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    {C : σ.qClosure.Closeds} (hcompact : IsCompactElement C)
    {B : Set ι} :
    σ.qClosure.IsMinimalGenerator B (C : Set ι) ↔
      B = σ.relativeSplitProjectives (C : Set ι) := by
  letI : ∀ i : ι,
      IsArtinianRing (Module.End R (σ.obj i)) :=
    fun i ↦
      OpConjecture.isArtinianRing_moduleEnd_of_finiteDimensional
        (K := K) (B := R) (M := σ.obj i)
  rw [← qExtremePoints_eq_relativeSplitProjectives σ]
  exact
    OpConjecture.SetClosure.compact_isMinimalGenerator_iff_eq_extremePoints
      (qClosure_isFinitary σ)
      (qClosure_isAntiExchange σ) hcompact

/-- A compact submodule-closed class has its finite, unique minimal basis
given by the relative split injectives. -/
theorem sCompact_relativeSplitInjectives_basis_of_finiteDimensional
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    {C : σ.sClosure.Closeds} (hcompact : IsCompactElement C) :
    (σ.relativeSplitInjectives (C : Set ι)).Finite ∧
      σ.sClosure.IsMinimalGenerator
        (σ.relativeSplitInjectives (C : Set ι)) (C : Set ι) := by
  letI : ∀ i : ι,
      IsArtinianRing (Module.End R (σ.obj i)) :=
    fun i ↦
      OpConjecture.isArtinianRing_moduleEnd_of_finiteDimensional
        (K := K) (B := R) (M := σ.obj i)
  have hbasis :=
    OpConjecture.SetClosure.compact_extremePoints_basis
      (sClosure_isFinitary σ)
      (sClosure_isAntiExchange σ) hcompact
  rwa [sExtremePoints_eq_relativeSplitInjectives σ] at hbasis

/-- The preceding relative split injective basis is the unique minimal
cogenerating set of a compact submodule-closed class. -/
theorem sCompact_isMinimalGenerator_iff_eq_relativeSplitInjectives
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    {C : σ.sClosure.Closeds} (hcompact : IsCompactElement C)
    {B : Set ι} :
    σ.sClosure.IsMinimalGenerator B (C : Set ι) ↔
      B = σ.relativeSplitInjectives (C : Set ι) := by
  letI : ∀ i : ι,
      IsArtinianRing (Module.End R (σ.obj i)) :=
    fun i ↦
      OpConjecture.isArtinianRing_moduleEnd_of_finiteDimensional
        (K := K) (B := R) (M := σ.obj i)
  rw [← sExtremePoints_eq_relativeSplitInjectives σ]
  exact
    OpConjecture.SetClosure.compact_isMinimalGenerator_iff_eq_extremePoints
      (sClosure_isFinitary σ)
      (sClosure_isAntiExchange σ) hcompact

/-- Finite quotient closure has the accessibility, one-point cover,
cardinality-grading, and extreme-generation consequences of the paper. -/
theorem qClosure_finiteConvexConsequences_of_finiteDimensional
    [Finite ι]
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    σ.qClosure.FiniteConvexConsequences :=
  OpConjecture.SetClosure.finiteConvexConsequences
    (qClosure_isAntiExchange_of_finiteDimensional (K := K) σ)
    (qClosure_isClosed_empty σ)

/-- Finite submodule closure has the accessibility, one-point cover,
cardinality-grading, and extreme-generation consequences of the paper. -/
theorem sClosure_finiteConvexConsequences_of_finiteDimensional
    [Finite ι]
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    σ.sClosure.FiniteConvexConsequences :=
  OpConjecture.SetClosure.finiteConvexConsequences
    (sClosure_isAntiExchange_of_finiteDimensional (K := K) σ)
    (sClosure_isClosed_empty σ)

/-- Every nonempty quotient-closed class on a finite skeleton contains a
relative split projective whose deletion remains quotient-closed. -/
theorem qClosed_exists_relativeSplitProjective_deletion
    [Finite ι]
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    {C : Set ι} (hC : σ.qClosure.IsClosed C)
    (hCne : C.Nonempty) :
    ∃ x ∈ C, σ.IsRelativeSplitProjective C x ∧
      σ.qClosure.IsClosed (C \ {x}) := by
  letI : ∀ i : ι,
      IsArtinianRing (Module.End R (σ.obj i)) :=
    fun i ↦
      OpConjecture.isArtinianRing_moduleEnd_of_finiteDimensional
        (K := K) (B := R) (M := σ.obj i)
  obtain ⟨x, hxextreme⟩ :=
    OpConjecture.SetClosure.extremePoints_nonempty
      (qClosure_isAntiExchange σ)
      (qClosure_isClosed_empty σ) hC hCne
  have hxrelative :
      x ∈ σ.relativeSplitProjectives C := by
    rw [← qExtremePoints_eq_relativeSplitProjectives σ]
    exact hxextreme
  refine ⟨x, hxrelative.1, hxrelative.2, ?_⟩
  exact
    (OpConjecture.SetClosure.mem_extremePoints_iff_isClosed_sdiff_singleton
      hC hxrelative.1).1 hxextreme

/-- Every nonempty submodule-closed class on a finite skeleton contains a
relative split injective whose deletion remains submodule-closed. -/
theorem sClosed_exists_relativeSplitInjective_deletion
    [Finite ι]
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    {C : Set ι} (hC : σ.sClosure.IsClosed C)
    (hCne : C.Nonempty) :
    ∃ x ∈ C, σ.IsRelativeSplitInjective C x ∧
      σ.sClosure.IsClosed (C \ {x}) := by
  letI : ∀ i : ι,
      IsArtinianRing (Module.End R (σ.obj i)) :=
    fun i ↦
      OpConjecture.isArtinianRing_moduleEnd_of_finiteDimensional
        (K := K) (B := R) (M := σ.obj i)
  obtain ⟨x, hxextreme⟩ :=
    OpConjecture.SetClosure.extremePoints_nonempty
      (sClosure_isAntiExchange σ)
      (sClosure_isClosed_empty σ) hC hCne
  have hxrelative :
      x ∈ σ.relativeSplitInjectives C := by
    rw [← sExtremePoints_eq_relativeSplitInjectives σ]
    exact hxextreme
  refine ⟨x, hxrelative.1, hxrelative.2, ?_⟩
  exact
    (OpConjecture.SetClosure.mem_extremePoints_iff_isClosed_sdiff_singleton
      hC hxrelative.1).1 hxextreme

/-- A finite quotient-closed class is generated by its relative split
projective indecomposables. -/
theorem qClosure_relativeSplitProjectives
    [Finite ι]
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    {C : Set ι} (hC : σ.qClosure.IsClosed C) :
    σ.qClosure (σ.relativeSplitProjectives C) = C := by
  letI : ∀ i : ι,
      IsArtinianRing (Module.End R (σ.obj i)) :=
    fun i ↦
      OpConjecture.isArtinianRing_moduleEnd_of_finiteDimensional
        (K := K) (B := R) (M := σ.obj i)
  rw [← qExtremePoints_eq_relativeSplitProjectives σ]
  exact
    OpConjecture.SetClosure.closure_extremePoints
      (qClosure_isAntiExchange σ) hC

/-- A finite submodule-closed class is cogenerated by its relative split
injective indecomposables. -/
theorem sClosure_relativeSplitInjectives
    [Finite ι]
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    {C : Set ι} (hC : σ.sClosure.IsClosed C) :
    σ.sClosure (σ.relativeSplitInjectives C) = C := by
  letI : ∀ i : ι,
      IsArtinianRing (Module.End R (σ.obj i)) :=
    fun i ↦
      OpConjecture.isArtinianRing_moduleEnd_of_finiteDimensional
        (K := K) (B := R) (M := σ.obj i)
  rw [← sExtremePoints_eq_relativeSplitInjectives σ]
  exact
    OpConjecture.SetClosure.closure_extremePoints
      (sClosure_isAntiExchange σ) hC

end OpConjecture.IndecomposableSkeleton
