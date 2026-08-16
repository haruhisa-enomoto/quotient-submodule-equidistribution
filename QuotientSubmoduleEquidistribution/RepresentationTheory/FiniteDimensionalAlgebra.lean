import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.RingTheory.Artinian.Module
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteLengthDecomposition
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteFacApproximation
import QuotientSubmoduleEquidistribution.RepresentationTheory.ConvexStructure
import QuotientSubmoduleEquidistribution.RepresentationTheory.Conjecture
import QuotientSubmoduleEquidistribution.RepresentationTheory.Distributive

/-!
# Finite-dimensional algebras and finite indecomposable skeletons

This file derives the
Noetherian, finite-dimensional-module, finite-length, and Artinian
endomorphism-ring hypotheses from a finite-dimensional algebra over a field,
then bundles representation-finiteness as a finite complete skeleton of
indecomposable right modules.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution

universe uK uA v w

/-- The opposite of a finite-dimensional algebra is Artinian. -/
theorem isArtinianRing_op_of_finiteDimensional
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    IsArtinianRing Aᵐᵒᵖ :=
  IsArtinianRing.of_finite K Aᵐᵒᵖ

/-- A finite-dimensional algebra has a left-Noetherian opposite ring. -/
theorem isNoetherianRing_op_of_finiteDimensional
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    IsNoetherianRing Aᵐᵒᵖ := by
  letI : IsArtinianRing Aᵐᵒᵖ :=
    isArtinianRing_op_of_finiteDimensional K A
  infer_instance

/-- Every finitely generated right module over a finite-dimensional
algebra is finite-dimensional over the ground field. -/
theorem finiteDimensional_rightFGModule
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (X : FGModuleCat.{w} Aᵐᵒᵖ) :
    letI : Module K X := Module.restrictScalars K Aᵐᵒᵖ X
    FiniteDimensional K X := by
  letI : Module K X := Module.restrictScalars K Aᵐᵒᵖ X
  letI : IsScalarTower K Aᵐᵒᵖ X :=
    IsScalarTower.restrictScalars K Aᵐᵒᵖ X
  exact Module.Finite.trans Aᵐᵒᵖ X

/-- Every finitely generated right module has finite length over the
opposite algebra. -/
theorem isFiniteLength_rightFGModule
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (X : FGModuleCat.{w} Aᵐᵒᵖ) :
    IsFiniteLength Aᵐᵒᵖ X := by
  letI : IsArtinianRing Aᵐᵒᵖ :=
    isArtinianRing_op_of_finiteDimensional K A
  exact
    ((IsArtinianRing.tfae Aᵐᵒᵖ X).out 0 3).mp
      (inferInstance : Module.Finite Aᵐᵒᵖ X)

/-- Consequently, its endomorphism ring over the opposite algebra is
Artinian. -/
theorem isArtinianRing_end_rightFGModule
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (X : FGModuleCat.{w} Aᵐᵒᵖ) :
    IsArtinianRing (Module.End Aᵐᵒᵖ X) := by
  letI : Module K X := Module.restrictScalars K Aᵐᵒᵖ X
  letI : IsScalarTower K Aᵐᵒᵖ X :=
    IsScalarTower.restrictScalars K Aᵐᵒᵖ X
  letI : FiniteDimensional K X :=
    finiteDimensional_rightFGModule K A X
  exact
    QuotientSubmoduleEquidistribution.isArtinianRing_moduleEnd_of_finiteDimensional
      (K := K) (B := Aᵐᵒᵖ) (M := X)

/-- The canonical duplicate-free complete skeleton of indecomposable right
modules over a finite-dimensional algebra.  Its decomposition field is
constructed from finite module length, rather than assumed. -/
noncomputable def rightIndecomposableSkeleton
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    IndecomposableSkeleton Aᵐᵒᵖ
      (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  exact
    indecomposableSkeletonOfFiniteLength
      (fun X ↦ isFiniteLength_rightFGModule K A X)

/-- The automatic approximation halves for the paper's literal
quotient-closed and subobject-closed additive subcategories. -/
theorem rightModule_automaticApproximations
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    (∀ C : IndecomposableSkeleton.QuotientClosedAdditiveSubcategory.{uA, w}
        (R := Aᵐᵒᵖ),
      IndecomposableSkeleton.IsContravariantlyFinite C.1.carrier) ∧
    (∀ C : IndecomposableSkeleton.SubobjectClosedAdditiveSubcategory.{uA, w}
        (R := Aᵐᵒᵖ),
      IndecomposableSkeleton.IsCovariantlyFinite C.1.carrier) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
  constructor
  · intro C
    exact
      IndecomposableSkeleton.quotientClosedAdditiveSubcategory_isContravariantlyFinite
        σ C
  · intro C
    exact
      IndecomposableSkeleton.subobjectClosedAdditiveSubcategory_isCovariantlyFinite
        σ (fun X ↦ isFiniteLength_rightFGModule K A X) C

/-- The finite-cover input for every finite quotient support over a
finite-dimensional algebra. -/
theorem rightModule_finiteFacCovariantlyFinite
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
    IndecomposableSkeleton.FiniteFacCovariantlyFinite σ := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
  exact
    IndecomposableSkeleton.finiteFacCovariantlyFinite_of_finiteDimensional
      K σ

/-- A quotient-closed subcategory of finitely generated right modules is a
compact element of the closure lattice exactly when it is functorially
finite. -/
theorem rightModule_compact_iff_functoriallyFinite
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    let σ := rightIndecomposableSkeleton.{uK, uA, uA} K A
    ∀ C : σ.qClosure.Closeds,
      IsCompactElement C ↔
        IndecomposableSkeleton.IsFunctoriallyFinite
          (σ.InFac (C : Set (CanonicalIndecomposableIndex Aᵐᵒᵖ))) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  let σ := rightIndecomposableSkeleton.{uK, uA, uA} K A
  change ∀ C : σ.qClosure.Closeds,
    IsCompactElement C ↔
      IndecomposableSkeleton.IsFunctoriallyFinite
        (σ.InFac (C : Set (CanonicalIndecomposableIndex Aᵐᵒᵖ)))
  intro C
  exact
    IndecomposableSkeleton.isCompactElement_iff_inFac_functoriallyFinite_of_finiteDimensional_sameUniverse
      K σ

/-- The two quotient/submodule convex geometries attached canonically to
the isomorphism classes of indecomposable right modules. -/
theorem rightModule_twoConvexGeometries
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
    σ.qClosure.IsConvexGeometry ∧
      σ.sClosure.IsConvexGeometry := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
  letI : ∀ i, Module K (σ.obj i) :=
    fun i ↦ Module.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i, IsScalarTower K Aᵐᵒᵖ (σ.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i, FiniteDimensional K (σ.obj i) :=
    fun i ↦ finiteDimensional_rightFGModule K A (σ.obj i)
  exact
    ⟨QuotientSubmoduleEquidistribution.IndecomposableSkeleton.qClosure_isConvexGeometry_of_finiteDimensional
        (K := K) σ,
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.sClosure_isConvexGeometry_of_finiteDimensional
        (K := K) σ⟩

/-- Canonical right-module form of the paper's infinite structural theorem:
both closure systems are algebraic and spatial, their compact completely
join-irreducibles are the point closures, and compact closed classes have
unique finite bases. -/
theorem rightModule_infiniteConvexStructures
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
    σ.qClosure.InfiniteConvexStructure ∧
      σ.sClosure.InfiniteConvexStructure := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
  letI : ∀ i, Module K (σ.obj i) :=
    fun i ↦ Module.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i, IsScalarTower K Aᵐᵒᵖ (σ.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i, FiniteDimensional K (σ.obj i) :=
    fun i ↦ finiteDimensional_rightFGModule K A (σ.obj i)
  exact
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.quotientSubmodule_infiniteConvexStructures_of_finiteDimensional
      (K := K) σ

/-- Canonical right-module form of the quotient distributivity criterion. -/
theorem rightModule_qDistributiveCriterion
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
    σ.qClosure.ClosedsIsDistributive ↔
      σ.qClosure.IsClosedUnderBinaryUnion ∧
        σ.qClosure.IsUnaryGeneration := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
  letI : ∀ i, Module K (σ.obj i) :=
    fun i ↦ Module.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i, IsScalarTower K Aᵐᵒᵖ (σ.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i, FiniteDimensional K (σ.obj i) :=
    fun i ↦ finiteDimensional_rightFGModule K A (σ.obj i)
  exact
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.qClosure_distributive_iff_union_iff_unaryGeneration
      (K := K) σ

set_option linter.checkUnivs false in
/-- The finite right-module model of a finite-dimensional algebra.  Its two
universe parameters intentionally occur together through the bundled
skeleton. -/
abbrev FiniteRightModuleModel
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :=
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  FiniteIndecomposableSkeleton.{uA, v, w} Aᵐᵒᵖ

/-- Paper-oriented representation-finiteness for right modules.  The
ground field enters only to discharge the Noetherian instance; the content
is finiteness of the canonical type of indecomposable isomorphism classes. -/
def IsRightRepresentationFinite
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] : Prop :=
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  IsRepresentationFinite.{uA, w} Aᵐᵒᵖ

/-- Under conventional representation-finiteness, the canonical quotient
and submodule convex geometries have all finite deletion, cover, grading,
and split-extreme generation consequences from the manuscript. -/
theorem rightRepresentationFinite_finiteConvexConsequences
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hrep : IsRightRepresentationFinite.{uK, uA, w} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
      hrep
    let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
    σ.qClosure.FiniteConvexConsequences ∧
      σ.sClosure.FiniteConvexConsequences := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
    hrep
  let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
  letI : ∀ i, Module K (σ.obj i) :=
    fun i ↦ Module.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i, IsScalarTower K Aᵐᵒᵖ (σ.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i, FiniteDimensional K (σ.obj i) :=
    fun i ↦ finiteDimensional_rightFGModule K A (σ.obj i)
  exact
    ⟨QuotientSubmoduleEquidistribution.IndecomposableSkeleton.qClosure_finiteConvexConsequences_of_finiteDimensional
        (K := K) σ,
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.sClosure_finiteConvexConsequences_of_finiteDimensional
        (K := K) σ⟩

/-- Conventional representation-finiteness constructs the finite complete
right-module skeleton used throughout the formalization. -/
noncomputable def finiteRightModuleModelOfRepresentationFinite
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hrep : IsRightRepresentationFinite.{uK, uA, w} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    FiniteIndecomposableSkeleton Aᵐᵒᵖ := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
    hrep
  exact
    finiteIndecomposableSkeletonOfFiniteLength
      (fun X ↦ isFiniteLength_rightFGModule K A X)

/-- A paper-level chosen-skeleton wrapper with no redundant Noetherian,
module-over-the-field, scalar-tower, or pointwise finite-dimensional
hypotheses. -/
theorem finiteRightModuleModel_twoConvexGeometries
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    ∀ M : FiniteIndecomposableSkeleton.{uA, v, w} Aᵐᵒᵖ,
      M.skeleton.qClosure.IsConvexGeometry ∧
        M.skeleton.sClosure.IsConvexGeometry := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  intro M
  let σ := M.skeleton
  letI : ∀ i : M.ι, Module K (σ.obj i) :=
    fun i ↦ Module.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i : M.ι, IsScalarTower K Aᵐᵒᵖ (σ.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i : M.ι, FiniteDimensional K (σ.obj i) :=
    fun i ↦ finiteDimensional_rightFGModule K A (σ.obj i)
  exact
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.twoConvexGeometries_of_finiteDimensional
      (K := K) σ

/-- The corresponding structural theorem wrapper. -/
theorem finiteRightModuleModel_infiniteConvexStructures
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    ∀ M : FiniteIndecomposableSkeleton.{uA, v, w} Aᵐᵒᵖ,
      M.skeleton.qClosure.InfiniteConvexStructure ∧
        M.skeleton.sClosure.InfiniteConvexStructure := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  intro M
  let σ := M.skeleton
  letI : ∀ i : M.ι, Module K (σ.obj i) :=
    fun i ↦ Module.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i : M.ι, IsScalarTower K Aᵐᵒᵖ (σ.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i : M.ι, FiniteDimensional K (σ.obj i) :=
    fun i ↦ finiteDimensional_rightFGModule K A (σ.obj i)
  exact
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.quotientSubmodule_infiniteConvexStructures_of_finiteDimensional
      (K := K) σ

/-- The finite accessibility, cover, grading, relative-split deletion, and
relative-split generation conclusions for both closure systems. -/
theorem finiteRightModuleModel_finiteConvexConsequences
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    ∀ M : FiniteIndecomposableSkeleton.{uA, v, w} Aᵐᵒᵖ,
      M.skeleton.qClosure.FiniteConvexConsequences ∧
        M.skeleton.sClosure.FiniteConvexConsequences := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  intro M
  let σ := M.skeleton
  letI : ∀ i : M.ι, Module K (σ.obj i) :=
    fun i ↦ Module.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i : M.ι, IsScalarTower K Aᵐᵒᵖ (σ.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i : M.ι, FiniteDimensional K (σ.obj i) :=
    fun i ↦ finiteDimensional_rightFGModule K A (σ.obj i)
  exact
    ⟨QuotientSubmoduleEquidistribution.IndecomposableSkeleton.qClosure_finiteConvexConsequences_of_finiteDimensional
        (K := K) σ,
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.sClosure_finiteConvexConsequences_of_finiteDimensional
        (K := K) σ⟩

/-- The paper's quotient-side distributivity criterion with all outer
finite-dimensional-algebra hypotheses discharged. -/
theorem finiteRightModuleModel_qDistributiveCriterion
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    ∀ M : FiniteIndecomposableSkeleton.{uA, v, w} Aᵐᵒᵖ,
      M.skeleton.qClosure.ClosedsIsDistributive ↔
        M.skeleton.qClosure.IsClosedUnderBinaryUnion ∧
          M.skeleton.qClosure.IsUnaryGeneration := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  intro M
  let σ := M.skeleton
  letI : ∀ i : M.ι, Module K (σ.obj i) :=
    fun i ↦ Module.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i : M.ι, IsScalarTower K Aᵐᵒᵖ (σ.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars K Aᵐᵒᵖ (σ.obj i)
  letI : ∀ i : M.ι, FiniteDimensional K (σ.obj i) :=
    fun i ↦ finiteDimensional_rightFGModule K A (σ.obj i)
  exact
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.qClosure_distributive_iff_union_iff_unaryGeneration
      (K := K) σ

/-- The strong and weak conjectures can be stated directly on the bundled
finite model. -/
def FiniteRightModuleModel.Equidistribution
    {K : Type uK} {A : Type uA}
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (M : FiniteRightModuleModel.{uK, uA, v, w} K A) : Prop :=
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  M.skeleton.HasQuotientSubmoduleEquidistribution

def FiniteRightModuleModel.WeakEquidistribution
    {K : Type uK} {A : Type uA}
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (M : FiniteRightModuleModel.{uK, uA, v, w} K A) : Prop :=
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  M.skeleton.WeakQuotientSubmoduleEquidistribution

/-- The paper's strong conjecture stated on the canonical indecomposable
isomorphism classes of a representation-finite algebra. -/
def RightQuotientSubmoduleEquidistribution
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hrep : IsRightRepresentationFinite.{uK, uA, w} K A) : Prop :=
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
    hrep
  (rightIndecomposableSkeleton.{uK, uA, w} K A).HasQuotientSubmoduleEquidistribution

/-- The paper's weak counting conjecture on the canonical
indecomposable isomorphism classes. -/
def RightWeakQuotientSubmoduleEquidistribution
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hrep : IsRightRepresentationFinite.{uK, uA, w} K A) : Prop :=
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
    hrep
  (rightIndecomposableSkeleton.{uK, uA, w} K A).WeakQuotientSubmoduleEquidistribution

/-- The strong canonical conjecture implies the weak canonical conjecture. -/
theorem rightQuotientSubmoduleEquidistribution_implies_weak
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hrep : IsRightRepresentationFinite.{uK, uA, w} K A) :
    RightQuotientSubmoduleEquidistribution K A hrep →
      RightWeakQuotientSubmoduleEquidistribution K A hrep := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
    hrep
  exact
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.quotientSubmoduleEquidistribution_implies_weak
      (rightIndecomposableSkeleton.{uK, uA, w} K A)

end QuotientSubmoduleEquidistribution
