import QuotientSubmoduleEquidistribution.RepresentationTheory.AnnihilatorInflation
import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulCore
import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulRegularSubobject

/-!
# Concrete faithful normal forms

This module proves that, on quotient-closed and submodule-closed
supports in a finite indecomposable skeleton, annihilator-zero faithfulness
is respectively equivalent to containing every indecomposable injective or
every indecomposable projective.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore

universe u v

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
  {ι : Type v} [Finite ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

include K in
/-- For a finite-dimensional algebra, a quotient-closed support is faithful
exactly when it contains every indecomposable injective, and a
submodule-closed support is faithful exactly when it contains every
indecomposable projective. -/
theorem closedFaithfulNormalForm :
    ClosedFaithfulNormalForm σ
      (AnnihilatorInflation.IsFaithfulSupport σ.obj)
      (AnnihilatorInflation.IsFaithfulSupport σ.obj) where
  quotient_iff := by
    intro C
    constructor
    · intro hC i hi
      let B : IndecomposableSkeleton.FiniteSupport (ι := ι) :=
        ⟨(C : Set ι), Set.toFinite _⟩
      have hAnn :
          Module.annihilator R (σ.basicModule B) = ⊥ :=
        (AnnihilatorInflation.Skeleton.isFaithfulSupport_iff_annihilator_basicModule_eq_bot
          σ B).1
          (by simpa [B] using hC)
      letI : Module K (σ.basicModule B) :=
        Module.restrictScalars K R _
      letI : IsScalarTower K R (σ.basicModule B) :=
        IsScalarTower.restrictScalars K R _
      letI : SMulCommClass R K (σ.basicModule B) := inferInstance
      letI : FiniteDimensional K (σ.basicModule B) :=
        Module.Finite.trans R _
      have hRegular :
          IndecomposableSkeleton.InSubOfModule
            (σ.basicModule B) (regularFGModule (R := R)) :=
        FaithfulRegularEmbedding.regular_inSubOfModule_of_annihilator_eq_bot
            K R (σ.basicModule B) hAnn
      have hFac :
          IndecomposableSkeleton.InFacOfModule
            (σ.basicModule B) (σ.obj i) :=
        injective_inFacOfModule_of_regular_inSub
          (R := R) (σ.basicModule B) (σ.obj i) hRegular hi
      have hiClosure : i ∈ σ.qClosure (C : Set ι) :=
        (σ.inFacOfModule_basicModule_iff B (σ.obj i)).1 hFac
      rw [C.property.closure_eq] at hiClosure
      exact hiClosure
    · intro hInjectives
      apply AnnihilatorInflation.isFaithfulSupport_monotone σ.obj
        hInjectives
      have hAnn :
          Module.annihilator R (injectiveCogenerator σ) = ⊥ :=
        annihilator_injectiveCogenerator_eq_bot σ K
      exact
        (AnnihilatorInflation.Skeleton.isFaithfulSupport_iff_annihilator_basicModule_eq_bot σ
            (injectiveCogeneratorSupport σ)).2 hAnn
  submodule_iff := by
    intro C
    constructor
    · intro hC i hi
      let B : IndecomposableSkeleton.FiniteSupport (ι := ι) :=
        ⟨(C : Set ι), Set.toFinite _⟩
      have hAnn :
          Module.annihilator R (σ.basicModule B) = ⊥ :=
        (AnnihilatorInflation.Skeleton.isFaithfulSupport_iff_annihilator_basicModule_eq_bot
          σ B).1
          (by simpa [B] using hC)
      letI : Module K (σ.basicModule B) :=
        Module.restrictScalars K R _
      letI : IsScalarTower K R (σ.basicModule B) :=
        IsScalarTower.restrictScalars K R _
      letI : SMulCommClass R K (σ.basicModule B) := inferInstance
      letI : FiniteDimensional K (σ.basicModule B) :=
        Module.Finite.trans R _
      have hRegular :
          IndecomposableSkeleton.InSubOfModule
            (σ.basicModule B) (regularFGModule (R := R)) :=
        FaithfulRegularEmbedding.regular_inSubOfModule_of_annihilator_eq_bot
            K R (σ.basicModule B) hAnn
      have hSub :
          IndecomposableSkeleton.InSubOfModule
            (σ.basicModule B) (σ.obj i) :=
        projective_inSubOfModule_of_regular_inSub
          (R := R) (σ.basicModule B) (σ.obj i) hRegular hi
      have hiClosure : i ∈ σ.sClosure (C : Set ι) :=
        (σ.inSubOfModule_basicModule_iff B (σ.obj i)).1 hSub
      rw [C.property.closure_eq] at hiClosure
      exact hiClosure
    · intro hProjectives
      apply AnnihilatorInflation.isFaithfulSupport_monotone σ.obj
        hProjectives
      have hAnn :
          Module.annihilator R (projectiveGenerator σ) = ⊥ :=
        annihilator_projectiveGenerator_eq_bot σ
      exact
        (AnnihilatorInflation.Skeleton.isFaithfulSupport_iff_annihilator_basicModule_eq_bot σ
            (projectiveGeneratorSupport σ)).2 hAnn

include K in
/-- The unconditional quotient-side minimal faithful core data. -/
def concreteQuotientCoreData :
    QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.Data
      σ.qClosure (AnnihilatorInflation.IsFaithfulSupport σ.obj) :=
  quotientCoreData σ (closedFaithfulNormalForm (K := K) σ)

include K in
/-- The unconditional submodule-side minimal faithful core data. -/
def concreteSubmoduleCoreData :
    QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.Data
      σ.sClosure (AnnihilatorInflation.IsFaithfulSupport σ.obj) :=
  submoduleCoreData σ (closedFaithfulNormalForm (K := K) σ)

include K in
/-- Ringel's core-cardinality comparison settles the faithful counts at
every level not exceeding the common core size. -/
theorem faithfulLevelCount_eq_of_ringel_of_level_le
    (hRingel : RingelCoreCardinality σ)
    {n : ℕ}
    (hn : n ≤ (quotientCore σ : Set ι).ncard) :
    QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        σ.qClosure (AnnihilatorInflation.IsFaithfulSupport σ.obj) n =
      QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        σ.sClosure (AnnihilatorInflation.IsFaithfulSupport σ.obj) n := by
  let hNormal := closedFaithfulNormalForm (K := K) σ
  let Q := concreteQuotientCoreData (K := K) σ
  let S := concreteSubmoduleCoreData (K := K) σ
  apply
    QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.faithfulLevelCount_eq_of_core_ncard_eq_of_level_le
      Q S
  · exact core_ncard_eq_of_ringel σ hNormal hRingel
  · simpa only [Q, concreteQuotientCoreData, quotientCoreData_core] using hn

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore
