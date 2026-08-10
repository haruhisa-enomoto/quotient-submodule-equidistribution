import OpConjecture.RepresentationTheory.FamilyThreeSpecialization
import OpConjecture.RepresentationTheory.TwoTargetSourceRank

noncomputable section

set_option linter.unusedSectionVars false

open Set
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace OpConjecture.FamilyThreeSpecialization

universe x

variable {K A : Type x}
  [Field K] [IsAlgClosed K]
  [Ring A] [Algebra K A] [FiniteDimensional K A]

variable [IsNoetherianRing Aᵐᵒᵖ] [IsArtinianRing Aᵐᵒᵖ]
  {ι : Type x} [Finite ι]
  (σ : OpConjecture.IndecomposableSkeleton.{x, x, x} Aᵐᵒᵖ ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The paper-facing top-simplicity consequence of the pure source-rank
bound for an idempotent-indecomposable two-target fork. -/
theorem moduleTop_isSimple_of_twoTargetModel
    {R M V W Z : Type x}
    [Ring R]
    [AddCommGroup M] [Module R M]
    [Nontrivial M] [Module.Finite R M] [IsArtinian R M]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    [AddCommGroup Z] [Module K Z]
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K Z]
    (f : V →ₗ[K] W) (g : V →ₗ[K] Z)
    (hfg : OpConjecture.LoewyTwoRankCore.IsTwoTargetIdempotentIndecomposable
      f g)
    (hsourceLength :
      (Module.finrank K V : ℕ∞) =
        Module.length R (M ⧸ Module.jacobson R M)) :
    IsSimpleModule R (M ⧸ Module.jacobson R M) := by
  let J : Submodule R M := Module.jacobson R M
  have hJneTop : J ≠ ⊤ :=
    (Module.jacobson_lt_top R M).ne
  letI : Nontrivial (M ⧸ J) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    exact hJneTop
      (Submodule.Quotient.subsingleton_iff.mp hsub)
  have hlengthPos :
      0 < Module.length R (M ⧸ J) :=
    Module.length_pos_iff.mpr inferInstance
  have hsource :
      Module.finrank K V ≤ 1 :=
    OpConjecture.LoewyTwoRankCore.twoTarget_source_finrank_le_one hfg
  have hlengthLe :
      Module.length R (M ⧸ J) ≤ 1 := by
    rw [← hsourceLength]
    exact ENat.coe_le_coe.mpr hsource
  have hlength :
      Module.length R (M ⧸ J) = 1 :=
    le_antisymm hlengthLe
      (Order.one_le_iff_ne_zero.mpr hlengthPos.ne')
  exact Module.length_eq_one_iff.mp hlength

/-- A two-target semisimple decomposition of the radical, together with an
isotypic decomposition of the top, produces the fork to which the source-rank
bound applies. -/
theorem moduleTop_isSimple_of_twoTargetDecomposition
    (hnoParallel :
      OpConjecture.LoewyTwoRankCore.NoParallelExtOne σ K)
    {j s t r : ι}
    (hs : Simple (σ.obj s)) (ht : Simple (σ.obj t))
    (hr : Simple (σ.obj r))
    {J L I : Type} [Fintype J] [Fintype L] [Fintype I]
    (eRadical :
      ((J → σ.obj s) × (L → σ.obj t)) ≃ₗ[Aᵐᵒᵖ]
        σ.moduleRadical j)
    (eTop : (I → σ.obj r) ≃ₗ[Aᵐᵒᵖ] σ.moduleTop j)
    (hsourceLength :
      (Module.finrank K (I → K) : ℕ∞) =
        Module.length Aᵐᵒᵖ (σ.moduleTop j)) :
    IsSimpleModule Aᵐᵒᵖ (σ.moduleTop j) := by
  classical
  let leftIso :
      ((⨁ fun _ : J ↦ (σ.obj s).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (J → σ.obj s) :=
    ModuleCat.biproductIsoPi (fun _ : J ↦ (σ.obj s).obj)
  let rightIso :
      ((⨁ fun _ : L ↦ (σ.obj t).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (L → σ.obj t) :=
    ModuleCat.biproductIsoPi (fun _ : L ↦ (σ.obj t).obj)
  let radicalIso :
      (((⨁ fun _ : J ↦ (σ.obj s).obj) ⊞
          (⨁ fun _ : L ↦ (σ.obj t).obj)) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (σ.moduleRadical j) :=
    biprod.mapIso leftIso rightIso ≪≫
      ModuleCat.biprodIsoProd
        (ModuleCat.of Aᵐᵒᵖ (J → σ.obj s))
        (ModuleCat.of Aᵐᵒᵖ (L → σ.obj t)) ≪≫
      eRadical.toModuleIso
  let topIso :
      ((⨁ fun _ : I ↦ (σ.obj r).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (σ.moduleTop j) :=
    ModuleCat.biproductIsoPi
        (fun _ : I ↦ (σ.obj r).obj) ≪≫
      eTop.toModuleIso
  let eRadical' :
      ((((⨁ fun _ : J ↦ (σ.obj s).obj) ⊞
          (⨁ fun _ : L ↦ (σ.obj t).obj)) :
          ModuleCat.{x} Aᵐᵒᵖ)) ≃ₗ[Aᵐᵒᵖ]
        σ.moduleRadical j :=
    radicalIso.toLinearEquiv
  let eMiddle : (σ.obj j) ≃ₗ[Aᵐᵒᵖ] (σ.obj j) :=
    LinearEquiv.refl Aᵐᵒᵖ (σ.obj j)
  let eTop' :
      (((⨁ fun _ : I ↦ (σ.obj r).obj) :
          ModuleCat.{x} Aᵐᵒᵖ)) ≃ₗ[Aᵐᵒᵖ]
        σ.moduleTop j :=
    topIso.toLinearEquiv
  let radicalInclusion :
      σ.moduleRadical j →ₗ[Aᵐᵒᵖ] σ.obj j :=
    (σ.moduleRadical j).subtype
  let topProjection :
      σ.obj j →ₗ[Aᵐᵒᵖ] σ.moduleTop j :=
    (σ.moduleRadical j).mkQ
  have hexact : Function.Exact radicalInclusion topProjection :=
    LinearMap.exact_subtype_mkQ (σ.moduleRadical j)
  let SC : ShortComplex (ModuleCat.{x} Aᵐᵒᵖ) :=
    ModuleCat.shortComplexOfConj
      eRadical' eMiddle eTop' radicalInclusion topProjection
      hexact.linearMap_comp_eq_zero
  have hSC : SC.ShortExact :=
    ModuleCat.shortComplexOfConj_shortExact
      eRadical' eMiddle eTop' radicalInclusion topProjection
      hexact (σ.moduleRadical j).subtype_injective
      (σ.moduleRadical j).mkQ_surjective
  have hSC' : (ShortComplex.mk SC.f SC.g SC.zero).ShortExact := by
    simpa only [SC] using hSC
  letI : IsNoetherian Aᵐᵒᵖ (σ.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength j)).1
  letI : IsArtinian Aᵐᵒᵖ (σ.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength j)).2
  have hExtLeft := hnoParallel hr hs
  have hExtRight := hnoParallel hr ht
  letI : FiniteDimensional K
      (Ext (σ.obj r).obj (σ.obj s).obj 1) := hExtLeft.1
  letI : FiniteDimensional K
      (Ext (σ.obj r).obj (σ.obj t).obj 1) := hExtRight.1
  obtain ⟨ell, hell⟩ :=
    OpConjecture.YonedaExtReflection.exists_injective_linearMap_to_field_of_finrank_le_one
      hExtLeft.2
  obtain ⟨ell', hell'⟩ :=
    OpConjecture.YonedaExtReflection.exists_injective_linearMap_to_field_of_finrank_le_one
      hExtRight.2
  letI : IsSimpleModule Aᵐᵒᵖ (σ.obj s) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp hs
  letI : IsSimpleModule Aᵐᵒᵖ (σ.obj t) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp ht
  letI : IsSimpleModule Aᵐᵒᵖ (σ.obj r) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp hr
  letI : Simple (σ.obj s).obj :=
    (simple_iff_isSimpleModule' (σ.obj s).obj).mpr inferInstance
  letI : Simple (σ.obj t).obj :=
    (simple_iff_isSimpleModule' (σ.obj t).obj).mpr inferInstance
  letI : Simple (σ.obj r).obj :=
    (simple_iff_isSimpleModule' (σ.obj r).obj).mpr inferInstance
  have hsNonzero : 𝟙 (σ.obj s).obj ≠ 0 :=
    CategoryTheory.id_nonzero (σ.obj s).obj
  have htNonzero : 𝟙 (σ.obj t).obj ≠ 0 :=
    CategoryTheory.id_nonzero (σ.obj t).obj
  have hrNonzero : 𝟙 (σ.obj r).obj ≠ 0 :=
    CategoryTheory.id_nonzero (σ.obj r).obj
  have hfork :=
    OpConjecture.YonedaExtReflection.shortExact_twoTargetScalarizedExtLinearMaps_isIdempotentIndecomposable
      (σ.obj r).obj (σ.obj s).obj (σ.obj t).obj (σ.obj j).obj
      hrNonzero hsNonzero htNonzero
      SC.f SC.g SC.zero hSC' (σ.indecomposable j)
      ell hell ell' hell'
  letI : Nontrivial (σ.obj j) :=
    (σ.indecomposable j).nontrivial
  change
    (Module.finrank K (I → K) : ℕ∞) =
      Module.length Aᵐᵒᵖ
        ((σ.obj j) ⧸ Module.jacobson Aᵐᵒᵖ (σ.obj j))
    at hsourceLength
  exact
    moduleTop_isSimple_of_twoTargetModel
      (K := K) (R := Aᵐᵒᵖ) (M := σ.obj j)
      (OpConjecture.YonedaExtReflection.firstTargetScalarizedExtLinearMap
        (σ.obj r).obj (σ.obj s).obj (σ.obj t).obj ell hSC'.extClass)
      (OpConjecture.YonedaExtReflection.secondTargetScalarizedExtLinearMap
        (σ.obj r).obj (σ.obj s).obj (σ.obj t).obj ell' hSC'.extClass)
      hfork (by simpa using hsourceLength)

include K in
/-- Every indecomposable generated by the Gabriel common-source-pair support
has simple top.  This discharges the exact collective condition left open by
the combinatorial family-3 reduction. -/
theorem moduleTop_isSimple_of_inFac_gabrielCommonSourcePair
    (p : σ.CommonSourcePair
      (OpConjecture.GabrielArrowBridge.LengthTwo.source
        (A := Aᵐᵒᵖ) σ))
    {j : ι}
    (hj : σ.InFac
      (σ.commonSourcePairSupport
        (OpConjecture.GabrielArrowBridge.LengthTwo.source
          (A := Aᵐᵒᵖ) σ) p)
      (σ.obj j)) :
    IsSimpleModule Aᵐᵒᵖ (σ.moduleTop j) := by
  classical
  obtain ⟨e₁, e₂, _hne, hp⟩ :=
    CommonSourcePair.exists_two_edges (A := A) σ p
  obtain ⟨J, L, hJ, hL, ⟨eRadical⟩⟩ :=
    exists_moduleRadical_twoTargetDecomposition_of_edges
      (A := A) σ p e₁ e₂ hp hj
  letI : Fintype J := hJ
  letI : Fintype L := hL
  letI : IsSimpleModule Aᵐᵒᵖ (σ.obj p.1.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      p.1.2
  have htopIsotypic :
      IsIsotypicOfType Aᵐᵒᵖ (σ.moduleTop j) (σ.obj p.1.1) :=
    σ.moduleTop_isIsotypicOfType_of_inFac_commonSourcePair
      (fun e ↦
        OpConjecture.GabrielArrowBridge.LengthTwo.quotient
          (A := Aᵐᵒᵖ) σ e)
      p hj
  letI : IsSemisimpleModule Aᵐᵒᵖ (σ.moduleTop j) :=
    σ.moduleTop_isSemisimple j
  letI : Module.Finite Aᵐᵒᵖ (σ.moduleTop j) := inferInstance
  obtain ⟨k, eTop, htopLength⟩ :=
    OpConjecture.LoewyTwoRankCore.exists_isotypicMultiplicity
      htopIsotypic
  have hnoParallel :
      OpConjecture.LoewyTwoRankCore.NoParallelExtOne σ K :=
    OpConjecture.NoParallelExtOne.noParallelExtOne_of_finiteDimensional_of_finiteSkeleton
      K A σ
  apply moduleTop_isSimple_of_twoTargetDecomposition
    (K := K) σ hnoParallel
    (OpConjecture.GabrielArrowBridge.LengthTwo.target
      (A := Aᵐᵒᵖ) σ e₁.1).2
    (OpConjecture.GabrielArrowBridge.LengthTwo.target
      (A := Aᵐᵒᵖ) σ e₂.1).2
    p.1.2 eRadical.symm eTop.symm
  simpa using htopLength

include K in
/-- The exact family-3 simple-top condition, now unconditional under the
paper's finite-dimensional algebraically closed hypotheses. -/
theorem gabrielCommonSourcePairFacTargetsHaveSimpleTop
    (p : σ.CommonSourcePair
      (OpConjecture.GabrielArrowBridge.LengthTwo.source
        (A := Aᵐᵒᵖ) σ)) :
    σ.CommonSourcePairFacTargetsHaveSimpleTop
      (OpConjecture.GabrielArrowBridge.LengthTwo.source
        (A := Aᵐᵒᵖ) σ) p := by
  intro j hj
  exact moduleTop_isSimple_of_inFac_gabrielCommonSourcePair
    (K := K) σ p hj

include K in
/-- The common-source-pair support is quotient-closed. -/
theorem qClosure_isClosed_gabrielCommonSourcePairSupport
    (p : σ.CommonSourcePair
      (OpConjecture.GabrielArrowBridge.LengthTwo.source
        (A := Aᵐᵒᵖ) σ)) :
    σ.qClosure.IsClosed
      (σ.commonSourcePairSupport
        (OpConjecture.GabrielArrowBridge.LengthTwo.source
          (A := Aᵐᵒᵖ) σ) p) := by
  exact
    (σ.qClosure_isClosed_commonSourcePairSupport_iff_targetsHaveSimpleTop
      (fun e ↦
        OpConjecture.GabrielArrowBridge.LengthTwo.quotient
          (A := Aᵐᵒᵖ) σ e)
      p).2
      (gabrielCommonSourcePairFacTargetsHaveSimpleTop
        (K := K) σ p)

include K in
/-- Unconditional realization of formal family 3 in the actual third
quotient-closure level. -/
noncomputable def gabrielCommonSourcePairToClosedLevelThree :
    σ.CommonSourcePair
        (OpConjecture.GabrielArrowBridge.LengthTwo.source
          (A := Aᵐᵒᵖ) σ) →
      OpConjecture.BottomLevels.BottomThreeAdapter.ClosedLevelThree
        σ.qClosure :=
  σ.commonSourcePairToClosedLevelThree
    (fun e ↦
      OpConjecture.GabrielArrowBridge.LengthTwo.quotient
        (A := Aᵐᵒᵖ) σ e)
    (fun p ↦
      gabrielCommonSourcePairFacTargetsHaveSimpleTop
        (K := K) σ p)

include K in
/-- Distinct formal common-source pairs give distinct closed level-three
subcategories. -/
theorem gabrielCommonSourcePairToClosedLevelThree_injective :
    Function.Injective
      (gabrielCommonSourcePairToClosedLevelThree (K := K) σ) := by
  exact
    σ.commonSourcePairToClosedLevelThree_injective
      (fun e ↦
        OpConjecture.GabrielArrowBridge.LengthTwo.quotient
          (A := Aᵐᵒᵖ) σ e)
      (fun p ↦
        gabrielCommonSourcePairFacTargetsHaveSimpleTop
          (K := K) σ p)

end OpConjecture.FamilyThreeSpecialization
