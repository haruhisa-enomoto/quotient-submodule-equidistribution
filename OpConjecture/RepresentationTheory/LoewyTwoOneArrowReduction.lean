import OpConjecture.RepresentationTheory.LoewyTwoYonedaBridge
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace OpConjecture.YonedaOneArrowReduction

universe x

variable {A : Type x} [Ring A]
  {ι : Type x} [IsNoetherianRing Aᵐᵒᵖ]
  (σ :
    _root_.OpConjecture.IndecomposableSkeleton.{x, x, x}
      Aᵐᵒᵖ ι)
  (K : Type x) [Field K] [IsAlgClosed K]
  [Algebra K A] [FiniteDimensional K A]

open LoewyTwoRankCore

/--
No-parallel `Ext¹` supplies the one-arrow model for every indecomposable
whose top and radical are isotypic semisimple modules.
-/
theorem noParallelExtOneArrowReduction :
    NoParallelExtOneArrowReduction σ K := by
  intro hnoParallel j s t hs ht htop hradSemisimple hradIsotypic
  letI : IsSimpleModule Aᵐᵒᵖ (σ.obj s) :=
    (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (σ.obj s)).mp hs
  letI : IsSimpleModule Aᵐᵒᵖ (σ.obj t) :=
    (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (σ.obj t)).mp ht
  letI : IsSemisimpleModule Aᵐᵒᵖ (σ.moduleTop j) :=
    σ.moduleTop_isSemisimple j
  letI : IsSemisimpleModule Aᵐᵒᵖ (σ.moduleRadical j) :=
    hradSemisimple
  obtain ⟨n, eTop, htopLength⟩ :=
    exists_isotypicMultiplicity htop
  obtain ⟨m, eRadical, _⟩ :=
    exists_isotypicMultiplicity hradIsotypic
  let topIso :
      ModuleCat.of Aᵐᵒᵖ (σ.moduleTop j) ≅
        (⨁ fun _ : Fin n ↦ (σ.obj s).obj) :=
    eTop.toModuleIso ≪≫
      (ModuleCat.biproductIsoPi
        (fun _ : Fin n ↦ (σ.obj s).obj)).symm
  let radicalIso :
      ModuleCat.of Aᵐᵒᵖ (σ.moduleRadical j) ≅
        (⨁ fun _ : Fin m ↦ (σ.obj t).obj) :=
    eRadical.toModuleIso ≪≫
      (ModuleCat.biproductIsoPi
        (fun _ : Fin m ↦ (σ.obj t).obj)).symm
  let eRadical :
      ((⨁ fun _ : Fin m ↦ (σ.obj t).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≃ₗ[Aᵐᵒᵖ]
        σ.moduleRadical j :=
    radicalIso.symm.toLinearEquiv
  let eMiddle : (σ.obj j) ≃ₗ[Aᵐᵒᵖ] (σ.obj j) :=
    LinearEquiv.refl Aᵐᵒᵖ (σ.obj j)
  let eTop :
      ((⨁ fun _ : Fin n ↦ (σ.obj s).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≃ₗ[Aᵐᵒᵖ]
        σ.moduleTop j :=
    topIso.symm.toLinearEquiv
  let radicalInclusion :
      σ.moduleRadical j →ₗ[Aᵐᵒᵖ] σ.obj j :=
    (σ.moduleRadical j).subtype
  let topProjection :
      σ.obj j →ₗ[Aᵐᵒᵖ] σ.moduleTop j :=
    (σ.moduleRadical j).mkQ
  have hexact : Function.Exact radicalInclusion topProjection :=
    LinearMap.exact_subtype_mkQ (σ.moduleRadical j)
  let S : ShortComplex (ModuleCat.{x} Aᵐᵒᵖ) :=
    ModuleCat.shortComplexOfConj
      eRadical eMiddle eTop radicalInclusion topProjection
      hexact.linearMap_comp_eq_zero
  have hS : S.ShortExact :=
    ModuleCat.shortComplexOfConj_shortExact
      eRadical eMiddle eTop radicalInclusion topProjection
      hexact (σ.moduleRadical j).subtype_injective
      (σ.moduleRadical j).mkQ_surjective
  have hS' :
      (ShortComplex.mk S.f S.g S.zero).ShortExact := by
    simpa only [S] using hS
  letI : IsNoetherian Aᵐᵒᵖ (σ.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength j)).1
  letI : IsArtinian Aᵐᵒᵖ (σ.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength j)).2
  have hExt := hnoParallel hs ht
  letI : FiniteDimensional K
      (Ext (σ.obj s).obj (σ.obj t).obj 1) :=
    hExt.1
  obtain ⟨ℓ, hℓ⟩ :=
    YonedaExtReflection.exists_injective_linearMap_to_field_of_finrank_le_one
      hExt.2
  letI : Simple (σ.obj s).obj :=
    (simple_iff_isSimpleModule' (σ.obj s).obj).mpr inferInstance
  letI : Simple (σ.obj t).obj :=
    (simple_iff_isSimpleModule' (σ.obj t).obj).mpr inferInstance
  have hsNonzero : 𝟙 (σ.obj s).obj ≠ 0 :=
    CategoryTheory.id_nonzero (σ.obj s).obj
  have htNonzero : 𝟙 (σ.obj t).obj ≠ 0 :=
    CategoryTheory.id_nonzero (σ.obj t).obj
  let arrow : (Fin n → K) →ₗ[K] (Fin m → K) :=
    YonedaExtReflection.scalarizedExtLinearMap
      (σ.obj s).obj (σ.obj t).obj ℓ hS'.extClass
  have harrow :
      LoewyTwoRankCore.IsIdempotentIndecomposable arrow :=
    YonedaExtReflection.shortExact_scalarizedExtLinearMap_isIdempotentIndecomposable
      (σ.obj s).obj (σ.obj t).obj (σ.obj j).obj
      hsNonzero htNonzero S.f S.g S.zero hS'
      (σ.indecomposable j) ℓ hℓ
  refine ⟨Fin n → K, Fin m → K, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    arrow, harrow, ?_⟩
  simpa using htopLength

end OpConjecture.YonedaOneArrowReduction
