import OpConjecture.RepresentationTheory.NoLoopNakayamaReduction
import OpConjecture.RepresentationTheory.ProjectiveSimpleRecognition

/-!
# Ext-degree Nakayama reduction

This file isolates the general finite-length and projective-quotient arguments
from the remaining Gabriel-quiver input.  It characterizes a Nakayama skeleton
by simple indecomposable tops and indecomposable nonzero radicals, and records
the exact two radical-layer fork-extraction statements which would let
Ext-Gabriel in/out-degree one force that characterization.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.ExtDegreeNakayamaReduction

universe u v

variable {R : Type u} [Ring R]

/-- Uniseriality is invariant under a linear equivalence. -/
theorem isUniserialModule_congr
    {M N : Type v}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N)
    (hM : OpConjecture.IsUniserialModule R M) :
    OpConjecture.IsUniserialModule R N := by
  unfold OpConjecture.IsUniserialModule at hM ⊢
  constructor
  intro P Q
  rcases hM.total
      (Submodule.comap e.toLinearMap P)
      (Submodule.comap e.toLinearMap Q) with hPQ | hQP
  · left
    exact
      (Submodule.comap_le_comap_iff_of_surjective
        e.surjective).mp hPQ
  · right
    exact
      (Submodule.comap_le_comap_iff_of_surjective
        e.surjective).mp hQP

/-- The zero module is uniserial, expressed for an arbitrary module whose
underlying additive group is subsingleton. -/
theorem isUniserialModule_of_subsingleton
    {M : Type v} [AddCommGroup M] [Module R M]
    [Subsingleton M] :
    OpConjecture.IsUniserialModule R M := by
  unfold OpConjecture.IsUniserialModule
  constructor
  intro P Q
  left
  exact Subsingleton.elim P Q ▸ le_rfl

variable [IsNoetherianRing R]
  {ι : Type v}
  (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} R ι)

/-- The objectwise top condition in the radical-chain characterization of
a Nakayama skeleton. -/
def AllIndecomposableTopsSimple : Prop :=
  ∀ i : ι,
    IsSimpleModule R
      ((σ.obj i) ⧸ Module.jacobson R (σ.obj i))

/-- The objectwise radical condition in the radical-chain characterization
of a Nakayama skeleton. -/
def AllNonzeroRadicalsIndecomposable : Prop :=
  ∀ i : ι,
    Module.jacobson R (σ.obj i) ≠ ⊥ →
      OpConjecture.Foundation.IsIndecomposableModule R
        (Module.jacobson R (σ.obj i))

/-- Simple tops and indecomposable nonzero radicals recursively force every
chosen indecomposable to be uniserial. -/
theorem isNakayamaSkeleton_of_simpleTops_of_indecRadicals
    (hTop : AllIndecomposableTopsSimple σ)
    (hRadical : AllNonzeroRadicalsIndecomposable σ) :
    OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton σ := by
  classical
  intro i
  let measure : ι → ℕ := σ.compositionLength
  apply
    (WellFounded.onFun (f := measure)
      (wellFounded_lt : WellFounded ((· < ·) : ℕ → ℕ → Prop))).induction i
  intro i ih
  obtain ⟨hNoetherianI, hArtinianI⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength i)
  letI : IsNoetherian R (σ.obj i) := hNoetherianI
  letI : IsArtinian R (σ.obj i) := hArtinianI
  let J : Submodule R (σ.obj i) := Module.jacobson R (σ.obj i)
  have hTopI : IsSimpleModule R ((σ.obj i) ⧸ J) := hTop i
  by_cases hJ : J = ⊥
  · haveI : Subsingleton J := by
      constructor
      intro x y
      apply Subtype.ext
      have hx : (x : σ.obj i) = 0 := by
        have hxBot : (x : σ.obj i) ∈
            (⊥ : Submodule R (σ.obj i)) := by
          rw [← hJ]
          exact x.2
        simpa using hxBot
      have hy : (y : σ.obj i) = 0 := by
        have hyBot : (y : σ.obj i) ∈
            (⊥ : Submodule R (σ.obj i)) := by
          rw [← hJ]
          exact y.2
        simpa using hyBot
      exact hx.trans hy.symm
    exact
      OpConjecture.NoLoopNakayamaReduction.isUniserialModule_of_simpleTop_of_radicalUniserial
        hTopI isUniserialModule_of_subsingleton
  · have hJIndec : OpConjecture.Foundation.IsIndecomposableModule R J :=
      hRadical i hJ
    let Jfg : FGModuleCat.{u} R := FGModuleCat.of R J
    obtain ⟨j, ⟨e⟩⟩ := σ.complete Jfg hJIndec
    have hJlt : measure j < measure i := by
      have hLengthEq :
          Module.length R J = Module.length R (σ.obj j) :=
        LinearEquiv.length_eq
          (FGModuleCat.isoToLinearEquiv e)
      have hJProper : J ≠ ⊤ := by
        letI : Nontrivial (σ.obj i) := (σ.indecomposable i).nontrivial
        exact (Module.jacobson_lt_top R (σ.obj i)).ne
      apply ENat.coe_lt_coe.mp
      rw [σ.coe_compositionLength j,
        σ.coe_compositionLength i, ← hLengthEq]
      exact Submodule.length_lt hJProper
    have hRepUniserial :
        OpConjecture.IsUniserialModule R (σ.obj j) :=
      ih j hJlt
    have hJUniserial : OpConjecture.IsUniserialModule R J :=
      isUniserialModule_congr
        (FGModuleCat.isoToLinearEquiv e).symm hRepUniserial
    exact
      OpConjecture.NoLoopNakayamaReduction.isUniserialModule_of_simpleTop_of_radicalUniserial
        hTopI hJUniserial

/-- A Nakayama skeleton has simple tops. -/
theorem simpleTops_of_isNakayamaSkeleton
    (hNakayama :
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton σ) :
    AllIndecomposableTopsSimple σ := by
  intro i
  exact σ.moduleTop_isSimple_of_isUniserial (hNakayama i)

/-- A Nakayama skeleton has indecomposable nonzero radicals. -/
theorem indecRadicals_of_isNakayamaSkeleton
    (hNakayama :
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton σ) :
    AllNonzeroRadicalsIndecomposable σ := by
  intro i hJ
  let J : Submodule R (σ.obj i) := Module.jacobson R (σ.obj i)
  letI : Nontrivial J := by
    rw [Submodule.nontrivial_iff_ne_bot]
    exact hJ
  have hJUniserial : OpConjecture.IsUniserialModule R J :=
    OpConjecture.IsUniserialModule.submodule (hNakayama i) J
  exact hJUniserial.isIndecomposableModule

/-- Exact finite-length radical-chain characterization. -/
theorem isNakayamaSkeleton_iff_simpleTops_and_indecRadicals :
    OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton σ ↔
      AllIndecomposableTopsSimple σ ∧
        AllNonzeroRadicalsIndecomposable σ := by
  constructor
  · intro h
    exact
      ⟨simpleTops_of_isNakayamaSkeleton σ h,
        indecRadicals_of_isNakayamaSkeleton σ h⟩
  · rintro ⟨hTop, hRadical⟩
    exact
      isNakayamaSkeleton_of_simpleTops_of_indecRadicals
        σ hTop hRadical

/-! ## Projective-quotient form of the reduction -/

/-- A map to a finite module with simple top is epic as soon as its
composite with the radical quotient is epic. -/
theorem epi_of_comp_radicalQuotient_epi_of_simpleTop
    {X Y : FGModuleCat.{u} R}
    (hTop :
      IsSimpleModule R (Y ⧸ Module.jacobson R Y))
    (f : X ⟶ Y)
    [Epi
      (f ≫ FGModuleCat.ofHom
        (Module.jacobson R Y).mkQ)] :
    Epi f := by
  apply
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective f).mpr
  rw [← LinearMap.range_eq_top]
  let J : Submodule R Y := Module.jacobson R Y
  let L : Submodule R Y := LinearMap.range f.hom.hom
  have hcompSurj :
      Function.Surjective (J.mkQ.comp f.hom.hom) := by
    exact
      (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective
        (f ≫ FGModuleCat.ofHom J.mkQ)).mp inferInstance
  have hmapTop : L.map J.mkQ = ⊤ := by
    rw [← LinearMap.range_comp, LinearMap.range_eq_top]
    exact hcompSurj
  have hsup : J ⊔ L = ⊤ :=
    (J.map_mkQ_eq_top L).mp hmapTop
  by_contra hL
  have hLJ : L ≤ J :=
    OpConjecture.FamilyFourControl.le_jacobson_of_ne_top_of_simple_top
      hTop hL
  have hJtop : J = ⊤ := by
    simpa only [sup_eq_left.mpr hLJ] using hsup
  exact (isSimpleModule_iff_isCoatom.mp hTop).ne_top hJtop

open OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank

/-- Every indecomposable with simple top is an epimorphic image of the
chosen indecomposable projective with that top. -/
theorem exists_epi_projectiveLabelOfSimple_of_simpleTop
    [Finite ι]
    (i : ι)
    (hTopI :
      IsSimpleModule R
        ((σ.obj i) ⧸ Module.jacobson R (σ.obj i)))
    (j : σ.SimpleIndex)
    (eTop :
      FGModuleCat.of R (σ.moduleTop i) ≅ σ.obj j.1) :
    ∃ f : σ.obj (projectiveLabelOfSimple σ j) ⟶ σ.obj i,
      Epi f := by
  let p : ProjectiveIndex σ :=
    (projectiveIndexEquivSimpleIndex σ).symm j
  have hpLabel : p.1 = projectiveLabelOfSimple σ j := rfl
  have hpTop : projectiveTopIndex σ p = j :=
    (projectiveIndexEquivSimpleIndex σ).apply_symm_apply j
  let qRad : σ.obj p.1 ⟶ projectiveTop σ p :=
    FGModuleCat.ofHom (Module.jacobson R (σ.obj p.1)).mkQ
  let qP : σ.obj p.1 ⟶ σ.obj j.1 :=
    qRad ≫ (projectiveTopIso σ p).hom ≫
      (eqToIso
        (congrArg (fun s : σ.SimpleIndex ↦ σ.obj s.1) hpTop)).hom
  haveI : Epi qRad :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective qRad).mpr
      (Module.jacobson R (σ.obj p.1)).mkQ_surjective
  haveI : Epi qP := by
    dsimp [qP]
    infer_instance
  let qM : σ.obj i ⟶ FGModuleCat.of R (σ.moduleTop i) :=
    FGModuleCat.ofHom (σ.moduleRadical i).mkQ
  haveI : Epi qM :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective qM).mpr
      (σ.moduleRadical i).mkQ_surjective
  let topMap : σ.obj i ⟶ σ.obj j.1 := qM ≫ eTop.hom
  haveI : Epi topMap := by
    dsimp [topMap]
    infer_instance
  letI : CategoryTheory.Projective (σ.obj p.1) := p.2
  let f : σ.obj p.1 ⟶ σ.obj i :=
    CategoryTheory.Projective.factorThru qP topMap
  have hfTop : f ≫ topMap = qP :=
    CategoryTheory.Projective.factorThru_comp qP topMap
  haveI : Epi (f ≫ topMap) := hfTop ▸ inferInstance
  haveI : Epi ((f ≫ qM) ≫ eTop.hom) := by
    simpa only [topMap, Category.assoc] using
      (inferInstance : Epi (f ≫ topMap))
  haveI : Epi (f ≫ qM) :=
    (CategoryTheory.epi_comp_iff_of_isIso (f ≫ qM) eTop.hom).mp
      (inferInstance : Epi ((f ≫ qM) ≫ eTop.hom))
  haveI :
      Epi
        (f ≫ FGModuleCat.ofHom
          (Module.jacobson R (σ.obj i)).mkQ) := by
    change Epi (f ≫ qM)
    infer_instance
  haveI : Epi f :=
    epi_of_comp_radicalQuotient_epi_of_simpleTop hTopI f
  refine ⟨eqToHom (congrArg σ.obj hpLabel).symm ≫ f, ?_⟩
  infer_instance

/-- Simple tops for all indecomposables reduce the all-module Nakayama
property to uniseriality of the indecomposable projectives. -/
theorem isNakayamaSkeleton_of_simpleTops_of_projectiveNakayama
    [Finite ι]
    (hTop : AllIndecomposableTopsSimple σ)
    (hProjective :
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton σ) :
    OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton σ := by
  intro i
  have hTopI := hTop i
  let Top : FGModuleCat.{u} R := FGModuleCat.of R (σ.moduleTop i)
  have hTopSimple : Simple Top :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      Top).mpr hTopI
  letI : IsSimpleModule R Top := hTopI
  have hTopIndec : OpConjecture.Foundation.IsIndecomposableModule R Top :=
    OpConjecture.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨jRaw, ⟨eTop⟩⟩ := σ.complete Top hTopIndec
  have hjSimple : Simple (σ.obj jRaw) :=
    (Simple.iff_of_iso eTop).mp hTopSimple
  let j : σ.SimpleIndex := ⟨jRaw, hjSimple⟩
  obtain ⟨f, hf⟩ :=
    exists_epi_projectiveLabelOfSimple_of_simpleTop
      σ i hTopI j eTop
  letI : Epi f := hf
  have hPUniserial :
      OpConjecture.IsUniserialModule R
        (σ.obj (projectiveLabelOfSimple σ j)) :=
    hProjective _ (projective_projectiveLabelOfSimple σ j)
  have hQuotUniserial :
      OpConjecture.IsUniserialModule R
        ((σ.obj (projectiveLabelOfSimple σ j)) ⧸
          LinearMap.ker f.hom.hom) :=
    OpConjecture.IsUniserialModule.quotient
      hPUniserial (LinearMap.ker f.hom.hom)
  have hSurj : Function.Surjective f.hom.hom :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective f).mp
      inferInstance
  exact
    isUniserialModule_congr
      (f.hom.hom.quotKerEquivOfSurjective hSurj)
      hQuotUniserial

section ExtGabrielForks

variable {K A : Type u}
  [Field K] [IsAlgClosed K]
  [Ring A] [Small.{u} A] [IsNoetherianRing A] [IsArtinianRing A]
  [Algebra K A]
  {κ : Type v} [Finite κ]
  (τ : OpConjecture.IndecomposableSkeleton.{u, v, u} A κ)

open OpConjecture.GabrielArrowBridge

/-- The exact finiteness needed for the multiplicity-bearing Ext--Gabriel
arrow type to reflect nonzero simple--simple `Ext¹` classes. -/
def FiniteExtOneSupport : Prop :=
  ∀ s t : τ.SimpleIndex, FiniteDimensional K (ExtOne τ s t)

omit [IsAlgClosed K] [IsArtinianRing A] [Finite κ] in
/-- Finite-dimensionality of the algebra supplies finite-dimensional
simple--simple degree-one extension spaces. -/
theorem finiteExtOneSupport_of_finiteDimensional
    [FiniteDimensional K A] :
    FiniteExtOneSupport (K := K) τ := by
  intro s t
  exact
    OpConjecture.NoParallelExtOne.moduleFinite_ext_one_of_finiteDimensional
      (K := K) (R := A)

/-- Two multiplicity-bearing arrows with a common target. -/
def HasIncomingExtGabrielFork : Prop :=
  ∃ a b : ExtGabrielArrowIndex (K := K) τ,
    a ≠ b ∧
      ExtGabrielArrowIndex.target τ a =
        ExtGabrielArrowIndex.target τ b

/-- Two multiplicity-bearing arrows with a common source. -/
def HasOutgoingExtGabrielFork : Prop :=
  ∃ a b : ExtGabrielArrowIndex (K := K) τ,
    a ≠ b ∧
      ExtGabrielArrowIndex.source τ a =
        ExtGabrielArrowIndex.source τ b

omit [IsAlgClosed K] [Finite κ] in
/-- The maintained length-two/Ext-arrow equivalence preserves sources, so
source injectivity descends to the length-two skeleton. -/
theorem lengthTwoSource_injective_of_extSource_injective
    (hNoParallel : NoParallelExtSupport (K := K) τ)
    (hSource :
      Function.Injective
        (ExtGabrielArrowIndex.source (K := K) τ)) :
    Function.Injective (LengthTwo.source τ) := by
  let e := LengthTwo.lengthTwoEquivExtGabrielArrow τ hNoParallel
  intro x y hxy
  apply e.injective
  apply hSource
  simpa [e, LengthTwo.lengthTwoEquivExtGabrielArrow,
    ExtGabrielArrowIndex.source,
    extGabrielArrowEquivSupport,
    LengthTwo.lengthTwoEquivGabrielArrow,
    LengthTwo.toGabrielArrow,
    GabrielArrowIndex.source] using hxy

omit [IsAlgClosed K] [Finite κ] in
/-- The maintained length-two/Ext-arrow equivalence also preserves targets. -/
theorem lengthTwoTarget_injective_of_extTarget_injective
    (hNoParallel : NoParallelExtSupport (K := K) τ)
    (hTarget :
      Function.Injective
        (ExtGabrielArrowIndex.target (K := K) τ)) :
    Function.Injective (LengthTwo.target τ) := by
  let e := LengthTwo.lengthTwoEquivExtGabrielArrow τ hNoParallel
  intro x y hxy
  apply e.injective
  apply hTarget
  simpa [e, LengthTwo.lengthTwoEquivExtGabrielArrow,
    ExtGabrielArrowIndex.target,
    extGabrielArrowEquivSupport,
    LengthTwo.lengthTwoEquivGabrielArrow,
    LengthTwo.toGabrielArrow,
    GabrielArrowIndex.target] using hxy

/-- The exact local fork-extraction statement needed from the
Ext--radical-layer theory.  A nonsimple top produces a fork at one of the
two endpoints; its direction need not be incoming.  Once the top is simple,
a decomposable nonzero radical produces an outgoing fork.

Multiplicity-bearing arrows make both alternatives include parallel arrows
as well as arrows with different other endpoints.  The explicit finite-Ext
field ensures that the `Fin (finrank ...)` arrow type detects every nonzero
simple--simple extension space. -/
structure ExtGabrielForkExtraction : Prop where
  finite_extOne : FiniteExtOneSupport (K := K) τ
  fork_of_nonsimple_top :
    ∀ i : κ,
      ¬ IsSimpleModule A
          ((τ.obj i) ⧸ Module.jacobson A (τ.obj i)) →
        HasIncomingExtGabrielFork (K := K) τ ∨
          HasOutgoingExtGabrielFork (K := K) τ
  outgoing_of_decomposable_radical :
    ∀ i : κ,
      IsSimpleModule A
          ((τ.obj i) ⧸ Module.jacobson A (τ.obj i)) →
      Module.jacobson A (τ.obj i) ≠ ⊥ →
      ¬ OpConjecture.Foundation.IsIndecomposableModule A
          (Module.jacobson A (τ.obj i)) →
        HasOutgoingExtGabrielFork (K := K) τ

omit [IsAlgClosed K] [IsArtinianRing A] [Finite κ] in
/-- Simultaneous incoming- and outgoing-degree one, together with the
nonsimple-top fork extraction, forces every chosen indecomposable to have
simple top. -/
theorem allIndecomposableTopsSimple_of_source_target_injective
    (hFork : ExtGabrielForkExtraction (K := K) τ)
    (hSource :
      Function.Injective
        (ExtGabrielArrowIndex.source (K := K) τ))
    (hTarget :
      Function.Injective
        (ExtGabrielArrowIndex.target (K := K) τ)) :
    AllIndecomposableTopsSimple τ := by
  intro i
  by_contra hTop
  rcases hFork.fork_of_nonsimple_top i hTop with
      ⟨a, b, hab, htarget⟩ | ⟨a, b, hab, hsource⟩
  · exact hab (hTarget htarget)
  · exact hab (hSource hsource)

omit [IsAlgClosed K] [IsArtinianRing A] [Finite κ] in
/-- Outgoing-degree one plus the outgoing-fork extraction forces every
nonzero radical to be indecomposable. -/
theorem allNonzeroRadicalsIndecomposable_of_source_injective
    (hFork : ExtGabrielForkExtraction (K := K) τ)
    (hTop : AllIndecomposableTopsSimple τ)
    (hSource :
      Function.Injective
        (ExtGabrielArrowIndex.source (K := K) τ)) :
    AllNonzeroRadicalsIndecomposable τ := by
  intro i hJ
  by_contra hIndec
  obtain ⟨a, b, hab, hsource⟩ :=
    hFork.outgoing_of_decomposable_radical
      i (hTop i) hJ hIndec
  exact hab (hSource hsource)

omit [IsAlgClosed K] [IsArtinianRing A] [Finite κ] in
/-- Once the two general radical-layer fork extractions are available, the
Ext-Gabriel in/out-degree-one Nakayama theorem follows by the compiled
finite-length induction. -/
theorem isNakayamaSkeleton_of_extGabrielForkExtraction
    (hFork : ExtGabrielForkExtraction (K := K) τ)
    (hSource :
      Function.Injective
        (ExtGabrielArrowIndex.source (K := K) τ))
    (hTarget :
      Function.Injective
        (ExtGabrielArrowIndex.target (K := K) τ)) :
    OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton τ := by
  have hTop : AllIndecomposableTopsSimple τ :=
    allIndecomposableTopsSimple_of_source_target_injective
      τ hFork hSource hTarget
  have hRadical : AllNonzeroRadicalsIndecomposable τ :=
    allNonzeroRadicalsIndecomposable_of_source_injective
      τ hFork hTop hSource
  exact
    isNakayamaSkeleton_of_simpleTops_of_indecRadicals
      τ hTop hRadical

omit [IsAlgClosed K] [IsArtinianRing A] [Finite κ] in
/-- The fork-extraction theorem supplies the exact classification interface
used by the loop-free two-vertex reduction.  The explicit no-parallel
hypothesis is not needed in this last adapter because injectivity of either
multiplicity-bearing endpoint map already rules out parallel arrows. -/
theorem extGabrielInOutDegreeOneNakayamaClassification_of_forkExtraction
    (hFork : ExtGabrielForkExtraction (K := K) τ) :
    OpConjecture.NoLoopNakayamaReduction.ExtGabrielInOutDegreeOneNakayamaClassification
      (K := K) τ := by
  intro _hNoParallel hSource hTarget
  exact
    isNakayamaSkeleton_of_extGabrielForkExtraction
      τ hFork hSource hTarget

end ExtGabrielForks

end OpConjecture.ExtDegreeNakayamaReduction
