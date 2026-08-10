import OpConjecture.RepresentationTheory.ConnectedSmallCoreAssembly
import OpConjecture.RepresentationTheory.ARNoTransitiveTriangles
import OpConjecture.RepresentationTheory.BottomThreeUnconditionalEndpoint
import OpConjecture.RepresentationTheory.ExtDualTransport
import OpConjecture.RepresentationTheory.FiniteDimensionalARNonvanishing
import OpConjecture.RepresentationTheory.FiniteDimensionalNoParallelExt
import OpConjecture.RepresentationTheory.FiniteDimensionalRecurrenceAssembly
import OpConjecture.RepresentationTheory.FiniteTypeARTranslation
import OpConjecture.RepresentationTheory.FamilyThreeClosure
import OpConjecture.RepresentationTheory.HereditaryTwoSimpleBoundary
import OpConjecture.RepresentationTheory.NakayamaProductFormula
import OpConjecture.RepresentationTheory.ProjectiveRadicalExt
import OpConjecture.RepresentationTheory.ProjectiveInjectiveBoundary
import OpConjecture.RepresentationTheory.SerialRingBridge
import OpConjecture.RepresentationTheory.TwoSimpleCoreThreeUnconditional
import Mathlib.CategoryTheory.Abelian.Injective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace OpConjecture.HereditaryThreeSimpleUnconditional

universe u v

open OpConjecture.BottomLevels.FiniteDimensionalRecurrence
open OpConjecture.ExtDegreeNakayamaReduction
open OpConjecture.GabrielArrowBridge

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- Simultaneous degree-one Ext source and target injectivity gives the full
profile equality on an algebra node. -/
theorem fullProfileEquality_of_extSourceTarget_injective
    (B : AlgebraNode K)
    (hSource : Function.Injective
      (ExtGabrielArrowIndex.source (K := K) B.skeleton))
    (hTarget : Function.Injective
      (ExtGabrielArrowIndex.target (K := K) B.skeleton)) :
    FullProfileEquality K B := by
  letI : IsArtinianRing B.Carrier :=
    IsArtinianRing.of_finite K B.Carrier
  letI : IsArtinianRing B.Carrierᵐᵒᵖ :=
    OpConjecture.isArtinianRing_op_of_finiteDimensional K B.Carrier
  let tau :=
    OpConjecture.rightIndecomposableSkeleton.{u, u, u} K B.Carrier
  let D :=
    OpConjecture.Contragredient.alignedBiduality
      K B.Carrier B.skeleton tau
  letI : Finite
      (OpConjecture.CanonicalIndecomposableIndex.{u, u}
        B.Carrierᵐᵒᵖ) :=
    D.forward.labelEquiv.finite_iff.mp inferInstance
  let hNoParallel : NoParallelExtSupport (K := K) B.skeleton :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport
      B.skeleton
  let hDualNoParallel : NoParallelExtSupport (K := K) tau :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport tau
  let hFinite : FiniteExtOneSupport (K := K) B.skeleton :=
    fun s t => (hNoParallel s t).1
  let hDualFinite : FiniteExtOneSupport (K := K) tau :=
    fun s t => (hDualNoParallel s t).1
  have hProjective :
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton
        B.skeleton :=
    OpConjecture.SerialRingBridge.projectiveNakayamaSkeleton_of_extSource_injective
      B.skeleton hFinite hSource
  have hDualSource : Function.Injective
      (ExtGabrielArrowIndex.source (K := K) tau) :=
    OpConjecture.ExtDualTransport.AlignedAntiEquivalence.dualExtSource_injective_of_extTarget_injective
      B.skeleton tau D.forward hNoParallel hDualNoParallel hTarget
  have hDualProjective :
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton tau :=
    OpConjecture.SerialRingBridge.projectiveNakayamaSkeleton_of_extSource_injective
      tau hDualFinite hDualSource
  have hInjective :
      OpConjecture.SerialRingBridge.IsInjectiveNakayamaSkeleton B.skeleton :=
    OpConjecture.SerialRingBridge.injectiveNakayamaSkeleton_of_dual_projectiveNakayama
      B.skeleton tau D.forward hDualProjective
  have hNakayama :
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton B.skeleton :=
    OpConjecture.SerialEndpointReduction.isNakayamaSkeleton_of_projective_and_injective_boundaries
      (K := K) B.skeleton hProjective hInjective
  have hProfile :=
    OpConjecture.NakayamaProductFormula.levelPolynomials_eq_fixedTopChainPolynomial_of_alignedBiduality
      B.skeleton tau D hNakayama
  exact hProfile.1.trans hProfile.2.symm

attribute [local instance]
  CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteCoproducts

namespace TwoTypeSemisimple

/-- Every simple submodule of `M` has one of the two indicated linear
isomorphism types.  This is the ring-generic form of the utility previously
specialized to opposite-algebra modules in the family-three files. -/
def HasSimpleConstituentsOfEitherType
    {R : Type u} [Ring R]
    (M S T : Type u)
    [AddCommGroup M] [Module R M]
    [AddCommGroup S] [Module R S]
    [AddCommGroup T] [Module R T] : Prop :=
  ∀ L : Submodule R M, IsSimpleModule R L →
    Nonempty (L ≃ₗ[R] S) ∨ Nonempty (L ≃ₗ[R] T)

theorem HasSimpleConstituentsOfEitherType.of_subsingleton
    {R M S T : Type u} [Ring R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup S] [Module R S]
    [AddCommGroup T] [Module R T]
    [Subsingleton M] :
    HasSimpleConstituentsOfEitherType (R := R) M S T := by
  intro L hL
  letI : IsSimpleModule R L := hL
  letI : Nontrivial L := IsSimpleModule.nontrivial R L
  obtain ⟨z, hz⟩ := exists_ne (0 : L)
  exact False.elim (hz (Subsingleton.elim z 0))

theorem HasSimpleConstituentsOfEitherType.of_simple_left
    {R M S T : Type u} [Ring R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup S] [Module R S]
    [AddCommGroup T] [Module R T]
    [IsSimpleModule R M]
    (e : M ≃ₗ[R] S) :
    HasSimpleConstituentsOfEitherType (R := R) M S T := by
  intro L hL
  letI : IsSimpleModule R L := hL
  exact Or.inl ⟨
    ((IsIsotypicOfType.of_isSimpleModule R M) L).some.trans e⟩

theorem HasSimpleConstituentsOfEitherType.of_simple_right
    {R M S T : Type u} [Ring R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup S] [Module R S]
    [AddCommGroup T] [Module R T]
    [IsSimpleModule R M]
    (e : M ≃ₗ[R] T) :
    HasSimpleConstituentsOfEitherType (R := R) M S T := by
  intro L hL
  letI : IsSimpleModule R L := hL
  exact Or.inr ⟨
    ((IsIsotypicOfType.of_isSimpleModule R M) L).some.trans e⟩

theorem hasSimpleConstituentsOfEitherType_pi
    {R : Type u} [Ring R]
    {J : Type} [Finite J]
    {M : J → Type u}
    [∀ t, AddCommGroup (M t)] [∀ t, Module R (M t)]
    {S T : Type u}
    [AddCommGroup S] [Module R S]
    [AddCommGroup T] [Module R T]
    (hcomponent : ∀ t,
      HasSimpleConstituentsOfEitherType (R := R) (M t) S T) :
    HasSimpleConstituentsOfEitherType (R := R) (∀ t, M t) S T := by
  intro L hL
  letI : IsSimpleModule R L := hL
  letI : Nontrivial L := IsSimpleModule.nontrivial R L
  obtain ⟨z, hz⟩ := exists_ne (0 : L)
  have hzval : z.1 ≠ 0 := by
    intro hzero
    apply hz
    apply Subtype.ext
    exact hzero
  have hcoordinate : ∃ t : J, z.1 t ≠ 0 := by
    by_contra h
    push Not at h
    apply hzval
    funext t
    exact h t
  obtain ⟨t, hzt⟩ := hcoordinate
  let f : L →ₗ[R] M t := (LinearMap.proj t).comp L.subtype
  have hf : f ≠ 0 := by
    intro hzero
    have hzmap : f z = 0 := by rw [hzero]; rfl
    exact hzt hzmap
  have hfinj : Function.Injective f := by
    rcases f.injective_or_eq_zero with hinj | hzero
    · exact hinj
    · exact (hf hzero).elim
  let e : L ≃ₗ[R] LinearMap.range f :=
    LinearEquiv.ofInjective f hfinj
  have hrangeSimple : IsSimpleModule R (LinearMap.range f) :=
    IsSimpleModule.congr e.symm
  rcases hcomponent t (LinearMap.range f) hrangeSimple with hS | hT
  · exact Or.inl ⟨e.trans hS.some⟩
  · exact Or.inr ⟨e.trans hT.some⟩

theorem moduleRadical_sumOver_hasSimpleConstituentsOfEitherType
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {ι : Type v}
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} R ι)
    (J : FintypeCat.{0}) (a : J → ι)
    {S T : Type u}
    [AddCommGroup S] [Module R S]
    [AddCommGroup T] [Module R T]
    (hcomponent : ∀ t : J,
      HasSimpleConstituentsOfEitherType (R := R)
        (Module.jacobson R (σ.obj (a t))) S T) :
    HasSimpleConstituentsOfEitherType (R := R)
      (Module.jacobson R (σ.sumOver J a)) S T := by
  letI : Fintype J := FintypeCat.fintype
  let e :
      σ.sumOver J a ≅ FGModuleCat.of R (∀ t : J, σ.obj (a t)) :=
    OpConjecture.IndecomposableSkeleton.biproductIsoPiFG _
  let sourceRadical : Submodule R (σ.sumOver J a) :=
    Module.jacobson R (σ.sumOver J a)
  let componentRadical (t : J) : Submodule R (σ.obj (a t)) :=
    Module.jacobson R (σ.obj (a t))
  let coordinate (t : J) :
      sourceRadical →ₗ[R] componentRadical t :=
    ((((LinearMap.proj t :
        (∀ s : J, σ.obj (a s)) →ₗ[R] σ.obj (a t))).comp
          e.hom.hom.hom).domRestrict sourceRadical).codRestrict
      (componentRadical t) (fun z ↦ by
        apply Module.map_jacobson_le
          ((LinearMap.proj t :
            (∀ s : J, σ.obj (a s)) →ₗ[R] σ.obj (a t)).comp
              e.hom.hom.hom)
        exact ⟨z.1, z.2, rfl⟩)
  let diagonal :
      sourceRadical →ₗ[R] (∀ t : J, componentRadical t) :=
    LinearMap.pi coordinate
  have hdiagonal : Function.Injective diagonal := by
    intro z z' hzz'
    apply Subtype.ext
    apply (FGModuleCat.isoToLinearEquiv e).injective
    funext t
    exact congrArg Subtype.val (congrFun hzz' t)
  intro L hL
  letI : IsSimpleModule R L := hL
  let f : L →ₗ[R] (∀ t : J, componentRadical t) :=
    diagonal.comp L.subtype
  have hf : Function.Injective f := hdiagonal.comp L.subtype_injective
  let eL : L ≃ₗ[R] LinearMap.range f :=
    LinearEquiv.ofInjective f hf
  have hrangeSimple : IsSimpleModule R (LinearMap.range f) :=
    IsSimpleModule.congr eL.symm
  have hproduct : HasSimpleConstituentsOfEitherType (R := R)
      (∀ t : J, componentRadical t) S T :=
    hasSimpleConstituentsOfEitherType_pi
      (R := R) (J := J) (M := fun t ↦ componentRadical t)
      (S := S) (T := T) (fun t ↦ hcomponent t)
  rcases hproduct (LinearMap.range f) hrangeSimple with hS | hT
  · exact Or.inl ⟨eL.trans hS.some⟩
  · exact Or.inr ⟨eL.trans hT.some⟩

theorem HasSimpleConstituentsOfEitherType.of_surjective_of_semisimple
    {R M N S T : Type u} [Ring R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup S] [Module R S]
    [AddCommGroup T] [Module R T]
    [IsSemisimpleModule R M]
    (hM : HasSimpleConstituentsOfEitherType (R := R) M S T)
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    HasSimpleConstituentsOfEitherType (R := R) N S T := by
  intro L hL
  letI : IsSimpleModule R L := hL
  obtain ⟨l, hl⟩ :=
    IsSemisimpleModule.lifting_property f hf L.subtype
  have hlinj : Function.Injective l := by
    intro a b hab
    apply L.subtype_injective
    calc
      L.subtype a = f (l a) := by
        have h := LinearMap.congr_fun hl a
        simpa using h.symm
      _ = f (l b) := by rw [hab]
      _ = L.subtype b := by
        have h := LinearMap.congr_fun hl b
        simpa using h
  let e : L ≃ₗ[R] LinearMap.range l :=
    LinearEquiv.ofInjective l hlinj
  have hrangeSimple : IsSimpleModule R (LinearMap.range l) :=
    IsSimpleModule.congr e.symm
  rcases hM (LinearMap.range l) hrangeSimple with hS | hT
  · exact Or.inl ⟨e.trans hS.some⟩
  · exact Or.inr ⟨e.trans hT.some⟩

/-- Split a dependent function on a sum type into its two restrictions. -/
def piSumLinearEquivProd
    {R : Type u} [Ring R]
    {α β : Type} {M : α ⊕ β → Type u}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    ((i : α ⊕ β) → M i) ≃ₗ[R]
      ((a : α) → M (.inl a)) × ((b : β) → M (.inr b)) where
  toFun f := (fun a ↦ f (.inl a), fun b ↦ f (.inr b))
  invFun f i := match i with
    | .inl a => f.1 a
    | .inr b => f.2 b
  left_inv f := by funext i; cases i <;> rfl
  right_inv f := by
    rcases f with ⟨f, g⟩
    apply Prod.ext <;> funext i <;> rfl
  map_add' f g := by apply Prod.ext <;> funext i <;> rfl
  map_smul' r f := by apply Prod.ext <;> funext i <;> rfl

/-- A finite semisimple module whose simple constituents have one of two
types is a product of finite powers of those two types. -/
theorem exists_twoTypeDecomposition
    {R M S T : Type u} [Ring R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup S] [Module R S]
    [AddCommGroup T] [Module R T]
    [IsSemisimpleModule R M] [Module.Finite R M]
    [IsSimpleModule R S] [IsSimpleModule R T]
    (h : HasSimpleConstituentsOfEitherType (R := R) M S T) :
    ∃ (J L : Type) (_ : Fintype J) (_ : Fintype L),
      Nonempty (M ≃ₗ[R] (J → S) × (L → T)) := by
  classical
  obtain ⟨n, U, e, hU⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R M
  let P : Fin n → Prop := fun i ↦ Nonempty (U i ≃ₗ[R] S)
  let J := {i : Fin n // P i}
  let L := {i : Fin n // ¬ P i}
  letI : Fintype J := Fintype.ofFinite J
  letI : Fintype L := Fintype.ofFinite L
  let eFun : M ≃ₗ[R] (i : Fin n) → U i :=
    e.trans (DFinsupp.linearEquivFunOnFintype
      (R := R) (M := fun i ↦ U i))
  let esum : J ⊕ L ≃ Fin n := Equiv.sumCompl P
  let eReindex :
      ((i : Fin n) → U i) ≃ₗ[R] ((q : J ⊕ L) → U (esum q)) :=
    (LinearEquiv.piCongrLeft R (fun i : Fin n ↦ U i) esum).symm
  let eSplit :
      ((q : J ⊕ L) → U (esum q)) ≃ₗ[R]
        (((j : J) → U (esum (.inl j))) ×
          ((l : L) → U (esum (.inr l)))) :=
    piSumLinearEquivProd
  let eLeft : ((j : J) → U (esum (.inl j))) ≃ₗ[R] (J → S) :=
    LinearEquiv.piCongrRight (fun j ↦ by
      change U j.1 ≃ₗ[R] S
      exact j.2.some)
  let eRight : ((l : L) → U (esum (.inr l))) ≃ₗ[R] (L → T) :=
    LinearEquiv.piCongrRight (fun l ↦ by
      have hl : ¬ P l.1 := l.2
      have hT : Nonempty (U l.1 ≃ₗ[R] T) :=
        (h (U l.1) (hU l.1)).resolve_left hl
      change U l.1 ≃ₗ[R] T
      exact hT.some)
  exact ⟨J, L, inferInstance, inferInstance,
    ⟨eFun.trans eReindex |>.trans eSplit |>.trans
      (eLeft.prodCongr eRight)⟩⟩

end TwoTypeSemisimple

/-- Ring-generic two-target Ext-matrix endpoint.  The maintained family-three
version was stated only for opposite-algebra modules; this formulation uses
the generic Gabriel no-parallel support and therefore applies equally to the
left-module hereditary core needed here. -/
theorem moduleTop_isSimple_of_twoTargetDecomposition
    {A : Type u} [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A] [IsNoetherianRing A]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hnoParallel : NoParallelExtSupport (K := K) σ)
    {j s t r : ι}
    (hs : Simple (σ.obj s)) (ht : Simple (σ.obj t))
    (hr : Simple (σ.obj r))
    {J L I : Type} [Fintype J] [Fintype L] [Fintype I]
    (eRadical :
      ((J → σ.obj s) × (L → σ.obj t)) ≃ₗ[A] σ.moduleRadical j)
    (eTop : (I → σ.obj r) ≃ₗ[A] σ.moduleTop j)
    (hsourceLength :
      (Module.finrank K (I → K) : ℕ∞) =
        Module.length A (σ.moduleTop j)) :
    IsSimpleModule A (σ.moduleTop j) := by
  classical
  let leftIso :
      ((⨁ fun _ : J ↦ (σ.obj s).obj) : ModuleCat.{u} A) ≅
        ModuleCat.of A (J → σ.obj s) :=
    ModuleCat.biproductIsoPi (fun _ : J ↦ (σ.obj s).obj)
  let rightIso :
      ((⨁ fun _ : L ↦ (σ.obj t).obj) : ModuleCat.{u} A) ≅
        ModuleCat.of A (L → σ.obj t) :=
    ModuleCat.biproductIsoPi (fun _ : L ↦ (σ.obj t).obj)
  let radicalIso :
      (((⨁ fun _ : J ↦ (σ.obj s).obj) ⊞
          (⨁ fun _ : L ↦ (σ.obj t).obj)) : ModuleCat.{u} A) ≅
        ModuleCat.of A (σ.moduleRadical j) :=
    biprod.mapIso leftIso rightIso ≪≫
      ModuleCat.biprodIsoProd
        (ModuleCat.of A (J → σ.obj s))
        (ModuleCat.of A (L → σ.obj t)) ≪≫
      eRadical.toModuleIso
  let topIso :
      ((⨁ fun _ : I ↦ (σ.obj r).obj) : ModuleCat.{u} A) ≅
        ModuleCat.of A (σ.moduleTop j) :=
    ModuleCat.biproductIsoPi
        (fun _ : I ↦ (σ.obj r).obj) ≪≫
      eTop.toModuleIso
  let eRadical' :
      ((((⨁ fun _ : J ↦ (σ.obj s).obj) ⊞
          (⨁ fun _ : L ↦ (σ.obj t).obj)) : ModuleCat.{u} A)) ≃ₗ[A]
        σ.moduleRadical j :=
    radicalIso.toLinearEquiv
  let eMiddle : (σ.obj j) ≃ₗ[A] (σ.obj j) :=
    LinearEquiv.refl A (σ.obj j)
  let eTop' :
      (((⨁ fun _ : I ↦ (σ.obj r).obj) : ModuleCat.{u} A)) ≃ₗ[A]
        σ.moduleTop j :=
    topIso.toLinearEquiv
  let radicalInclusion : σ.moduleRadical j →ₗ[A] σ.obj j :=
    (σ.moduleRadical j).subtype
  let topProjection : σ.obj j →ₗ[A] σ.moduleTop j :=
    (σ.moduleRadical j).mkQ
  have hexact : Function.Exact radicalInclusion topProjection :=
    LinearMap.exact_subtype_mkQ (σ.moduleRadical j)
  let SC : ShortComplex (ModuleCat.{u} A) :=
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
  letI : IsNoetherian A (σ.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength j)).1
  letI : IsArtinian A (σ.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength j)).2
  have hExtLeft := hnoParallel ⟨r, hr⟩ ⟨s, hs⟩
  have hExtRight := hnoParallel ⟨r, hr⟩ ⟨t, ht⟩
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
  letI : IsSimpleModule A (σ.obj s) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp hs
  letI : IsSimpleModule A (σ.obj t) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp ht
  letI : IsSimpleModule A (σ.obj r) :=
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
  letI : Nontrivial (σ.obj j) := (σ.indecomposable j).nontrivial
  change
    (Module.finrank K (I → K) : ℕ∞) =
      Module.length A
        ((σ.obj j) ⧸ Module.jacobson A (σ.obj j))
    at hsourceLength
  exact
    OpConjecture.FamilyThreeSpecialization.moduleTop_isSimple_of_twoTargetModel
      (K := K) (R := A) (M := σ.obj j)
      (OpConjecture.YonedaExtReflection.firstTargetScalarizedExtLinearMap
        (σ.obj r).obj (σ.obj s).obj (σ.obj t).obj ell hSC'.extClass)
      (OpConjecture.YonedaExtReflection.secondTargetScalarizedExtLinearMap
        (σ.obj r).obj (σ.obj s).obj (σ.obj t).obj ell' hSC'.extClass)
      hfork (by simpa using hsourceLength)

omit [IsAlgClosed K] in
/-- Ring-generic multiplicity bound dual to the preceding top-simplicity
endpoint.  A simple top and a two-type radical decomposition force at most
one copy of either radical type. -/
theorem radicalMultiplicityBounds_of_simpleTop_twoTypeDecomposition
    {A : Type u} [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A] [IsNoetherianRing A]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hnoParallel : NoParallelExtSupport (K := K) σ)
    {j s t r : ι}
    (hs : Simple (σ.obj s)) (ht : Simple (σ.obj t))
    (hr : Simple (σ.obj r))
    {J L : Type} [Fintype J] [Fintype L]
    (eRadical :
      ((J → σ.obj s) × (L → σ.obj t)) ≃ₗ[A] σ.moduleRadical j)
    (eTop : σ.obj r ≃ₗ[A] σ.moduleTop j) :
    Fintype.card J ≤ 1 ∧ Fintype.card L ≤ 1 := by
  classical
  let leftIso :
      ((⨁ fun _ : J ↦ (σ.obj s).obj) : ModuleCat.{u} A) ≅
        ModuleCat.of A (J → σ.obj s) :=
    ModuleCat.biproductIsoPi (fun _ : J ↦ (σ.obj s).obj)
  let rightIso :
      ((⨁ fun _ : L ↦ (σ.obj t).obj) : ModuleCat.{u} A) ≅
        ModuleCat.of A (L → σ.obj t) :=
    ModuleCat.biproductIsoPi (fun _ : L ↦ (σ.obj t).obj)
  let radicalIso :
      (((⨁ fun _ : J ↦ (σ.obj s).obj) ⊞
          (⨁ fun _ : L ↦ (σ.obj t).obj)) : ModuleCat.{u} A) ≅
        ModuleCat.of A (σ.moduleRadical j) :=
    biprod.mapIso leftIso rightIso ≪≫
      ModuleCat.biprodIsoProd
        (ModuleCat.of A (J → σ.obj s))
        (ModuleCat.of A (L → σ.obj t)) ≪≫
      eRadical.toModuleIso
  let topIso :
      ((⨁ fun _ : Unit ↦ (σ.obj r).obj) : ModuleCat.{u} A) ≅
        ModuleCat.of A (σ.moduleTop j) :=
    ModuleCat.biproductIsoPi
        (fun _ : Unit ↦ (σ.obj r).obj) ≪≫
      (LinearEquiv.funUnique Unit A (σ.obj r)).toModuleIso ≪≫
      eTop.toModuleIso
  let eRadical' :
      ((((⨁ fun _ : J ↦ (σ.obj s).obj) ⊞
          (⨁ fun _ : L ↦ (σ.obj t).obj)) : ModuleCat.{u} A)) ≃ₗ[A]
        σ.moduleRadical j :=
    radicalIso.toLinearEquiv
  let eMiddle : (σ.obj j) ≃ₗ[A] (σ.obj j) :=
    LinearEquiv.refl A (σ.obj j)
  let eTop' :
      (((⨁ fun _ : Unit ↦ (σ.obj r).obj) : ModuleCat.{u} A)) ≃ₗ[A]
        σ.moduleTop j :=
    topIso.toLinearEquiv
  let radicalInclusion : σ.moduleRadical j →ₗ[A] σ.obj j :=
    (σ.moduleRadical j).subtype
  let topProjection : σ.obj j →ₗ[A] σ.moduleTop j :=
    (σ.moduleRadical j).mkQ
  have hexact : Function.Exact radicalInclusion topProjection :=
    LinearMap.exact_subtype_mkQ (σ.moduleRadical j)
  let SC : ShortComplex (ModuleCat.{u} A) :=
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
  letI : IsNoetherian A (σ.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength j)).1
  letI : IsArtinian A (σ.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength j)).2
  have hExtLeft := hnoParallel ⟨r, hr⟩ ⟨s, hs⟩
  have hExtRight := hnoParallel ⟨r, hr⟩ ⟨t, ht⟩
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
  letI : IsSimpleModule A (σ.obj s) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp hs
  letI : IsSimpleModule A (σ.obj t) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp ht
  letI : IsSimpleModule A (σ.obj r) :=
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
  have hbounds :=
    OpConjecture.YonedaExtReflection.shortExact_twoTarget_target_finrank_le_one
      (σ.obj r).obj (σ.obj s).obj (σ.obj t).obj (σ.obj j).obj
      hrNonzero hsNonzero htNonzero
      SC.f SC.g SC.zero hSC' (σ.indecomposable j)
      ell hell ell' hell' (by simp)
  simpa using hbounds

/-- The sum map from two disjoint submodules is injective. -/
private theorem submoduleSubtype_coprod_injective_of_disjoint
    {A M : Type u} [Ring A] [AddCommGroup M] [Module A M]
    {P Q : Submodule A M} (hDisjoint : Disjoint P Q) :
    Function.Injective (P.subtype.coprod Q.subtype) := by
  rintro ⟨xLeft, xRight⟩ ⟨yLeft, yRight⟩ hxy
  have hxy' :
      (xLeft : M) + (xRight : M) =
        (yLeft : M) + (yRight : M) := by
    simpa only [LinearMap.coprod_apply, Submodule.coe_subtype] using hxy
  have hcommon :
      (xLeft : M) - (yLeft : M) =
        (yRight : M) - (xRight : M) := by
    calc
      (xLeft : M) - (yLeft : M) =
          ((xLeft : M) + (xRight : M)) -
            ((yLeft : M) + (xRight : M)) := by abel
      _ = ((yLeft : M) + (yRight : M)) -
            ((yLeft : M) + (xRight : M)) := by rw [hxy']
      _ = (yRight : M) - (xRight : M) := by abel
  have hcommonMem :
      (xLeft : M) - (yLeft : M) ∈ P ⊓ Q := by
    constructor
    · exact P.sub_mem xLeft.2 yLeft.2
    · rw [hcommon]
      exact Q.sub_mem yRight.2 xRight.2
  have hcommonBot :
      (xLeft : M) - (yLeft : M) ∈ (⊥ : Submodule A M) := by
    rw [← hDisjoint.eq_bot]
    exact hcommonMem
  have hleftEq : xLeft = yLeft := by
    apply Subtype.ext
    exact sub_eq_zero.mp (by simpa using hcommonBot)
  have hrightEq : xRight = yRight := by
    apply Subtype.ext
    have hxy'' :
        (yLeft : M) + (xRight : M) =
          (yLeft : M) + (yRight : M) := by
      simpa only [hleftEq] using hxy'
    exact add_left_cancel hxy''
  exact Prod.ext hleftEq hrightEq

/-- A component of a finite biproduct is projective when the whole
biproduct is projective. -/
private theorem projective_biproduct_component
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {J : Type} [Fintype J]
    (X : J → FGModuleCat.{u} R)
    [CategoryTheory.Projective (⨁ X)] (j : J) :
    CategoryTheory.Projective (X j) where
  factors f e _ := by
    obtain ⟨l, hl⟩ :=
      CategoryTheory.Projective.factors
        (biproduct.π X j ≫ f) e
    refine ⟨biproduct.ι X j ≫ l, ?_⟩
    calc
      (biproduct.ι X j ≫ l) ≫ e =
          biproduct.ι X j ≫ (l ≫ e) := Category.assoc _ _ _
      _ = biproduct.ι X j ≫ (biproduct.π X j ≫ f) := by rw [hl]
      _ = f := by simp

/-- In a finite left-hereditary algebra, an Ext-Gabriel arrow strictly
decreases the composition length of the corresponding indecomposable
projective covers. -/
theorem projectiveCoverLength_lt_of_extArrow
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (a : ExtGabrielArrowIndex (K := K) σ) :
    σ.compositionLength
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
          σ (ExtGabrielArrowIndex.target σ a)) <
      σ.compositionLength
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
          σ (ExtGabrielArrowIndex.source σ a)) := by
  classical
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  rcases a with ⟨s, t, k⟩
  let hNoParallel : NoParallelExtSupport (K := K) σ :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ
  letI : FiniteDimensional K (ExtOne σ s t) :=
    (hNoParallel s t).1
  have hExtPos : 0 < Module.finrank K (ExtOne σ s t) :=
    lt_of_le_of_lt (Nat.zero_le k.1) k.2
  letI : Nontrivial (ExtOne σ s t) :=
    Module.nontrivial_of_finrank_pos hExtPos
  obtain ⟨η, hη⟩ := exists_ne (0 : ExtOne σ s t)
  let p :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex σ :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).symm s
  have hpTop :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIndex
          σ p = s :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).apply_symm_apply s
  let eTopFG :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTop σ p ≅
        σ.obj s.1 :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIso σ p ≪≫
      eqToIso (congrArg (fun z : σ.SimpleIndex => σ.obj z.1) hpTop)
  let eTop := FGModuleCat.isoToLinearEquiv eTopFG
  letI : Module.Projective A (σ.obj p.1) :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.moduleProjective_of_fgProjective
      (σ.obj p.1) p.2
  letI : IsSimpleModule A (σ.obj t.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (σ.obj t.1)).mp t.2
  letI : IsSemisimpleModule A (σ.obj t.1) := inferInstance
  let E :=
    OpConjecture.ProjectiveRadicalExt.radicalHomLinearEquivExtOne
      (K := K) (R := A) (P := σ.obj p.1)
      (S := σ.obj s.1) (T := σ.obj t.1) eTop
  let f :
      ModuleCat.of A (Module.jacobson A (σ.obj p.1)) ⟶
        ModuleCat.of A (σ.obj t.1) := E.symm η
  have hf : f ≠ 0 := by
    intro hf0
    apply hη
    apply E.symm.injective
    simpa [f] using hf0
  letI : Simple (ModuleCat.of A (σ.obj t.1)) :=
    (simple_iff_isSimpleModule' (ModuleCat.of A (σ.obj t.1))).mpr
      inferInstance
  letI : Epi f := CategoryTheory.epi_of_nonzero_to_simple hf
  let J : Submodule A (σ.obj p.1) := Module.jacobson A (σ.obj p.1)
  have hJModuleProjective : Module.Projective A J :=
    hHereditary (σ.obj p.1) p.2 J
  have hJProjective : CategoryTheory.Projective (FGModuleCat.of A J) :=
    OpConjecture.RingelStable.fgProjective_of_moduleProjective
      (FGModuleCat.of A J) hJModuleProjective
  letI : CategoryTheory.Projective (FGModuleCat.of A J) := hJProjective
  obtain ⟨n, labels, ⟨e⟩⟩ := σ.decomposes (FGModuleCat.of A J)
  have hSumProjective :
      CategoryTheory.Projective (⨁ fun i : Fin n => σ.obj (labels i)) :=
    CategoryTheory.Projective.of_iso e inferInstance
  letI : CategoryTheory.Projective
      (⨁ fun i : Fin n => σ.obj (labels i)) := hSumProjective
  let fFG : FGModuleCat.of A J ⟶ σ.obj t.1 :=
    FGModuleCat.ofHom f.hom
  have hfFGSurj : Function.Surjective fFG.hom.hom := by
    exact (ModuleCat.epi_iff_surjective f).mp inferInstance
  letI : Epi fFG :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective fFG).mpr
      hfFGSurj
  let fsum :
      (⨁ fun i : Fin n => σ.obj (labels i)) ⟶ σ.obj t.1 :=
    e.inv ≫ fFG
  letI : Epi fsum := by
    dsimp [fsum]
    infer_instance
  obtain ⟨i, hi⟩ :=
    σ.exists_epi_biproduct_component_of_simple_top
      (FintypeCat.of (Fin n)) labels
      (σ.moduleTop_isSimple_of_simple t.2) fsum
  let componentMap : σ.obj (labels i) ⟶ σ.obj t.1 :=
    biproduct.ι (fun j : Fin n => σ.obj (labels j)) i ≫ fsum
  letI : Epi componentMap := hi
  have hComponentProjective : CategoryTheory.Projective (σ.obj (labels i)) :=
    projective_biproduct_component
      (fun j : Fin n => σ.obj (labels j)) i
  have hComponentIso : Nonempty
      (σ.obj (labels i) ≅
        σ.obj
          (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
            σ t)) :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projective_iso_of_indec_of_epi_to_simple
      σ (σ.obj (labels i)) hComponentProjective
        (σ.indecomposable (labels i)) t componentMap
  have hLabel : labels i =
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
        σ t :=
    σ.eq_of_iso hComponentIso
  let jSubtype : FGModuleCat.of A J ⟶ σ.obj p.1 :=
    FGModuleCat.ofHom J.subtype
  have hjSubtypeMono : Mono jSubtype :=
    (OpConjecture.IndecomposableSkeleton.fg_mono_iff_injective
      jSubtype).mpr J.subtype_injective
  letI : Mono jSubtype := hjSubtypeMono
  let inclusion : σ.obj (labels i) ⟶ σ.obj p.1 :=
    biproduct.ι (fun j : Fin n => σ.obj (labels j)) i ≫
      e.inv ≫ jSubtype
  have hinclusionMono : Mono inclusion := by
    dsimp [inclusion]
    infer_instance
  letI : Mono inclusion := hinclusionMono
  have hle : σ.compositionLength (labels i) ≤
      σ.compositionLength p.1 :=
    σ.compositionLength_le_of_mono inclusion
  have hne : σ.compositionLength (labels i) ≠
      σ.compositionLength p.1 := by
    intro heq
    have hIso : IsIso inclusion :=
      σ.isIso_of_mono_of_compositionLength_eq inclusion heq
    letI : IsIso inclusion := hIso
    have hIncSurj : Function.Surjective inclusion.hom.hom :=
      (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective
        inclusion).mp inferInstance
    have hSurj : Function.Surjective J.subtype := by
      intro x
      obtain ⟨y, hy⟩ := hIncSurj x
      let z : J :=
        e.inv.hom.hom
          ((biproduct.ι (fun j : Fin n => σ.obj (labels j)) i).hom.hom y)
      refine ⟨z, ?_⟩
      change (FGModuleCat.ofHom J.subtype).hom.hom z = x
      simpa [inclusion, jSubtype, z] using hy
    have hJtop : J = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨y, hy⟩ := hSurj x
      exact hy ▸ y.2
    letI : Nontrivial (σ.obj p.1) := (σ.indecomposable p.1).nontrivial
    exact (Module.jacobson_lt_top A (σ.obj p.1)).ne hJtop
  have hlt : σ.compositionLength (labels i) <
      σ.compositionLength p.1 := lt_of_le_of_ne hle hne
  change σ.compositionLength
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
        σ t) <
    σ.compositionLength
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
        σ s)
  simpa [hLabel, p,
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple]
    using hlt

/-- An Ext-Gabriel arrow between simples induces the corresponding
irreducible arrow between their indecomposable projective covers.  Left
heredity is used exactly to make the source projective's radical projective. -/
theorem hasIrreducibleMorphism_projectiveCovers_of_extArrow
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (a : ExtGabrielArrowIndex (K := K) σ) :
    HasIrreducibleMorphism
      (σ.obj
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
          σ (ExtGabrielArrowIndex.target σ a)))
      (σ.obj
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
          σ (ExtGabrielArrowIndex.source σ a))) := by
  classical
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  rcases a with ⟨s, t, k⟩
  change HasIrreducibleMorphism
    (σ.obj
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
        σ t))
    (σ.obj
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
        σ s))
  let hNoParallel : NoParallelExtSupport (K := K) σ :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ
  letI : FiniteDimensional K (ExtOne σ s t) :=
    (hNoParallel s t).1
  have hExtPos : 0 < Module.finrank K (ExtOne σ s t) :=
    lt_of_le_of_lt (Nat.zero_le k.1) k.2
  letI : Nontrivial (ExtOne σ s t) :=
    Module.nontrivial_of_finrank_pos hExtPos
  obtain ⟨η, hη⟩ := exists_ne (0 : ExtOne σ s t)
  let p :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex σ :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).symm s
  have hpTop :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIndex
          σ p = s :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).apply_symm_apply s
  let eTopFG :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTop σ p ≅
        σ.obj s.1 :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIso σ p ≪≫
      eqToIso (congrArg (fun z : σ.SimpleIndex => σ.obj z.1) hpTop)
  let eTop := FGModuleCat.isoToLinearEquiv eTopFG
  letI : Module.Projective A (σ.obj p.1) :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.moduleProjective_of_fgProjective
      (σ.obj p.1) p.2
  letI : IsSimpleModule A (σ.obj t.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (σ.obj t.1)).mp t.2
  letI : IsSemisimpleModule A (σ.obj t.1) := inferInstance
  let E :=
    OpConjecture.ProjectiveRadicalExt.radicalHomLinearEquivExtOne
      (K := K) (R := A) (P := σ.obj p.1)
      (S := σ.obj s.1) (T := σ.obj t.1) eTop
  let f :
      ModuleCat.of A (Module.jacobson A (σ.obj p.1)) ⟶
        ModuleCat.of A (σ.obj t.1) := E.symm η
  have hf : f ≠ 0 := by
    intro hf0
    apply hη
    apply E.symm.injective
    simpa [f] using hf0
  letI : Simple (ModuleCat.of A (σ.obj t.1)) :=
    (simple_iff_isSimpleModule' (ModuleCat.of A (σ.obj t.1))).mpr
      inferInstance
  letI : Epi f := CategoryTheory.epi_of_nonzero_to_simple hf
  let J : Submodule A (σ.obj p.1) := Module.jacobson A (σ.obj p.1)
  have hJModuleProjective : Module.Projective A J :=
    hHereditary (σ.obj p.1) p.2 J
  have hJProjective : CategoryTheory.Projective (FGModuleCat.of A J) :=
    OpConjecture.RingelStable.fgProjective_of_moduleProjective
      (FGModuleCat.of A J) hJModuleProjective
  letI : CategoryTheory.Projective (FGModuleCat.of A J) := hJProjective
  obtain ⟨n, labels, ⟨e⟩⟩ := σ.decomposes (FGModuleCat.of A J)
  have hSumProjective :
      CategoryTheory.Projective (⨁ fun i : Fin n => σ.obj (labels i)) :=
    CategoryTheory.Projective.of_iso e inferInstance
  letI : CategoryTheory.Projective
      (⨁ fun i : Fin n => σ.obj (labels i)) := hSumProjective
  let fFG : FGModuleCat.of A J ⟶ σ.obj t.1 :=
    FGModuleCat.ofHom f.hom
  have hfFGSurj : Function.Surjective fFG.hom.hom :=
    (ModuleCat.epi_iff_surjective f).mp inferInstance
  letI : Epi fFG :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective fFG).mpr
      hfFGSurj
  let fsum :
      (⨁ fun i : Fin n => σ.obj (labels i)) ⟶ σ.obj t.1 :=
    e.inv ≫ fFG
  letI : Epi fsum := by
    dsimp [fsum]
    infer_instance
  obtain ⟨i, hi⟩ :=
    σ.exists_epi_biproduct_component_of_simple_top
      (FintypeCat.of (Fin n)) labels
      (σ.moduleTop_isSimple_of_simple t.2) fsum
  let componentMap : σ.obj (labels i) ⟶ σ.obj t.1 :=
    biproduct.ι (fun j : Fin n => σ.obj (labels j)) i ≫ fsum
  letI : Epi componentMap := hi
  have hComponentProjective : CategoryTheory.Projective (σ.obj (labels i)) :=
    projective_biproduct_component
      (fun j : Fin n => σ.obj (labels j)) i
  have hComponentIso : Nonempty
      (σ.obj (labels i) ≅
        σ.obj
          (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
            σ t)) :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projective_iso_of_indec_of_epi_to_simple
      σ (σ.obj (labels i)) hComponentProjective
        (σ.indecomposable (labels i)) t componentMap
  have hLabel : labels i =
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
        σ t :=
    σ.eq_of_iso hComponentIso
  let r : Retract (σ.obj (labels i)) (FGModuleCat.of A J) :=
    { i := biproduct.ι (fun j : Fin n => σ.obj (labels j)) i ≫ e.inv
      r := e.hom ≫ biproduct.π (fun j : Fin n => σ.obj (labels j)) i
      retract := by simp }
  rw [hLabel] at r
  apply
    (σ.indecomposableRetract_projectiveBoundaryRadical_iff_irreducible
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
        σ s)
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projective_projectiveLabelOfSimple
        σ s)
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
        σ t)).mp
  change Nonempty (Retract
    (σ.obj
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
        σ t))
    (FGModuleCat.of A J))
  exact ⟨r⟩

/-- A transitive triangle in the Ext-Gabriel support would become a
transitive triangle of irreducible maps between indecomposable projective
covers, which cannot occur in the finite AR quiver. -/
theorem no_extTransitiveTriangle
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (a b c : ExtGabrielArrowIndex (K := K) σ)
    (hab : ExtGabrielArrowIndex.target σ a =
      ExtGabrielArrowIndex.source σ b)
    (hacSource : ExtGabrielArrowIndex.source σ a =
      ExtGabrielArrowIndex.source σ c)
    (hbcTarget : ExtGabrielArrowIndex.target σ b =
      ExtGabrielArrowIndex.target σ c) : False := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let ha := hasIrreducibleMorphism_projectiveCovers_of_extArrow
    K σ hHereditary a
  let hb := hasIrreducibleMorphism_projectiveCovers_of_extArrow
    K σ hHereditary b
  let hc := hasIrreducibleMorphism_projectiveCovers_of_extArrow
    K σ hHereditary c
  have hb' : HasIrreducibleMorphism
      (σ.obj
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
          σ (ExtGabrielArrowIndex.target σ b)))
      (σ.obj
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
          σ (ExtGabrielArrowIndex.target σ a))) := by
    simpa [hab] using hb
  have hc' : HasIrreducibleMorphism
      (σ.obj
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
          σ (ExtGabrielArrowIndex.target σ b)))
      (σ.obj
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
          σ (ExtGabrielArrowIndex.source σ a))) := by
    simpa [hacSource, hbcTarget] using hc
  exact
    (OpConjecture.IndecomposableSkeleton.FiniteARTranslationData.no_irreducible_transitiveTriangle
      (K := K) σ (σ.finiteDimensionalARTranslationData K A) hb' ha) hc'

section ThreeVertexSupport

variable {V Arrow : Type u} [Finite V]
  (source target : Arrow → V)

/-- On three vertices, a strict height function, endpoint-pair uniqueness,
and exclusion of transitive triangles force a common-source fork to exhaust
the whole arrow support. -/
theorem arrow_eq_left_or_right_of_threeVertices_of_source_fork
    (hcard : Nat.card V = 3)
    (hPair : Function.Injective (fun a : Arrow => (source a, target a)))
    (height : V → ℕ)
    (hdecrease : ∀ a : Arrow, height (target a) < height (source a))
    (hNoTriangle : ∀ a b c : Arrow,
      target a = source b → source a = source c →
        target b = target c → False)
    (left right : Arrow) (hne : left ≠ right)
    (hsource : source left = source right)
    (a : Arrow) :
    a = left ∨ a = right := by
  classical
  let s := source left
  let t := target left
  let u := target right
  have hst : s ≠ t := by
    intro h
    have hloop : target left = source left := by
      exact (show t = s from h.symm)
    have hd := hdecrease left
    rw [hloop] at hd
    exact (Nat.lt_irrefl _ hd)
  have hsu : s ≠ u := by
    intro h
    have hloop : target right = source right := by
      calc
        target right = u := rfl
        _ = s := h.symm
        _ = source left := rfl
        _ = source right := hsource
    have hd := hdecrease right
    rw [hloop] at hd
    exact (Nat.lt_irrefl _ hd)
  have htu : t ≠ u := by
    intro h
    apply hne
    apply hPair
    apply Prod.ext
    · exact hsource
    · exact h
  have hTripleCard : ({s, t, u} : Set V).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨s, t, u, hst, hsu, htu, rfl⟩
  have hUniv : ({s, t, u} : Set V) = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    simp [Set.ncard_univ, hcard, hTripleCard]
  have vertex_cases (v : V) : v = s ∨ v = t ∨ v = u := by
    have hv : v ∈ ({s, t, u} : Set V) := by rw [hUniv]; trivial
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hv
  rcases vertex_cases (source a) with hsa | hta | hua
  · rcases vertex_cases (target a) with has | hat | hau
    · have hlt := hdecrease a
      simp [hsa, has] at hlt
    · left
      apply hPair
      apply Prod.ext <;> assumption
    · right
      apply hPair
      apply Prod.ext
      · exact hsa.trans hsource
      · exact hau
  · rcases vertex_cases (target a) with has | hat | hau
    · have hleft := hdecrease left
      have ha' := hdecrease a
      simp [s, t, hta, has] at hleft ha'
      omega
    · have hlt := hdecrease a
      simp [hta, hat] at hlt
    · exact False.elim <| hNoTriangle left a right
        (by simpa [t] using hta.symm)
        hsource
        (by simpa [u] using hau)
  · rcases vertex_cases (target a) with has | hat | hau
    · have hright := hdecrease right
      have ha' := hdecrease a
      simp [s, u, hsource, hua, has] at hright ha'
      omega
    · exact False.elim <| hNoTriangle right a left
        (by simpa [u] using hua.symm)
        hsource.symm
        (by simpa [t] using hat)
    · have hlt := hdecrease a
      simp [hua, hau] at hlt

/-- Consequently, the target map of an exact common-source fork is
injective. -/
theorem target_injective_of_threeVertices_of_source_fork
    (hcard : Nat.card V = 3)
    (hPair : Function.Injective (fun a : Arrow => (source a, target a)))
    (height : V → ℕ)
    (hdecrease : ∀ a : Arrow, height (target a) < height (source a))
    (hNoTriangle : ∀ a b c : Arrow,
      target a = source b → source a = source c →
        target b = target c → False)
    (left right : Arrow) (hne : left ≠ right)
    (hsource : source left = source right) :
    Function.Injective target := by
  intro a b hab
  have ha := arrow_eq_left_or_right_of_threeVertices_of_source_fork
    source target hcard hPair height hdecrease hNoTriangle
      left right hne hsource a
  have hb := arrow_eq_left_or_right_of_threeVertices_of_source_fork
    source target hcard hPair height hdecrease hNoTriangle
      left right hne hsource b
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exfalso
    apply hne
    apply hPair
    exact Prod.ext hsource hab
  · exfalso
    apply hne
    apply hPair
    exact Prod.ext hsource hab.symm
  · rfl

end ThreeVertexSupport

/-- For a hereditary skeleton with exactly three simples, failure of
outgoing-degree one forces an exact source fork, so incoming-degree one
holds automatically. -/
theorem extTarget_injective_of_threeSimples_of_not_extSource_injective
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (hNotSource : ¬ Function.Injective
      (ExtGabrielArrowIndex.source (K := K) σ)) :
    Function.Injective (ExtGabrielArrowIndex.target (K := K) σ) := by
  classical
  letI : Finite σ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  simp only [Function.Injective] at hNotSource
  push Not at hNotSource
  obtain ⟨left, right, hsource, hne⟩ := hNotSource
  let hNoParallel : NoParallelExtSupport (K := K) σ :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ
  let height : σ.SimpleIndex → ℕ := fun s =>
    σ.compositionLength
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
        σ s)
  apply target_injective_of_threeVertices_of_source_fork
    (ExtGabrielArrowIndex.source (K := K) σ)
    (ExtGabrielArrowIndex.target (K := K) σ)
    hThree
    (ExtGabrielArrowIndex.source_target_injective σ hNoParallel)
    height
  · exact projectiveCoverLength_lt_of_extArrow K σ hHereditary
  · exact no_extTransitiveTriangle K σ hHereditary
  · exact hne
  · exact hsource

/-- The exact support exhaustion associated to the preceding source-fork
case. -/
theorem extArrow_eq_left_or_right_of_threeSimples_of_source_fork
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right)
    (a : ExtGabrielArrowIndex (K := K) σ) :
    a = left ∨ a = right := by
  letI : Finite σ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let hNoParallel : NoParallelExtSupport (K := K) σ :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ
  let height : σ.SimpleIndex → ℕ := fun s =>
    σ.compositionLength
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
        σ s)
  exact arrow_eq_left_or_right_of_threeVertices_of_source_fork
    (ExtGabrielArrowIndex.source (K := K) σ)
    (ExtGabrielArrowIndex.target (K := K) σ)
    hThree
    (ExtGabrielArrowIndex.source_target_injective σ hNoParallel)
    height
    (projectiveCoverLength_lt_of_extArrow K σ hHereditary)
    (no_extTransitiveTriangle K σ hHereditary)
    (left := left) (right := right) hne hsource a

set_option linter.unusedSectionVars false in
/-- If no Ext--Gabriel arrow starts at a chosen simple, the radical of its
indecomposable projective cover vanishes.  A nonzero radical would have a
simple quotient, and the radical--Ext equivalence would turn that quotient
into an outgoing arrow. -/
theorem projectiveRadical_eq_bot_of_no_extArrow_source
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (s : σ.SimpleIndex)
    (hNoArrow : ∀ a : ExtGabrielArrowIndex (K := K) σ,
      ExtGabrielArrowIndex.source σ a ≠ s) :
    Module.jacobson A
        (σ.obj
          (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
            σ s)) = ⊥ := by
  classical
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  let p :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex σ :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).symm s
  let P : FGModuleCat.{u} A := σ.obj p.1
  let J : Submodule A P := Module.jacobson A P
  change J = ⊥
  by_contra hJ
  letI : Nontrivial J := by
    rw [Submodule.nontrivial_iff_ne_bot]
    exact hJ
  obtain ⟨t, q, hq⟩ :=
    OpConjecture.ProjectiveRadicalExt.exists_surjective_to_chosen_simple
      σ (M := J)
  have hpTop :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIndex
          σ p = s :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).apply_symm_apply s
  let eTopFG :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTop σ p ≅
        σ.obj s.1 :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIso σ p ≪≫
      eqToIso (congrArg (fun z : σ.SimpleIndex => σ.obj z.1) hpTop)
  let eTop := FGModuleCat.isoToLinearEquiv eTopFG
  letI : Module.Projective A P :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.moduleProjective_of_fgProjective
      P p.2
  letI : IsSimpleModule A (σ.obj t.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (σ.obj t.1)).mp t.2
  letI : IsSemisimpleModule A (σ.obj t.1) := inferInstance
  let E :=
    OpConjecture.ProjectiveRadicalExt.radicalHomLinearEquivExtOne
      (K := K) (R := A) (P := P)
      (S := σ.obj s.1) (T := σ.obj t.1) eTop
  let qCat : ModuleCat.of A J ⟶ ModuleCat.of A (σ.obj t.1) :=
    ModuleCat.ofHom q
  have hqCat : qCat ≠ 0 := by
    intro hzero
    have hqzero : q = 0 := by
      have h := congrArg
        (fun f : ModuleCat.of A J ⟶ ModuleCat.of A (σ.obj t.1) => f.hom)
        hzero
      exact h
    letI : Nontrivial (σ.obj t.1) :=
      IsSimpleModule.nontrivial A (σ.obj t.1)
    obtain ⟨y, hy⟩ := exists_ne (0 : σ.obj t.1)
    obtain ⟨x, hx⟩ := hq y
    rw [hqzero] at hx
    exact hy hx.symm
  let η : ExtOne σ s t := E qCat
  have hη : η ≠ 0 := by
    intro hzero
    apply hqCat
    apply E.injective
    simpa [η] using hzero
  let hNoParallel : NoParallelExtSupport (K := K) σ :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ
  letI : FiniteDimensional K (ExtOne σ s t) :=
    (hNoParallel s t).1
  letI : Nontrivial (ExtOne σ s t) := ⟨η, 0, hη⟩
  let a : ExtGabrielArrowIndex (K := K) σ :=
    ⟨s, t, ⟨0, Module.finrank_pos⟩⟩
  exact hNoArrow a rfl

set_option linter.unusedSectionVars false in
/-- A nonzero map from the radical of a chosen indecomposable projective
cover to a chosen simple produces the corresponding Ext--Gabriel arrow. -/
theorem extArrow_of_ne_zero_projectiveRadical_to_simple
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (s t : σ.SimpleIndex)
    (q :
      ModuleCat.of A
          (Module.jacobson A
            (σ.obj
              (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
                σ s))) ⟶
        ModuleCat.of A (σ.obj t.1))
    (hq : q ≠ 0) :
    ∃ a : ExtGabrielArrowIndex (K := K) σ,
      ExtGabrielArrowIndex.source σ a = s ∧
        ExtGabrielArrowIndex.target σ a = t := by
  let p :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex σ :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).symm s
  have hpTop :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIndex
          σ p = s :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).apply_symm_apply s
  let eTopFG :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTop σ p ≅
        σ.obj s.1 :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIso σ p ≪≫
      eqToIso (congrArg (fun z : σ.SimpleIndex => σ.obj z.1) hpTop)
  let eTop := FGModuleCat.isoToLinearEquiv eTopFG
  letI : Module.Projective A (σ.obj p.1) :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.moduleProjective_of_fgProjective
      (σ.obj p.1) p.2
  letI : IsSimpleModule A (σ.obj t.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (σ.obj t.1)).mp t.2
  letI : IsSemisimpleModule A (σ.obj t.1) := inferInstance
  let E :=
    OpConjecture.ProjectiveRadicalExt.radicalHomLinearEquivExtOne
      (K := K) (R := A) (P := σ.obj p.1)
      (S := σ.obj s.1) (T := σ.obj t.1) eTop
  let η : ExtOne σ s t := E q
  have hη : η ≠ 0 := by
    intro hzero
    have hEq : E q = 0 := by
      exact hzero
    exact hq (E.map_eq_zero_iff.mp hEq)
  let hNoParallel : NoParallelExtSupport (K := K) σ :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ
  letI : FiniteDimensional K (ExtOne σ s t) :=
    (hNoParallel s t).1
  letI : Nontrivial (ExtOne σ s t) := ⟨η, 0, hη⟩
  exact ⟨⟨s, t, ⟨0, Module.finrank_pos⟩⟩, rfl, rfl⟩

set_option linter.unusedSectionVars false in
/-- An Ext--Gabriel arrow supplies a nonzero map from the radical of the
source projective cover to the target simple. -/
theorem exists_ne_zero_projectiveRadical_to_target_of_extArrow
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (a : ExtGabrielArrowIndex (K := K) σ) :
    ∃ q :
        Module.jacobson A
            (σ.obj
              (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
                σ (ExtGabrielArrowIndex.source σ a))) →ₗ[A]
          σ.obj (ExtGabrielArrowIndex.target σ a).1,
      q ≠ 0 := by
  let s := ExtGabrielArrowIndex.source σ a
  let t := ExtGabrielArrowIndex.target σ a
  let p :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex σ :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).symm s
  have hpTop :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIndex
          σ p = s :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).apply_symm_apply s
  let eTopFG :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTop σ p ≅
        σ.obj s.1 :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIso σ p ≪≫
      eqToIso (congrArg (fun z : σ.SimpleIndex => σ.obj z.1) hpTop)
  let eTop := FGModuleCat.isoToLinearEquiv eTopFG
  letI : Module.Projective A (σ.obj p.1) :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.moduleProjective_of_fgProjective
      (σ.obj p.1) p.2
  letI : IsSimpleModule A (σ.obj t.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (σ.obj t.1)).mp t.2
  letI : IsSemisimpleModule A (σ.obj t.1) := inferInstance
  let E :=
    OpConjecture.ProjectiveRadicalExt.radicalHomLinearEquivExtOne
      (K := K) (R := A) (P := σ.obj p.1)
      (S := σ.obj s.1) (T := σ.obj t.1) eTop
  let hNoParallel : NoParallelExtSupport (K := K) σ :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ
  letI : FiniteDimensional K (ExtOne σ s t) :=
    (hNoParallel s t).1
  have hpos : 0 < Module.finrank K (ExtOne σ s t) := by
    exact lt_of_le_of_lt (Nat.zero_le a.2.2.1) a.2.2.2
  letI : Nontrivial (ExtOne σ s t) :=
    Module.nontrivial_of_finrank_pos hpos
  obtain ⟨eta, heta⟩ := exists_ne (0 : ExtOne σ s t)
  let qCat :
      ModuleCat.of A (Module.jacobson A (σ.obj p.1)) ⟶
        ModuleCat.of A (σ.obj t.1) :=
    E.symm eta
  have hqCat : qCat ≠ 0 := by
    intro hzero
    apply heta
    apply E.symm.injective
    simpa [qCat] using hzero
  refine ⟨qCat.hom, ?_⟩
  intro hzero
  apply hqCat
  apply ModuleCat.hom_ext
  exact hzero

/-- A chosen indecomposable projective cover with zero radical is simple. -/
theorem isSimpleModule_projectiveCover_of_radical_eq_bot
    {A : Type u}
    [Ring A] [Small.{u} A] [IsNoetherianRing A]
    {ι : Type v}
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (s : σ.SimpleIndex)
    (hRadical :
      Module.jacobson A
          (σ.obj
            (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
              σ s)) = ⊥) :
    IsSimpleModule A
      (σ.obj
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
          σ s)) := by
  let p :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex σ :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).symm s
  have hTopSimple :
      IsSimpleModule A
        ((σ.obj p.1) ⧸ Module.jacobson A (σ.obj p.1)) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      _).mp
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTop_isSimple
          σ p)
  change IsSimpleModule A (σ.obj p.1)
  exact IsSimpleModule.congr
    (Submodule.quotEquivOfEqBot
      (Module.jacobson A (σ.obj p.1)) hRadical).symm

/-- In the exact three-simple source-fork case, neither target supports an
outgoing Ext arrow.  Hence both target projective covers have zero radical. -/
theorem forkTarget_projectiveRadicals_eq_bot
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right) :
    Module.jacobson A
          (σ.obj
            (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
              σ (ExtGabrielArrowIndex.target σ left))) = ⊥ ∧
      Module.jacobson A
          (σ.obj
            (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
              σ (ExtGabrielArrowIndex.target σ right))) = ⊥ := by
  have hAll (a : ExtGabrielArrowIndex (K := K) σ) :
      a = left ∨ a = right :=
    extArrow_eq_left_or_right_of_threeSimples_of_source_fork
      K σ hHereditary hThree left right hne hsource a
  have hNoLoop (a : ExtGabrielArrowIndex (K := K) σ) :
      ExtGabrielArrowIndex.source σ a ≠
        ExtGabrielArrowIndex.target σ a := by
    intro hloop
    have hlt := projectiveCoverLength_lt_of_extArrow K σ hHereditary a
    rw [← hloop] at hlt
    exact (Nat.lt_irrefl _ hlt)
  constructor
  · apply projectiveRadical_eq_bot_of_no_extArrow_source K σ
    intro a ha
    rcases hAll a with rfl | rfl
    · exact hNoLoop _ ha
    · apply hNoLoop left
      exact hsource.trans ha
  · apply projectiveRadical_eq_bot_of_no_extArrow_source K σ
    intro a ha
    rcases hAll a with rfl | rfl
    · apply hNoLoop right
      exact hsource.symm.trans ha
    · exact hNoLoop _ ha

/-- The source and the two distinct targets of a three-simple fork exhaust
the simple labels. -/
theorem simpleIndex_eq_source_or_targets_of_threeSimpleFork
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right)
    (v : σ.SimpleIndex) :
    v = ExtGabrielArrowIndex.source σ left ∨
      v = ExtGabrielArrowIndex.target σ left ∨
        v = ExtGabrielArrowIndex.target σ right := by
  classical
  letI : Finite σ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let s := ExtGabrielArrowIndex.source σ left
  let t := ExtGabrielArrowIndex.target σ left
  let r := ExtGabrielArrowIndex.target σ right
  have hNoLoop (a : ExtGabrielArrowIndex (K := K) σ) :
      ExtGabrielArrowIndex.source σ a ≠
        ExtGabrielArrowIndex.target σ a := by
    intro hloop
    have hlt := projectiveCoverLength_lt_of_extArrow K σ hHereditary a
    rw [← hloop] at hlt
    exact (Nat.lt_irrefl _ hlt)
  have hst : s ≠ t := hNoLoop left
  have hsr : s ≠ r := by
    intro h
    apply hNoLoop right
    exact hsource.symm.trans h
  have htr : t ≠ r := by
    intro h
    apply hne
    apply ExtGabrielArrowIndex.source_target_injective σ
      (OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ)
    exact Prod.ext hsource h
  have hTripleCard : ({s, t, r} : Set σ.SimpleIndex).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨s, t, r, hst, hsr, htr, rfl⟩
  have hUniv : ({s, t, r} : Set σ.SimpleIndex) = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    simp [Set.ncard_univ, hThree, hTripleCard]
  have hv : v ∈ ({s, t, r} : Set σ.SimpleIndex) := by
    rw [hUniv]
    trivial
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, s, t, r] using hv

/-- If the chosen projective cover of a simple has zero radical, then the
simple itself is projective. -/
theorem simple_projective_of_projectiveCoverRadical_eq_bot
    {A : Type u} [Ring A] [IsNoetherianRing A]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (v : σ.SimpleIndex)
    (hRadical :
      Module.jacobson A
        (σ.obj
          (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
            σ v)) = ⊥) :
    CategoryTheory.Projective (σ.obj v.1) := by
  let p :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex σ :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).symm v
  have hpTop :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIndex
          σ p = v :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).apply_symm_apply v
  let eBot :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTop σ p ≅
        σ.obj p.1 :=
    (Submodule.quotEquivOfEqBot
      (Module.jacobson A (σ.obj p.1)) hRadical).toFGModuleCatIso
  let eTarget : σ.obj p.1 ≅ σ.obj v.1 :=
    eBot.symm ≪≫
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIso
        σ p ≪≫
      eqToIso (congrArg (fun z : σ.SimpleIndex => σ.obj z.1) hpTop)
  letI : CategoryTheory.Projective (σ.obj p.1) := p.2
  exact CategoryTheory.Projective.of_iso eTarget inferInstance

/-- A nonsimple indecomposable in the exact fork case has no simple quotient
of either projective target type.  Since there are only three simple types,
all of its simple quotients have the fork-source type. -/
theorem simpleQuotient_index_eq_source_of_not_simple_threeSimpleFork
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right)
    (j : ι) (hj : ¬ Simple (σ.obj j))
    (Q : σ.SimpleQuotient j) :
    Q.index = (ExtGabrielArrowIndex.source σ left).1 := by
  let hTargets := forkTarget_projectiveRadicals_eq_bot
    K σ hHereditary hThree left right hne hsource
  have hLeftProjective : CategoryTheory.Projective
      (σ.obj (ExtGabrielArrowIndex.target σ left).1) :=
    simple_projective_of_projectiveCoverRadical_eq_bot
      σ (ExtGabrielArrowIndex.target σ left) hTargets.1
  have hRightProjective : CategoryTheory.Projective
      (σ.obj (ExtGabrielArrowIndex.target σ right).1) :=
    simple_projective_of_projectiveCoverRadical_eq_bot
      σ (ExtGabrielArrowIndex.target σ right) hTargets.2
  let qSimple : σ.SimpleIndex := ⟨Q.index, Q.simple⟩
  rcases simpleIndex_eq_source_or_targets_of_threeSimpleFork
    K σ hHereditary hThree left right hne hsource qSimple with hq | hq | hq
  · exact congrArg Subtype.val hq
  · exfalso
    apply hj
    have hqVal : Q.index = (ExtGabrielArrowIndex.target σ left).1 :=
      congrArg Subtype.val hq
    have hQProjective : CategoryTheory.Projective (σ.obj Q.index) := by
      rw [hqVal]
      exact hLeftProjective
    letI : CategoryTheory.Projective (σ.obj Q.index) := hQProjective
    letI : Epi Q.map := Q.epi
    obtain ⟨sec, hsec⟩ :=
      CategoryTheory.Projective.factors (𝟙 (σ.obj Q.index)) Q.map
    letI : IsSplitEpi Q.map := IsSplitEpi.mk'
      { section_ := sec
        id := hsec }
    letI : IsSplitMono Q.map :=
      σ.isSplitMono_of_isSplitEpi_between_obj Q.map
    letI : IsIso Q.map := isIso_of_mono_of_isSplitEpi Q.map
    exact (Simple.iff_of_iso (asIso Q.map)).mpr Q.simple
  · exfalso
    apply hj
    have hqVal : Q.index = (ExtGabrielArrowIndex.target σ right).1 :=
      congrArg Subtype.val hq
    have hQProjective : CategoryTheory.Projective (σ.obj Q.index) := by
      rw [hqVal]
      exact hRightProjective
    letI : CategoryTheory.Projective (σ.obj Q.index) := hQProjective
    letI : Epi Q.map := Q.epi
    obtain ⟨sec, hsec⟩ :=
      CategoryTheory.Projective.factors (𝟙 (σ.obj Q.index)) Q.map
    letI : IsSplitEpi Q.map := IsSplitEpi.mk'
      { section_ := sec
        id := hsec }
    letI : IsSplitMono Q.map :=
      σ.isSplitMono_of_isSplitEpi_between_obj Q.map
    letI : IsIso Q.map := isIso_of_mono_of_isSplitEpi Q.map
    exact (Simple.iff_of_iso (asIso Q.map)).mpr Q.simple

/-- In the exact source-fork case, the radical of the source projective cover
is a finite direct sum of the two simple target projectives, and is therefore
semisimple. -/
theorem forkSource_projectiveRadical_isSemisimple
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right) :
    IsSemisimpleModule A
      (Module.jacobson A
        (σ.obj
          (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
            σ (ExtGabrielArrowIndex.source σ left)))) := by
  classical
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  let s := ExtGabrielArrowIndex.source σ left
  let p :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex σ :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).symm s
  let J : Submodule A (σ.obj p.1) := Module.jacobson A (σ.obj p.1)
  have hJModuleProjective : Module.Projective A J :=
    hHereditary (σ.obj p.1) p.2 J
  have hJProjective : CategoryTheory.Projective (FGModuleCat.of A J) :=
    OpConjecture.RingelStable.fgProjective_of_moduleProjective
      (FGModuleCat.of A J) hJModuleProjective
  letI : CategoryTheory.Projective (FGModuleCat.of A J) := hJProjective
  obtain ⟨n, labels, ⟨e⟩⟩ := σ.decomposes (FGModuleCat.of A J)
  have hSumProjective :
      CategoryTheory.Projective (⨁ fun i : Fin n => σ.obj (labels i)) :=
    CategoryTheory.Projective.of_iso e inferInstance
  letI : CategoryTheory.Projective
      (⨁ fun i : Fin n => σ.obj (labels i)) := hSumProjective
  have hTargets := forkTarget_projectiveRadicals_eq_bot
    K σ hHereditary hThree left right hne hsource
  have hAll (a : ExtGabrielArrowIndex (K := K) σ) :
      a = left ∨ a = right :=
    extArrow_eq_left_or_right_of_threeSimples_of_source_fork
      K σ hHereditary hThree left right hne hsource a
  have hComponentSimple (i : Fin n) :
      IsSimpleModule A (σ.obj (labels i)) := by
    have hComponentProjective : CategoryTheory.Projective (σ.obj (labels i)) :=
      projective_biproduct_component
        (fun j : Fin n => σ.obj (labels j)) i
    let pi :
        OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex σ :=
      ⟨labels i, hComponentProjective⟩
    let ti : σ.SimpleIndex :=
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIndex σ pi
    let qRad : σ.obj pi.1 ⟶
        OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTop σ pi :=
      FGModuleCat.ofHom (Module.jacobson A (σ.obj pi.1)).mkQ
    haveI : Epi qRad :=
      (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective qRad).mpr
        (Module.jacobson A (σ.obj pi.1)).mkQ_surjective
    let qTop : σ.obj pi.1 ⟶ σ.obj ti.1 :=
      qRad ≫
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIso
          σ pi).hom
    let qFG : FGModuleCat.of A J ⟶ σ.obj ti.1 :=
      e.hom ≫ biproduct.π (fun j : Fin n => σ.obj (labels j)) i ≫ qTop
    letI : Epi qFG := by
      dsimp [qFG, qTop]
      infer_instance
    have hqFG : qFG ≠ 0 := by
      intro hzero
      letI : Simple (σ.obj ti.1) := ti.2
      exact Simple.not_isZero (σ.obj ti.1)
        (IsZero.of_epi_eq_zero qFG hzero)
    have hq : qFG.hom ≠ 0 := by
      intro hzero
      apply hqFG
      ext x
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hzero) x
    obtain ⟨a, haSource, haTarget⟩ :=
      extArrow_of_ne_zero_projectiveRadical_to_simple
        K σ s ti qFG.hom hq
    have hti : ti = ExtGabrielArrowIndex.target σ left ∨
        ti = ExtGabrielArrowIndex.target σ right := by
      rcases hAll a with rfl | rfl
      · exact Or.inl haTarget.symm
      · exact Or.inr haTarget.symm
    have htiRadical :
        Module.jacobson A
          (σ.obj
            (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
              σ ti)) = ⊥ := by
      rcases hti with hti | hti
      · rw [hti]
        exact hTargets.1
      · rw [hti]
        exact hTargets.2
    have hpiSubtype :
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
            σ).symm ti = pi := by
      change
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
            σ).symm
            ((OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
              σ) pi) = pi
      exact
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
          σ).symm_apply_apply pi
    have hpi :
        OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
            σ ti = labels i := by
      change
        ((OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
          σ).symm ti).1 = labels i
      exact congrArg Subtype.val hpiSubtype
    have hsimp := isSimpleModule_projectiveCover_of_radical_eq_bot
      σ ti htiRadical
    rw [hpi] at hsimp
    exact hsimp
  letI (i : Fin n) : IsSimpleModule A (σ.obj (labels i)) :=
    hComponentSimple i
  letI : IsSemisimpleModule A (∀ i : Fin n, σ.obj (labels i)) :=
    inferInstance
  let ePi :
      σ.sumOver (FintypeCat.of (Fin n)) labels ≅
        FGModuleCat.of A (∀ i : Fin n, σ.obj (labels i)) :=
    OpConjecture.IndecomposableSkeleton.biproductIsoPiFG _
  have hSumSemisimple : IsSemisimpleModule A
      (σ.sumOver (FintypeCat.of (Fin n)) labels) :=
    (LinearEquiv.isSemisimpleModule_iff
      (FGModuleCat.isoToLinearEquiv ePi)).mpr inferInstance
  have hJSemisimple : IsSemisimpleModule A J :=
    (LinearEquiv.isSemisimpleModule_iff
      (FGModuleCat.isoToLinearEquiv e)).mpr hSumSemisimple
  change IsSemisimpleModule A J
  exact hJSemisimple

/-- An Ext arrow whose source projective has semisimple radical realizes its
target simple as a simple submodule of that radical. -/
theorem exists_simpleSubmodule_projectiveRadical_of_extArrow
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (a : ExtGabrielArrowIndex (K := K) σ)
    (hSemisimple : IsSemisimpleModule A
      (Module.jacobson A
        (σ.obj
          (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
            σ (ExtGabrielArrowIndex.source σ a))))) :
    ∃ L : Submodule A
        (Module.jacobson A
          (σ.obj
            (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
              σ (ExtGabrielArrowIndex.source σ a)))),
      IsSimpleModule A L ∧
        Nonempty (L ≃ₗ[A] σ.obj (ExtGabrielArrowIndex.target σ a).1) := by
  let J :=
    Module.jacobson A
      (σ.obj
        (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
          σ (ExtGabrielArrowIndex.source σ a)))
  letI : IsSemisimpleModule A J := hSemisimple
  obtain ⟨q, hq⟩ :=
    exists_ne_zero_projectiveRadical_to_target_of_extArrow K σ a
  letI : IsSimpleModule A
      (σ.obj (ExtGabrielArrowIndex.target σ a).1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      (ExtGabrielArrowIndex.target σ a).2
  have hsurj : Function.Surjective q :=
    LinearMap.surjective_of_ne_zero hq
  obtain ⟨L, ⟨eL⟩⟩ :=
    IsSemisimpleModule.exists_submodule_linearEquiv_quotient
      (LinearMap.ker q)
  let e : L ≃ₗ[A] σ.obj (ExtGabrielArrowIndex.target σ a).1 :=
    eL.trans (q.quotKerEquivOfSurjective hsurj)
  exact ⟨L, IsSimpleModule.congr e, ⟨e⟩⟩

/-- Every simple constituent of the source projective's radical is one of
the two fork targets. -/
theorem forkSource_projectiveRadical_hasTwoTargetConstituents
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right) :
    TwoTypeSemisimple.HasSimpleConstituentsOfEitherType (R := A)
      (Module.jacobson A
        (σ.obj
          (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
            σ (ExtGabrielArrowIndex.source σ left))))
      (σ.obj (ExtGabrielArrowIndex.target σ left).1)
      (σ.obj (ExtGabrielArrowIndex.target σ right).1) := by
  classical
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  let s := ExtGabrielArrowIndex.source σ left
  let p :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex σ :=
    (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ).symm s
  let J : Submodule A (σ.obj p.1) := Module.jacobson A (σ.obj p.1)
  letI : IsSemisimpleModule A J := by
    exact forkSource_projectiveRadical_isSemisimple
      K σ hHereditary hThree left right hne hsource
  change TwoTypeSemisimple.HasSimpleConstituentsOfEitherType (R := A)
    J
    (σ.obj (ExtGabrielArrowIndex.target σ left).1)
    (σ.obj (ExtGabrielArrowIndex.target σ right).1)
  have hAll (a : ExtGabrielArrowIndex (K := K) σ) :
      a = left ∨ a = right :=
    extArrow_eq_left_or_right_of_threeSimples_of_source_fork
      K σ hHereditary hThree left right hne hsource a
  intro L hL
  letI : IsSimpleModule A L := hL
  letI : Module.Finite A L := inferInstance
  let LFG : FGModuleCat.{u} A := FGModuleCat.of A L
  have hLIndec : OpConjecture.Foundation.IsIndecomposableModule A LFG :=
    OpConjecture.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨v, ⟨e⟩⟩ := σ.complete LFG hLIndec
  have hvSimple : Simple (σ.obj v) := by
    have hLFGSimple : Simple LFG :=
      (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
        LFG).mpr hL
    exact (Simple.iff_of_iso e).mp hLFGSimple
  let vSimple : σ.SimpleIndex := ⟨v, hvSimple⟩
  obtain ⟨c, hLc⟩ := exists_isCompl L
  let projection : J →ₗ[A] L :=
    Submodule.projectionOnto L c hLc
  have hprojection : Function.Surjective projection :=
    Submodule.projectionOnto_surjective hLc
  let q : ModuleCat.of A J ⟶ ModuleCat.of A (σ.obj v) :=
    ModuleCat.ofHom (e.hom.hom.hom.comp projection)
  have hqSurj : Function.Surjective q.hom :=
    (FGModuleCat.isoToLinearEquiv e).surjective.comp hprojection
  letI : Epi q := (ModuleCat.epi_iff_surjective q).mpr hqSurj
  letI : IsSimpleModule A (σ.obj v) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (σ.obj v)).mp hvSimple
  letI : Simple (ModuleCat.of A (σ.obj v)) :=
    (simple_iff_isSimpleModule' (ModuleCat.of A (σ.obj v))).mpr
      inferInstance
  have hq : q ≠ 0 := by
    intro hzero
    exact Simple.not_isZero (ModuleCat.of A (σ.obj v))
      (IsZero.of_epi_eq_zero q hzero)
  obtain ⟨a, haSource, haTarget⟩ :=
    extArrow_of_ne_zero_projectiveRadical_to_simple
      K σ s vSimple q hq
  let eLin : L ≃ₗ[A] σ.obj v := FGModuleCat.isoToLinearEquiv e
  rcases hAll a with rfl | rfl
  · exact Or.inl ⟨eLin.trans
      (FGModuleCat.isoToLinearEquiv
        (eqToIso (congrArg (fun z : σ.SimpleIndex => σ.obj z.1)
          haTarget.symm)))⟩
  · exact Or.inr ⟨eLin.trans
      (FGModuleCat.isoToLinearEquiv
        (eqToIso (congrArg (fun z : σ.SimpleIndex => σ.obj z.1)
          haTarget.symm)))⟩

/-- Every chosen indecomposable projective cover has semisimple radical in
the exact three-simple source-fork case. -/
theorem projectiveCoverRadical_isSemisimple_of_threeSimpleFork
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right)
    (v : σ.SimpleIndex) :
    IsSemisimpleModule A
      (Module.jacobson A
        (σ.obj
          (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
            σ v))) := by
  rcases simpleIndex_eq_source_or_targets_of_threeSimpleFork
    K σ hHereditary hThree left right hne hsource v with hv | hv | hv
  · rw [hv]
    exact forkSource_projectiveRadical_isSemisimple
      K σ hHereditary hThree left right hne hsource
  · have hTargets := forkTarget_projectiveRadicals_eq_bot
      K σ hHereditary hThree left right hne hsource
    rw [hv, hTargets.1]
    exact (isSemisimpleModule_iff A _).mpr
      Subsingleton.instComplementedLattice
  · have hTargets := forkTarget_projectiveRadicals_eq_bot
      K σ hHereditary hThree left right hne hsource
    rw [hv, hTargets.2]
    exact (isSemisimpleModule_iff A _).mpr
      Subsingleton.instComplementedLattice

/-- The radical of any indecomposable projective skeleton representative is
semisimple in the exact fork case. -/
theorem projectiveRadical_isSemisimple_of_threeSimpleFork
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right)
    (i : ι) (hi : CategoryTheory.Projective (σ.obj i)) :
    IsSemisimpleModule A (Module.jacobson A (σ.obj i)) := by
  let pi :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex σ :=
    ⟨i, hi⟩
  let v : σ.SimpleIndex :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIndex σ pi
  have hpiSubtype :
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
          σ).symm v = pi := by
    change
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
          σ).symm
          ((OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
            σ) pi) = pi
    exact
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
        σ).symm_apply_apply pi
  have hlabel :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
          σ v = i := by
    change
      ((OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
        σ).symm v).1 = i
    exact congrArg Subtype.val hpiSubtype
  have h := projectiveCoverRadical_isSemisimple_of_threeSimpleFork
    K σ hHereditary hThree left right hne hsource v
  rw [hlabel] at h
  exact h

/-- The radical of any indecomposable projective has only the two fork-target
simple constituent types. -/
theorem projectiveRadical_hasTwoTargetConstituents_of_threeSimpleFork
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right)
    (i : ι) (hi : CategoryTheory.Projective (σ.obj i)) :
    TwoTypeSemisimple.HasSimpleConstituentsOfEitherType (R := A)
      (Module.jacobson A (σ.obj i))
      (σ.obj (ExtGabrielArrowIndex.target σ left).1)
      (σ.obj (ExtGabrielArrowIndex.target σ right).1) := by
  let pi :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex σ :=
    ⟨i, hi⟩
  let v : σ.SimpleIndex :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTopIndex σ pi
  have hpiSubtype :
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
          σ).symm v = pi := by
    change
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
          σ).symm
          ((OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
            σ) pi) = pi
    exact
      (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
        σ).symm_apply_apply pi
  have hlabel :
      OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
          σ v = i := by
    change
      ((OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
        σ).symm v).1 = i
    exact congrArg Subtype.val hpiSubtype
  have hvTypes : TwoTypeSemisimple.HasSimpleConstituentsOfEitherType (R := A)
      (Module.jacobson A
        (σ.obj
          (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
            σ v)))
      (σ.obj (ExtGabrielArrowIndex.target σ left).1)
      (σ.obj (ExtGabrielArrowIndex.target σ right).1) := by
    rcases simpleIndex_eq_source_or_targets_of_threeSimpleFork
      K σ hHereditary hThree left right hne hsource v with hv | hv | hv
    · rw [hv]
      exact forkSource_projectiveRadical_hasTwoTargetConstituents
        K σ hHereditary hThree left right hne hsource
    · have hTargets := forkTarget_projectiveRadicals_eq_bot
        K σ hHereditary hThree left right hne hsource
      have hRadical : Module.jacobson A
          (σ.obj
            (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
              σ v)) = ⊥ := by
        rw [hv]
        exact hTargets.1
      letI : Subsingleton
          (Module.jacobson A
            (σ.obj
              (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
                σ v))) := by
        rw [Submodule.subsingleton_iff_eq_bot]
        exact hRadical
      exact TwoTypeSemisimple.HasSimpleConstituentsOfEitherType.of_subsingleton
        (R := A)
    · have hTargets := forkTarget_projectiveRadicals_eq_bot
        K σ hHereditary hThree left right hne hsource
      have hRadical : Module.jacobson A
          (σ.obj
            (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
              σ v)) = ⊥ := by
        rw [hv]
        exact hTargets.2
      letI : Subsingleton
          (Module.jacobson A
            (σ.obj
              (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
                σ v))) := by
        rw [Submodule.subsingleton_iff_eq_bot]
        exact hRadical
      exact TwoTypeSemisimple.HasSimpleConstituentsOfEitherType.of_subsingleton
        (R := A)
  rw [hlabel] at hvTypes
  exact hvTypes

/-- Every indecomposable module has semisimple radical in the exact fork
case.  A projective presentation maps the semisimple radical of its source
onto the module radical. -/
theorem moduleRadical_isSemisimple_of_threeSimpleFork
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right)
    (j : ι) :
    IsSemisimpleModule A (σ.moduleRadical j) := by
  classical
  obtain ⟨P⟩ :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.inFac_projectiveLabels
      σ (σ.obj j)
  letI (t : P.index) : IsArtinian A (σ.obj (P.label t)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength (P.label t))).2
  let e :
      σ.sumOver P.index P.label ≅
        FGModuleCat.of A (∀ t : P.index, σ.obj (P.label t)) :=
    OpConjecture.IndecomposableSkeleton.biproductIsoPiFG _
  letI : IsArtinian A (σ.sumOver P.index P.label) :=
    (LinearEquiv.isArtinian_iff
      (FGModuleCat.isoToLinearEquiv e)).mpr inferInstance
  have hSourceRadical : IsSemisimpleModule A
      (Module.jacobson A (σ.sumOver P.index P.label)) := by
    apply
      OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.moduleRadical_sumOver_isSemisimple
        σ P.index P.label
    intro t
    exact projectiveRadical_isSemisimple_of_threeSimpleFork
      K σ hHereditary hThree left right hne hsource
        (P.label t) (P.mem t)
  letI : IsSemisimpleModule A
      (Module.jacobson A (σ.sumOver P.index P.label)) := hSourceRadical
  letI : Epi P.map := P.epi
  have hsurj : Function.Surjective P.map.hom.hom :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective P.map).mp
      inferInstance
  let radicalMap :
      Module.jacobson A (σ.sumOver P.index P.label) →ₗ[A]
        σ.moduleRadical j :=
    OpConjecture.ProjectiveRadicalExt.radicalMapOfSurjective P.map.hom.hom
  have hradicalMap : Function.Surjective radicalMap :=
    OpConjecture.ProjectiveRadicalExt.radicalMapOfSurjective_surjective
      P.map.hom.hom hsurj
  exact IsSemisimpleModule.of_surjective radicalMap hradicalMap

/-- Every indecomposable module radical has only the two fork-target simple
constituent types. -/
theorem moduleRadical_hasTwoTargetConstituents_of_threeSimpleFork
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right)
    (j : ι) :
    TwoTypeSemisimple.HasSimpleConstituentsOfEitherType (R := A)
      (σ.moduleRadical j)
      (σ.obj (ExtGabrielArrowIndex.target σ left).1)
      (σ.obj (ExtGabrielArrowIndex.target σ right).1) := by
  classical
  obtain ⟨P⟩ :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.inFac_projectiveLabels
      σ (σ.obj j)
  letI (t : P.index) : IsArtinian A (σ.obj (P.label t)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength (P.label t))).2
  let e :
      σ.sumOver P.index P.label ≅
        FGModuleCat.of A (∀ t : P.index, σ.obj (P.label t)) :=
    OpConjecture.IndecomposableSkeleton.biproductIsoPiFG _
  letI : IsArtinian A (σ.sumOver P.index P.label) :=
    (LinearEquiv.isArtinian_iff
      (FGModuleCat.isoToLinearEquiv e)).mpr inferInstance
  have hSourceSemisimple : IsSemisimpleModule A
      (Module.jacobson A (σ.sumOver P.index P.label)) := by
    apply
      OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.moduleRadical_sumOver_isSemisimple
        σ P.index P.label
    intro t
    exact projectiveRadical_isSemisimple_of_threeSimpleFork
      K σ hHereditary hThree left right hne hsource
        (P.label t) (P.mem t)
  letI : IsSemisimpleModule A
      (Module.jacobson A (σ.sumOver P.index P.label)) := hSourceSemisimple
  have hSourceTypes :
      TwoTypeSemisimple.HasSimpleConstituentsOfEitherType (R := A)
        (Module.jacobson A (σ.sumOver P.index P.label))
        (σ.obj (ExtGabrielArrowIndex.target σ left).1)
        (σ.obj (ExtGabrielArrowIndex.target σ right).1) := by
    apply
      TwoTypeSemisimple.moduleRadical_sumOver_hasSimpleConstituentsOfEitherType
        (R := A) σ P.index P.label
    intro t
    exact projectiveRadical_hasTwoTargetConstituents_of_threeSimpleFork
      K σ hHereditary hThree left right hne hsource
        (P.label t) (P.mem t)
  letI : Epi P.map := P.epi
  have hsurj : Function.Surjective P.map.hom.hom :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective P.map).mp
      inferInstance
  let radicalMap :
      Module.jacobson A (σ.sumOver P.index P.label) →ₗ[A]
        σ.moduleRadical j :=
    OpConjecture.ProjectiveRadicalExt.radicalMapOfSurjective P.map.hom.hom
  have hradicalMap : Function.Surjective radicalMap :=
    OpConjecture.ProjectiveRadicalExt.radicalMapOfSurjective_surjective
      P.map.hom.hom hsurj
  exact hSourceTypes.of_surjective_of_semisimple radicalMap hradicalMap

/-- The top of every nonsimple indecomposable in the exact fork case is
isotypic of the fork source. -/
theorem moduleTop_isIsotypicSource_of_not_simple_threeSimpleFork
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right)
    (j : ι) (hj : ¬ Simple (σ.obj j)) :
    IsIsotypicOfType A (σ.moduleTop j)
      (σ.obj (ExtGabrielArrowIndex.source σ left).1) := by
  have hunique : σ.HasUniqueSimpleQuotientType j
      (ExtGabrielArrowIndex.source σ left).1 := by
    refine ⟨(ExtGabrielArrowIndex.source σ left).2, ?_⟩
    intro Q
    exact simpleQuotient_index_eq_source_of_not_simple_threeSimpleFork
      K σ hHereditary hThree left right hne hsource j hj Q
  exact
    OpConjecture.LevelTwoUnconditional.moduleTop_isIsotypicOfType_of_hasUniqueSimpleQuotientType
      σ hunique

/-- The radical of every indecomposable admits a finite two-target
decomposition. -/
theorem exists_moduleRadical_twoTargetDecomposition_threeSimpleFork
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right)
    (j : ι) :
    ∃ (J L : Type) (_ : Fintype J) (_ : Fintype L),
      Nonempty
        (σ.moduleRadical j ≃ₗ[A]
          (J → σ.obj (ExtGabrielArrowIndex.target σ left).1) ×
          (L → σ.obj (ExtGabrielArrowIndex.target σ right).1)) := by
  letI : IsSemisimpleModule A (σ.moduleRadical j) :=
    moduleRadical_isSemisimple_of_threeSimpleFork
      K σ hHereditary hThree left right hne hsource j
  letI : Module.Finite A (σ.moduleRadical j) := inferInstance
  letI : IsSimpleModule A
      (σ.obj (ExtGabrielArrowIndex.target σ left).1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      (ExtGabrielArrowIndex.target σ left).2
  letI : IsSimpleModule A
      (σ.obj (ExtGabrielArrowIndex.target σ right).1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      (ExtGabrielArrowIndex.target σ right).2
  exact TwoTypeSemisimple.exists_twoTypeDecomposition
    (R := A)
    (moduleRadical_hasTwoTargetConstituents_of_threeSimpleFork
      K σ hHereditary hThree left right hne hsource j)

/-- Every indecomposable has simple top in the exact three-simple fork case. -/
theorem moduleTop_isSimple_of_threeSimpleFork
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right)
    (j : ι) :
    IsSimpleModule A (σ.moduleTop j) := by
  by_cases hj : Simple (σ.obj j)
  · exact σ.moduleTop_isSimple_of_simple hj
  · obtain ⟨J, L, hJ, hL, ⟨eRadical⟩⟩ :=
      exists_moduleRadical_twoTargetDecomposition_threeSimpleFork
        K σ hHereditary hThree left right hne hsource j
    letI : Fintype J := hJ
    letI : Fintype L := hL
    letI : IsSimpleModule A
        (σ.obj (ExtGabrielArrowIndex.source σ left).1) :=
      (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
        (ExtGabrielArrowIndex.source σ left).2
    have htopIsotypic :=
      moduleTop_isIsotypicSource_of_not_simple_threeSimpleFork
        K σ hHereditary hThree left right hne hsource j hj
    letI : IsSemisimpleModule A (σ.moduleTop j) :=
      σ.moduleTop_isSemisimple j
    letI : Module.Finite A (σ.moduleTop j) := inferInstance
    obtain ⟨k, eTop, htopLength⟩ :=
      OpConjecture.LoewyTwoRankCore.exists_isotypicMultiplicity
        htopIsotypic
    let hNoParallel : NoParallelExtSupport (K := K) σ :=
      OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ
    apply moduleTop_isSimple_of_twoTargetDecomposition
      K σ hNoParallel
      (ExtGabrielArrowIndex.target σ left).2
      (ExtGabrielArrowIndex.target σ right).2
      (ExtGabrielArrowIndex.source σ left).2
      eRadical.symm eTop.symm
    simpa using htopLength

/-- Every indecomposable radical in the exact fork has at most one copy of
each target-simple type. -/
theorem exists_moduleRadical_twoTargetDecomposition_with_bounds_threeSimpleFork
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right)
    (j : ι) :
    ∃ (J L : Type) (_ : Fintype J) (_ : Fintype L),
      Nonempty
        (σ.moduleRadical j ≃ₗ[A]
          (J → σ.obj (ExtGabrielArrowIndex.target σ left).1) ×
          (L → σ.obj (ExtGabrielArrowIndex.target σ right).1)) ∧
        Fintype.card J ≤ 1 ∧ Fintype.card L ≤ 1 := by
  obtain ⟨J, L, hJ, hL, ⟨eRadical⟩⟩ :=
    exists_moduleRadical_twoTargetDecomposition_threeSimpleFork
      K σ hHereditary hThree left right hne hsource j
  letI : Fintype J := hJ
  letI : Fintype L := hL
  have hTopSimple : IsSimpleModule A (σ.moduleTop j) :=
    moduleTop_isSimple_of_threeSimpleFork
      K σ hHereditary hThree left right hne hsource j
  let Top : FGModuleCat.{u} A := FGModuleCat.of A (σ.moduleTop j)
  have hTopSimpleCat : Simple Top :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      Top).mpr hTopSimple
  have hTopIndec : OpConjecture.Foundation.IsIndecomposableModule A Top :=
    OpConjecture.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨r, ⟨eTopFG⟩⟩ := σ.complete Top hTopIndec
  have hr : Simple (σ.obj r) :=
    (Simple.iff_of_iso eTopFG).mp hTopSimpleCat
  let eTop : σ.obj r ≃ₗ[A] σ.moduleTop j :=
    (FGModuleCat.isoToLinearEquiv eTopFG).symm
  have hbounds :=
    radicalMultiplicityBounds_of_simpleTop_twoTypeDecomposition
      K σ
      (OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ)
      (ExtGabrielArrowIndex.target σ left).2
      (ExtGabrielArrowIndex.target σ right).2
      hr eRadical.symm eTop
  exact ⟨J, L, inferInstance, inferInstance,
    ⟨eRadical⟩, hbounds.1, hbounds.2⟩

/-- The radical of the fork-source projective consists of exactly the two
distinct target simples, hence has composition length two. -/
theorem forkSource_projectiveRadical_length_eq_two
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right) :
    Module.length A
        (Module.jacobson A
          (σ.obj
            (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
              σ (ExtGabrielArrowIndex.source σ left)))) = 2 := by
  classical
  let p :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
      σ (ExtGabrielArrowIndex.source σ left)
  let Rad : Submodule A (σ.obj p) := Module.jacobson A (σ.obj p)
  obtain ⟨J, L, hJ, hL, ⟨eRadical⟩, hJcard, hLcard⟩ :=
    exists_moduleRadical_twoTargetDecomposition_with_bounds_threeSimpleFork
      K σ hHereditary hThree left right hne hsource p
  letI : Fintype J := hJ
  letI : Fintype L := hL
  letI : IsSimpleModule A
      (σ.obj (ExtGabrielArrowIndex.target σ left).1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      (ExtGabrielArrowIndex.target σ left).2
  letI : IsSimpleModule A
      (σ.obj (ExtGabrielArrowIndex.target σ right).1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      (ExtGabrielArrowIndex.target σ right).2
  have hlengthFormula :
      Module.length A Rad =
        (Fintype.card J : ℕ∞) + (Fintype.card L : ℕ∞) := by
    change Module.length A (σ.moduleRadical p) = _
    rw [eRadical.length_eq, Module.length_prod,
      Module.length_pi_of_fintype, Module.length_pi_of_fintype]
    simp [Module.length_eq_one]
  have hcardSum : Fintype.card J + Fintype.card L ≤ 2 := by omega
  have hUpper : Module.length A Rad ≤ 2 := by
    rw [hlengthFormula, ← ENat.coe_add]
    exact ENat.coe_le_coe.mpr hcardSum
  have hRadSemisimple : IsSemisimpleModule A Rad :=
    forkSource_projectiveRadical_isSemisimple
      K σ hHereditary hThree left right hne hsource
  obtain ⟨Lleft, hLleft, ⟨eLeft⟩⟩ :=
    exists_simpleSubmodule_projectiveRadical_of_extArrow
      K σ left hRadSemisimple
  obtain ⟨Lright, hLright, ⟨eRightRaw⟩⟩ :=
    exists_simpleSubmodule_projectiveRadical_of_extArrow
      K σ
        (⟨ExtGabrielArrowIndex.source σ left,
          ExtGabrielArrowIndex.target σ right,
          hsource.symm ▸ right.2.2⟩ :
            ExtGabrielArrowIndex (K := K) σ)
        hRadSemisimple
  change Submodule A Rad at Lright
  have hRightTarget :
      ExtGabrielArrowIndex.target σ
          (⟨ExtGabrielArrowIndex.source σ left,
            ExtGabrielArrowIndex.target σ right,
            hsource.symm ▸ right.2.2⟩ :
              ExtGabrielArrowIndex (K := K) σ) =
        ExtGabrielArrowIndex.target σ right := by
    apply Subtype.ext
    rfl
  let eRight : Lright ≃ₗ[A]
      σ.obj (ExtGabrielArrowIndex.target σ right).1 :=
    eRightRaw.trans <| FGModuleCat.isoToLinearEquiv <|
      eqToIso <| congrArg (fun s : σ.SimpleIndex => σ.obj s.1) hRightTarget
  have hTargetNe : ExtGabrielArrowIndex.target σ left ≠
      ExtGabrielArrowIndex.target σ right := by
    intro htarget
    apply hne
    apply ExtGabrielArrowIndex.source_target_injective σ
      (OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ)
    exact Prod.ext hsource htarget
  have hSubNe : Lleft ≠ Lright := by
    intro hEq
    subst Lright
    apply hTargetNe
    apply Subtype.ext
    apply σ.eq_of_iso
    exact ⟨(eLeft.symm.trans eRight).toFGModuleCatIso⟩
  letI : IsSimpleModule A Lleft := hLleft
  letI : IsSimpleModule A Lright := hLright
  have hDisjoint : Disjoint Lleft Lright :=
    (isSimpleModule_iff_isAtom.mp hLleft).disjoint_of_ne
      (isSimpleModule_iff_isAtom.mp hLright) hSubNe
  let f : (Lleft × Lright) →ₗ[A] Rad :=
    Lleft.subtype.coprod Lright.subtype
  have hf : Function.Injective f :=
    submoduleSubtype_coprod_injective_of_disjoint hDisjoint
  have hLower : (2 : ℕ∞) ≤ Module.length A Rad := by
    have hle := Module.length_le_of_injective f hf
    rw [Module.length_prod,
      Module.length_eq_one A Lleft,
      Module.length_eq_one A Lright] at hle
    norm_num at hle ⊢
    exact hle
  exact le_antisymm hUpper hLower

/-- The two target simples form complementary submodules of the source
projective radical. -/
theorem exists_forkSource_projectiveRadical_target_isCompl
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right) :
    ∃ (Lleft Lright : Submodule A
        (Module.jacobson A
          (σ.obj
            (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
              σ (ExtGabrielArrowIndex.source σ left))))),
      IsSimpleModule A Lleft ∧
        IsSimpleModule A Lright ∧
        Nonempty
          (Lleft ≃ₗ[A] σ.obj (ExtGabrielArrowIndex.target σ left).1) ∧
        Nonempty
          (Lright ≃ₗ[A] σ.obj (ExtGabrielArrowIndex.target σ right).1) ∧
        IsCompl Lleft Lright := by
  classical
  let p :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
      σ (ExtGabrielArrowIndex.source σ left)
  let Rad : Submodule A (σ.obj p) := Module.jacobson A (σ.obj p)
  have hRadSemisimple : IsSemisimpleModule A Rad :=
    forkSource_projectiveRadical_isSemisimple
      K σ hHereditary hThree left right hne hsource
  obtain ⟨Lleft, hLleft, ⟨eLeft⟩⟩ :=
    exists_simpleSubmodule_projectiveRadical_of_extArrow
      K σ left hRadSemisimple
  obtain ⟨Lright, hLright, ⟨eRightRaw⟩⟩ :=
    exists_simpleSubmodule_projectiveRadical_of_extArrow
      K σ
        (⟨ExtGabrielArrowIndex.source σ left,
          ExtGabrielArrowIndex.target σ right,
          hsource.symm ▸ right.2.2⟩ :
            ExtGabrielArrowIndex (K := K) σ)
        hRadSemisimple
  change Submodule A Rad at Lright
  have hRightTarget :
      ExtGabrielArrowIndex.target σ
          (⟨ExtGabrielArrowIndex.source σ left,
            ExtGabrielArrowIndex.target σ right,
            hsource.symm ▸ right.2.2⟩ :
              ExtGabrielArrowIndex (K := K) σ) =
        ExtGabrielArrowIndex.target σ right := by
    apply Subtype.ext
    rfl
  let eRight : Lright ≃ₗ[A]
      σ.obj (ExtGabrielArrowIndex.target σ right).1 :=
    eRightRaw.trans <| FGModuleCat.isoToLinearEquiv <|
      eqToIso <| congrArg (fun s : σ.SimpleIndex => σ.obj s.1) hRightTarget
  have hTargetNe : ExtGabrielArrowIndex.target σ left ≠
      ExtGabrielArrowIndex.target σ right := by
    intro htarget
    apply hne
    apply ExtGabrielArrowIndex.source_target_injective σ
      (OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ)
    exact Prod.ext hsource htarget
  have hSubNe : Lleft ≠ Lright := by
    intro hEq
    subst Lright
    apply hTargetNe
    apply Subtype.ext
    apply σ.eq_of_iso
    exact ⟨(eLeft.symm.trans eRight).toFGModuleCatIso⟩
  have hDisjoint : Disjoint Lleft Lright :=
    (isSimpleModule_iff_isAtom.mp hLleft).disjoint_of_ne
      (isSimpleModule_iff_isAtom.mp hLright) hSubNe
  let f : (Lleft × Lright) →ₗ[A] Rad :=
    Lleft.subtype.coprod Lright.subtype
  have hf : Function.Injective f :=
    submoduleSubtype_coprod_injective_of_disjoint hDisjoint
  have hRadFinite : IsFiniteLength A Rad :=
    (σ.finiteLength p).of_injective Rad.subtype_injective
  have hlengthRad : Module.length A Rad = 2 :=
    forkSource_projectiveRadical_length_eq_two
      K σ hHereditary hThree left right hne hsource
  letI : IsSimpleModule A Lleft := hLleft
  letI : IsSimpleModule A Lright := hLright
  have hlengthSource : Module.length A Rad ≤
      Module.length A (Lleft × Lright) := by
    rw [hlengthRad, Module.length_prod,
      Module.length_eq_one A Lleft,
      Module.length_eq_one A Lright]
    norm_num
  have hsurj : Function.Surjective f :=
    OpConjecture.SerialEndpointReduction.surjective_of_injective_of_length_le
      hRadFinite f hf hlengthSource
  have hRange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hSup : Lleft ⊔ Lright = ⊤ := by
    calc
      Lleft ⊔ Lright =
          LinearMap.range (Lleft.subtype.coprod Lright.subtype) :=
        Submodule.sup_eq_range Lleft Lright
      _ = ⊤ := hRange
  exact ⟨Lleft, Lright, hLleft, hLright, ⟨eLeft⟩, ⟨eRight⟩,
    ⟨hDisjoint, codisjoint_iff.mpr hSup⟩⟩

/-- The source-projective radical has precisely the four submodules
`⊥`, its two target-simple summands, and `⊤`. -/
theorem exists_forkSource_projectiveRadical_four_submodule_classifier
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right) :
    ∃ (Lleft Lright : Submodule A
        (Module.jacobson A
          (σ.obj
            (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
              σ (ExtGabrielArrowIndex.source σ left))))),
      ∀ N, N = ⊥ ∨ N = Lleft ∨ N = Lright ∨ N = ⊤ := by
  classical
  let p :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
      σ (ExtGabrielArrowIndex.source σ left)
  let Rad : Submodule A (σ.obj p) := Module.jacobson A (σ.obj p)
  obtain ⟨Lleft, Lright, hLleft, hLright,
      ⟨eLeft⟩, ⟨eRight⟩, hCompl⟩ :=
    exists_forkSource_projectiveRadical_target_isCompl
      K σ hHereditary hThree left right hne hsource
  letI : IsSimpleModule A Lleft := hLleft
  letI : IsSimpleModule A Lright := hLright
  have hTargetNe : ExtGabrielArrowIndex.target σ left ≠
      ExtGabrielArrowIndex.target σ right := by
    intro htarget
    apply hne
    apply ExtGabrielArrowIndex.source_target_injective σ
      (OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ)
    exact Prod.ext hsource htarget
  have hTypes :=
    forkSource_projectiveRadical_hasTwoTargetConstituents
      K σ hHereditary hThree left right hne hsource
  have hSimpleCases (S : Submodule A Rad)
      (hS : IsSimpleModule A S) : S = Lleft ∨ S = Lright := by
    letI : IsSimpleModule A S := hS
    rcases hTypes S hS with hTypeLeft | hTypeRight
    · obtain ⟨eS⟩ := hTypeLeft
      let projection : Rad →ₗ[A] Lright :=
        Lright.projectionOnto Lleft hCompl.symm
      let g : S →ₗ[A] Lright := projection.comp S.subtype
      rcases g.bijective_or_eq_zero with hbij | hzero
      · exfalso
        apply hTargetNe
        apply Subtype.ext
        apply σ.eq_of_iso
        exact ⟨(eS.symm.trans <|
          (LinearEquiv.ofBijective g hbij).trans eRight).toFGModuleCatIso⟩
      · left
        have hSL : S ≤ Lleft := by
          intro x hx
          apply (Submodule.projectionOnto_apply_eq_zero_iff hCompl.symm).mp
          have hz : g ⟨x, hx⟩ = 0 := by rw [hzero]; rfl
          exact hz
        exact
          ((isSimpleModule_iff_isAtom.mp hLleft).le_iff_eq
            (isSimpleModule_iff_isAtom.mp hS).ne_bot).mp hSL
    · obtain ⟨eS⟩ := hTypeRight
      let projection : Rad →ₗ[A] Lleft :=
        Lleft.projectionOnto Lright hCompl
      let g : S →ₗ[A] Lleft := projection.comp S.subtype
      rcases g.bijective_or_eq_zero with hbij | hzero
      · exfalso
        apply hTargetNe
        apply Subtype.ext
        exact (σ.eq_of_iso ⟨(eS.symm.trans <|
          (LinearEquiv.ofBijective g hbij).trans eLeft).toFGModuleCatIso⟩).symm
      · right
        have hSR : S ≤ Lright := by
          intro x hx
          apply (Submodule.projectionOnto_apply_eq_zero_iff hCompl).mp
          have hz : g ⟨x, hx⟩ = 0 := by rw [hzero]; rfl
          exact hz
        exact
          ((isSimpleModule_iff_isAtom.mp hLright).le_iff_eq
            (isSimpleModule_iff_isAtom.mp hS).ne_bot).mp hSR
  have hLeftQuotSimple : IsSimpleModule A (Rad ⧸ Lleft) :=
    IsSimpleModule.congr (Lleft.quotientEquivOfIsCompl Lright hCompl)
  have hRightQuotSimple : IsSimpleModule A (Rad ⧸ Lright) :=
    IsSimpleModule.congr (Lright.quotientEquivOfIsCompl Lleft hCompl.symm)
  have hLeftCoatom : IsCoatom Lleft :=
    isSimpleModule_iff_isCoatom.mp hLeftQuotSimple
  have hRightCoatom : IsCoatom Lright :=
    isSimpleModule_iff_isCoatom.mp hRightQuotSimple
  refine ⟨Lleft, Lright, ?_⟩
  intro N
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  · letI : IsSemisimpleModule A Rad :=
      forkSource_projectiveRadical_isSemisimple
        K σ hHereditary hThree left right hne hsource
    letI : IsSemisimpleModule A N := inferInstance
    obtain ⟨S, hSN, hSsimple⟩ :=
      (IsSemisimpleModule.eq_bot_or_exists_simple_le N).resolve_left hNbot
    rcases hSimpleCases S hSsimple with rfl | rfl
    · rcases hLeftCoatom.le_iff.mp hSN with htop | heq
      · exact Or.inr (Or.inr (Or.inr htop))
      · exact Or.inr (Or.inl heq)
    · rcases hRightCoatom.le_iff.mp hSN with htop | heq
      · exact Or.inr (Or.inr (Or.inr htop))
      · exact Or.inr (Or.inr (Or.inl heq))

/-- Numerical form of the four-submodule classification. -/
theorem forkSource_projectiveRadical_submodule_natCard_le_four
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right) :
    Nat.card
        (Submodule A
          (Module.jacobson A
            (σ.obj
              (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
                σ (ExtGabrielArrowIndex.source σ left))))) ≤ 4 := by
  classical
  let p :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
      σ (ExtGabrielArrowIndex.source σ left)
  let Rad : Submodule A (σ.obj p) := Module.jacobson A (σ.obj p)
  obtain ⟨Lleft, Lright, hclass⟩ :=
    exists_forkSource_projectiveRadical_four_submodule_classifier
      K σ hHereditary hThree left right hne hsource
  let candidates : Set (Submodule A Rad) := {⊥, Lleft, Lright, ⊤}
  have hcandidatesFinite : candidates.Finite := by
    simp only [candidates]
    exact Set.Finite.insert _
      (Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _)))
  letI : Fintype candidates := hcandidatesFinite.fintype
  let code (N : Submodule A Rad) : candidates :=
    ⟨N, by
      rcases hclass N with hN | hN | hN | hN
      · simp [candidates, hN]
      · simp [candidates, hN]
      · simp [candidates, hN]
      · simp [candidates, hN]⟩
  have hcode : Function.Injective code := by
    intro N P hNP
    exact congrArg Subtype.val hNP
  letI : Finite (Submodule A Rad) := Finite.of_injective code hcode
  have hcard : Nat.card (Submodule A Rad) ≤ Nat.card candidates :=
    Nat.card_le_card_of_injective code hcode
  have hcandidatesCard : candidates.ncard ≤ 4 := by
    have h₁ := Set.ncard_insert_le (⊥ : Submodule A Rad)
      ({Lleft, Lright, ⊤} : Set (Submodule A Rad))
    have h₂ := Set.ncard_insert_le Lleft
      ({Lright, ⊤} : Set (Submodule A Rad))
    have h₃ := Set.ncard_insert_le Lright
      ({⊤} : Set (Submodule A Rad))
    simp only [Set.ncard_singleton] at h₃
    change candidates.ncard ≤ 4
    simp only [candidates]
    omega
  change Nat.card (Submodule A Rad) ≤ 4
  exact hcard.trans <| by
    rw [Nat.card_coe_set_eq]
    exact hcandidatesCard

/-- Apart from the two target-simple labels, every indecomposable in the
three-simple fork is an epimorphic image of the fork-source projective. -/
theorem exists_epi_forkSourceProjective_of_ne_targets
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right)
    (j : ι)
    (hjLeft : j ≠ (ExtGabrielArrowIndex.target σ left).1)
    (hjRight : j ≠ (ExtGabrielArrowIndex.target σ right).1) :
    ∃ f :
        σ.obj
            (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
              σ (ExtGabrielArrowIndex.source σ left)) ⟶
          σ.obj j,
      Epi f := by
  classical
  have hTop : IsSimpleModule A (σ.moduleTop j) :=
    moduleTop_isSimple_of_threeSimpleFork
      K σ hHereditary hThree left right hne hsource j
  by_cases hjSimple : Simple (σ.obj j)
  · let jSimple : σ.SimpleIndex := ⟨j, hjSimple⟩
    rcases simpleIndex_eq_source_or_targets_of_threeSimpleFork
      K σ hHereditary hThree left right hne hsource jSimple with
      hjSource | hjTargetLeft | hjTargetRight
    · have hjSourceVal :
          j = (ExtGabrielArrowIndex.source σ left).1 :=
        congrArg Subtype.val hjSource
      letI : IsSimpleModule A (σ.obj j) :=
        (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
          _).mp hjSimple
      let eSimpleTop : FGModuleCat.of A (σ.moduleTop j) ≅ σ.obj j :=
        (Submodule.quotEquivOfEqBot
          (Module.jacobson A (σ.obj j))
          (IsSimpleModule.jacobson_eq_bot A (σ.obj j))).toFGModuleCatIso
      let eTop : FGModuleCat.of A (σ.moduleTop j) ≅
          σ.obj (ExtGabrielArrowIndex.source σ left).1 :=
        eSimpleTop ≪≫
          eqToIso (congrArg σ.obj hjSourceVal)
      exact
        OpConjecture.ExtDegreeNakayamaReduction.exists_epi_projectiveLabelOfSimple_of_simpleTop
          σ j hTop (ExtGabrielArrowIndex.source σ left) eTop
    · exact False.elim <| hjLeft (congrArg Subtype.val hjTargetLeft)
    · exact False.elim <| hjRight (congrArg Subtype.val hjTargetRight)
  · let Q : σ.SimpleQuotient j :=
      Classical.choice (σ.exists_simpleQuotient j)
    letI : Epi Q.map := Q.epi
    have hQSurj : Function.Surjective Q.map.hom.hom :=
      (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective Q.map).mp
        inferInstance
    have hQSimple : IsSimpleModule A (σ.obj Q.index) :=
      (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
        _).mp Q.simple
    have hQSource :
        Q.index = (ExtGabrielArrowIndex.source σ left).1 :=
      simpleQuotient_index_eq_source_of_not_simple_threeSimpleFork
        K σ hHereditary hThree left right hne hsource j hjSimple Q
    let eTopRaw : σ.moduleTop j ≃ₗ[A] σ.obj Q.index :=
      OpConjecture.FamilyFourControl.moduleTopLinearEquivOfSurjectiveToSimple
        hTop hQSimple Q.map.hom.hom hQSurj
    let eTop : FGModuleCat.of A (σ.moduleTop j) ≅
        σ.obj (ExtGabrielArrowIndex.source σ left).1 :=
      eTopRaw.toFGModuleCatIso ≪≫
        eqToIso (congrArg σ.obj hQSource)
    exact
      OpConjecture.ExtDegreeNakayamaReduction.exists_epi_projectiveLabelOfSimple_of_simpleTop
        σ j hTop (ExtGabrielArrowIndex.source σ left) eTop

/-- Finiteness form of the four-submodule classification, used when the
source-projective quotients are counted by their kernels. -/
theorem forkSource_projectiveRadical_submodule_finite
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right) :
    Finite
      (Submodule A
        (Module.jacobson A
          (σ.obj
            (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
              σ (ExtGabrielArrowIndex.source σ left))))) := by
  classical
  let p :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
      σ (ExtGabrielArrowIndex.source σ left)
  let Rad : Submodule A (σ.obj p) := Module.jacobson A (σ.obj p)
  obtain ⟨Lleft, Lright, hclass⟩ :=
    exists_forkSource_projectiveRadical_four_submodule_classifier
      K σ hHereditary hThree left right hne hsource
  let candidates : Set (Submodule A Rad) := {⊥, Lleft, Lright, ⊤}
  have hcandidatesFinite : candidates.Finite := by
    simp only [candidates]
    exact Set.Finite.insert _
      (Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _)))
  letI : Fintype candidates := hcandidatesFinite.fintype
  let code (N : Submodule A Rad) : candidates :=
    ⟨N, by
      rcases hclass N with hN | hN | hN | hN
      · simp [candidates, hN]
      · simp [candidates, hN]
      · simp [candidates, hN]
      · simp [candidates, hN]⟩
  exact Finite.of_injective code fun _ _ h => congrArg Subtype.val h

/-- A hereditary three-simple source fork has at most six indecomposable
module labels: the two target simples and at most four quotients of the
source projective. -/
theorem indecomposable_natCard_le_six_of_threeSimpleFork
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right) :
    Nat.card ι ≤ 6 := by
  classical
  let t : ι := (ExtGabrielArrowIndex.target σ left).1
  let r : ι := (ExtGabrielArrowIndex.target σ right).1
  let p : ι :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveLabelOfSimple
      σ (ExtGabrielArrowIndex.source σ left)
  let Rad : Submodule A (σ.obj p) := Module.jacobson A (σ.obj p)
  have htr : t ≠ r := by
    intro htargets
    apply hne
    apply ExtGabrielArrowIndex.source_target_injective σ
      (OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ)
    apply Prod.ext hsource
    apply Subtype.ext
    exact htargets
  let sourceMap :
      ∀ (j : ι), j ≠ t → j ≠ r → (σ.obj p ⟶ σ.obj j) :=
    fun j hjt hjr =>
      Classical.choose
        (exists_epi_forkSourceProjective_of_ne_targets
          K σ hHereditary hThree left right hne hsource j hjt hjr)
  have sourceMap_epi (j : ι) (hjt : j ≠ t) (hjr : j ≠ r) :
      Epi (sourceMap j hjt hjr) := by
    dsimp only [sourceMap]
    exact Classical.choose_spec
      (exists_epi_forkSourceProjective_of_ne_targets
        K σ hHereditary hThree left right hne hsource j hjt hjr)
  let code (j : ι) : Fin 2 ⊕ Submodule A Rad :=
    if hjt : j = t then Sum.inl 0
    else if hjr : j = r then Sum.inl 1
    else
      Sum.inr
        ((LinearMap.ker (sourceMap j hjt hjr).hom.hom).comap Rad.subtype)
  have hcode : Function.Injective code := by
    intro j k hjk
    by_cases hjt : j = t
    · by_cases hkt : k = t
      · exact hjt.trans hkt.symm
      · by_cases hkr : k = r
        · simp [code, hjt, hkr, htr.symm] at hjk
        · simp [code, hjt, hkt, hkr] at hjk
    · by_cases hjr : j = r
      · by_cases hkt : k = t
        · simp [code, hjr, hkt, htr.symm] at hjk
        · by_cases hkr : k = r
          · exact hjr.trans hkr.symm
          · simp [code, hjr, hkt, hkr, htr.symm] at hjk
      · by_cases hkt : k = t
        · simp [code, hjt, hjr, hkt] at hjk
        · by_cases hkr : k = r
          · simp [code, hjt, hjr, hkr, htr.symm] at hjk
          · let f : σ.obj p ⟶ σ.obj j := sourceMap j hjt hjr
            let g : σ.obj p ⟶ σ.obj k := sourceMap k hkt hkr
            have hfEpi : Epi f := sourceMap_epi j hjt hjr
            have hgEpi : Epi g := sourceMap_epi k hkt hkr
            letI : Epi f := hfEpi
            letI : Epi g := hgEpi
            have hcomap :
                (LinearMap.ker f.hom.hom).comap Rad.subtype =
                  (LinearMap.ker g.hom.hom).comap Rad.subtype := by
              simpa [code, hjt, hjr, hkt, hkr, f, g] using hjk
            have hfSurj : Function.Surjective f.hom.hom :=
              (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective f).mp
                inferInstance
            have hgSurj : Function.Surjective g.hom.hom :=
              (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective g).mp
                inferInstance
            have hTopP : IsSimpleModule A (σ.moduleTop p) :=
              moduleTop_isSimple_of_threeSimpleFork
                K σ hHereditary hThree left right hne hsource p
            have hfKerNeTop : LinearMap.ker f.hom.hom ≠ ⊤ := by
              intro htop
              have hfzero : f.hom.hom = 0 :=
                LinearMap.ker_eq_top.mp htop
              letI : Nontrivial (σ.obj j) := (σ.indecomposable j).nontrivial
              obtain ⟨y, hy⟩ := exists_ne (0 : σ.obj j)
              obtain ⟨x, hx⟩ := hfSurj y
              rw [hfzero] at hx
              exact hy hx.symm
            have hgKerNeTop : LinearMap.ker g.hom.hom ≠ ⊤ := by
              intro htop
              have hgzero : g.hom.hom = 0 :=
                LinearMap.ker_eq_top.mp htop
              letI : Nontrivial (σ.obj k) := (σ.indecomposable k).nontrivial
              obtain ⟨y, hy⟩ := exists_ne (0 : σ.obj k)
              obtain ⟨x, hx⟩ := hgSurj y
              rw [hgzero] at hx
              exact hy hx.symm
            have hfKerLe :
                LinearMap.ker f.hom.hom ≤ Module.jacobson A (σ.obj p) :=
              OpConjecture.FamilyFourControl.le_jacobson_of_ne_top_of_simple_top
                hTopP hfKerNeTop
            have hgKerLe :
                LinearMap.ker g.hom.hom ≤ Module.jacobson A (σ.obj p) :=
              OpConjecture.FamilyFourControl.le_jacobson_of_ne_top_of_simple_top
                hTopP hgKerNeTop
            have hker :
                LinearMap.ker f.hom.hom = LinearMap.ker g.hom.hom := by
              calc
                LinearMap.ker f.hom.hom =
                    ((LinearMap.ker f.hom.hom).comap Rad.subtype).map
                      Rad.subtype := by
                  symm
                  rw [Submodule.map_comap_subtype,
                    inf_eq_right.mpr hfKerLe]
                _ = ((LinearMap.ker g.hom.hom).comap Rad.subtype).map
                      Rad.subtype :=
                  congrArg (fun N => N.map Rad.subtype) hcomap
                _ = LinearMap.ker g.hom.hom := by
                  rw [Submodule.map_comap_subtype,
                    inf_eq_right.mpr hgKerLe]
            let e : σ.obj j ≃ₗ[A] σ.obj k :=
              (f.hom.hom.quotKerEquivOfSurjective hfSurj).symm.trans
                ((Submodule.quotEquivOfEq
                  (LinearMap.ker f.hom.hom)
                  (LinearMap.ker g.hom.hom) hker).trans
                    (g.hom.hom.quotKerEquivOfSurjective hgSurj))
            exact σ.eq_of_iso ⟨e.toFGModuleCatIso⟩
  letI : Finite (Submodule A Rad) :=
    forkSource_projectiveRadical_submodule_finite
      K σ hHereditary hThree left right hne hsource
  letI : Finite (Fin 2 ⊕ Submodule A Rad) := inferInstance
  have hcard : Nat.card ι ≤ Nat.card (Fin 2 ⊕ Submodule A Rad) :=
    Nat.card_le_card_of_injective code hcode
  have hradCard : Nat.card (Submodule A Rad) ≤ 4 :=
    forkSource_projectiveRadical_submodule_natCard_le_four
      K σ hHereditary hThree left right hne hsource
  rw [Nat.card_sum, Nat.card_fin] at hcard
  omega

omit [IsAlgClosed K] in
/-- For a finite-dimensional algebra with at most six indecomposable
labels, the fourth quotient- and submodule-closure levels agree.  This is
purely the already-established top/co-top combinatorics. -/
theorem levelCount_four_eq_of_indec_natCard_le_six
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hcard : Nat.card ι ≤ 6) :
    σ.qClosure.levelCount 4 = σ.sClosure.levelCount 4 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  by_cases hlt : Nat.card ι < 4
  · rw [OpConjecture.SetClosure.levelCount_eq_zero_of_card_lt
        σ.qClosure hlt,
      OpConjecture.SetClosure.levelCount_eq_zero_of_card_lt
        σ.sClosure hlt]
  · have hcases :
        Nat.card ι = 4 ∨ Nat.card ι = 5 ∨ Nat.card ι = 6 := by
      omega
    rcases hcases with hfour | hfive | hsix
    · calc
        σ.qClosure.levelCount 4 =
            σ.qClosure.levelCount (Nat.card ι) := by rw [hfour]
        _ = 1 := OpConjecture.SetClosure.levelCount_card_eq_one _
        _ = σ.sClosure.levelCount (Nat.card ι) :=
          (OpConjecture.SetClosure.levelCount_card_eq_one _).symm
        _ = σ.sClosure.levelCount 4 := by rw [hfour]
    · have hone : 1 ≤ Nat.card ι := by omega
      have hfive' : Fintype.card ι = 5 := by
        simpa only [Nat.card_eq_fintype_card] using hfive
      simpa [hfive'] using
        (σ.finiteDimensional_colevelOne_formula (K := K) hone).1
    · have htwo : 2 ≤ Nat.card ι := by omega
      have hsix' : Fintype.card ι = 6 := by
        simpa only [Nat.card_eq_fintype_card] using hsix
      have hcolevelTwo :
          σ.qClosure.levelCount (Nat.card ι - 2) =
            σ.sClosure.levelCount (Nat.card ι - 2) := by
        rw [← σ.qCofiniteTwoCount_eq_levelCount_card_sub_two htwo,
          ← σ.sCofiniteTwoCount_eq_levelCount_card_sub_two htwo]
        exact
          σ.finiteDimensional_qCofiniteTwoCount_eq_sCofiniteTwoCount
            (K := K)
      simpa [hsix'] using hcolevelTwo

/-- The fourth-level equality in the exact hereditary three-simple fork is
therefore unconditional. -/
theorem levelCount_four_eq_of_threeSimpleFork
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3)
    (left right : ExtGabrielArrowIndex (K := K) σ)
    (hne : left ≠ right)
    (hsource : ExtGabrielArrowIndex.source σ left =
      ExtGabrielArrowIndex.source σ right) :
    σ.qClosure.levelCount 4 = σ.sClosure.levelCount 4 :=
  levelCount_four_eq_of_indec_natCard_le_six K σ
    (indecomposable_natCard_le_six_of_threeSimpleFork
      K σ hHereditary hThree left right hne hsource)

/-! ## Finite heredity on the opposite algebra -/

/-- The unbundled finite-left-heredity predicate implies its categorical
mono-to-projective form in `FGModuleCat`. -/
theorem fgProjective_of_mono_to_fgProjective_of_finitelyGeneratedLeftHereditary
    {A : Type u} [Ring A] [IsNoetherianRing A]
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    {X P : FGModuleCat.{u} A}
    (f : X ⟶ P) (hf : Mono f) (hP : CategoryTheory.Projective P) :
    CategoryTheory.Projective X := by
  letI : Mono f := hf
  have hfinjective : Function.Injective f.hom.hom :=
    (OpConjecture.IndecomposableSkeleton.fg_mono_iff_injective f).mp
      inferInstance
  let Range : Submodule A P := LinearMap.range f.hom.hom
  have hRangeProjective : Module.Projective A Range :=
    hHereditary P hP Range
  let e : X ≃ₗ[A] Range :=
    LinearEquiv.ofBijective f.hom.hom.rangeRestrict
      ⟨f.hom.hom.injective_rangeRestrict_iff.mpr hfinjective,
        LinearMap.surjective_rangeRestrict f.hom.hom⟩
  have hXProjective : Module.Projective A X := by
    letI : Module.Projective A Range := hRangeProjective
    exact Module.Projective.of_equiv' e.symm
  exact OpConjecture.RingelStable.fgProjective_of_moduleProjective
    X hXProjective

/-- Every finitely generated module over a finite-left-hereditary
Noetherian ring has projective dimension at most one. -/
theorem hasProjectiveDimensionLT_two_of_finitelyGeneratedLeftHereditary
    {A : Type u} [Ring A] [IsNoetherianRing A]
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (X : FGModuleCat.{u} A) :
    HasProjectiveDimensionLT X 2 := by
  let f : CategoryTheory.Projective.over X ⟶ X :=
    CategoryTheory.Projective.π X
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_kernel f }
  have hKernelProjective : CategoryTheory.Projective (kernel f) :=
    fgProjective_of_mono_to_fgProjective_of_finitelyGeneratedLeftHereditary
      hHereditary (kernel.ι f) inferInstance inferInstance
  letI : CategoryTheory.Projective (kernel f) := hKernelProjective
  exact
    (hS.hasProjectiveDimensionLT_X₃_iff 0
      (inferInstance : CategoryTheory.Projective
        (CategoryTheory.Projective.over X))).2 inferInstance

/-- Equivalently, every finitely generated module has injective dimension
at most one. -/
theorem hasInjectiveDimensionLT_two_of_finitelyGeneratedLeftHereditary
    {A : Type u} [Ring A] [IsNoetherianRing A]
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (Y : FGModuleCat.{u} A) :
    HasInjectiveDimensionLT Y 2 := by
  letI : HasExt.{u} (FGModuleCat.{u} A) :=
    hasExt_of_enoughProjectives.{u} (FGModuleCat.{u} A)
  apply hasInjectiveDimensionLT_of_enoughProjectives Y 2
  intro X
  letI : HasProjectiveDimensionLT X 2 :=
    hasProjectiveDimensionLT_two_of_finitelyGeneratedLeftHereditary
      hHereditary X
  exact HasProjectiveDimensionLT.subsingleton X 2 2 le_rfl Y

/-- Hence an epimorphic image of a finitely generated injective remains
injective over a finite-left-hereditary ring. -/
theorem fgInjective_of_epi_from_fgInjective_of_finitelyGeneratedLeftHereditary
    {A : Type u} [Ring A] [IsNoetherianRing A]
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    {I Q : FGModuleCat.{u} A}
    (f : I ⟶ Q) (hf : Epi f) (hI : CategoryTheory.Injective I) :
    CategoryTheory.Injective Q := by
  letI : Epi f := hf
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_kernel f }
  have hKernelDimension : HasInjectiveDimensionLT (kernel f) 2 :=
    hasInjectiveDimensionLT_two_of_finitelyGeneratedLeftHereditary
      hHereditary (kernel f)
  letI : HasInjectiveDimensionLT (kernel f) 2 := hKernelDimension
  have hQDimension : HasInjectiveDimensionLT Q 1 :=
    (hS.hasInjectiveDimensionLT_X₃_iff 0 hI).2 inferInstance
  exact injective_iff_hasInjectiveDimensionLT_one.mpr hQDimension

omit [IsAlgClosed K] in
/-- Finite left heredity is therefore preserved by passage to the opposite
of a finite-dimensional algebra. -/
theorem finitelyGeneratedLeftHereditary_op
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A) :
    OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
      Aᵐᵒᵖ := by
  intro P hP T
  let X : FGModuleCat.{u} Aᵐᵒᵖ := FGModuleCat.of Aᵐᵒᵖ T
  let inclusion : X ⟶ P := FGModuleCat.ofHom T.subtype
  have hInclusionMono : Mono inclusion :=
    (OpConjecture.IndecomposableSkeleton.fg_mono_iff_injective inclusion).mpr
      T.subtype_injective
  let E := OpConjecture.Contragredient.reverseDualityEquivalence K A
  let dualMap :
      E.functor.obj (Opposite.op P) ⟶
        E.functor.obj (Opposite.op X) :=
    E.functor.map inclusion.op
  have hDualMapEpi : Epi dualMap := by
    letI : Mono inclusion := hInclusionMono
    dsimp only [dualMap]
    infer_instance
  have hDualPInjective :
      CategoryTheory.Injective (E.functor.obj (Opposite.op P)) := by
    apply (E.map_injective_iff (Opposite.op P)).2
    exact
      (CategoryTheory.Injective.projective_iff_injective_op).1 hP
  have hDualXInjective :
      CategoryTheory.Injective (E.functor.obj (Opposite.op X)) :=
    fgInjective_of_epi_from_fgInjective_of_finitelyGeneratedLeftHereditary
      hHereditary dualMap hDualMapEpi hDualPInjective
  have hXopInjective : CategoryTheory.Injective (Opposite.op X) :=
    (E.map_injective_iff (Opposite.op X)).1 hDualXInjective
  have hXProjective : CategoryTheory.Projective X :=
    (CategoryTheory.Injective.projective_iff_injective_op).2 hXopInjective
  exact OpConjecture.RingelStable.moduleProjective_of_fgProjective
    X hXProjective

/-- Every finite-left-hereditary skeleton with exactly three simple labels
has unconditional fourth-level equality.  If both Ext endpoint maps are
injective, the skeleton is Nakayama.  Otherwise one orientation is the
source fork proved above; the opposite-fork case is transported through
contragredient duality and opposite finite heredity. -/
theorem levelCount_four_eq_of_threeSimples_of_finitelyGeneratedLeftHereditary
    {A : Type u}
    [Ring A] [Small.{u} A] [Algebra K A]
    [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {ι : Type (u + 1)} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, u + 1, u} A ι)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        A)
    (hThree : Nat.card σ.SimpleIndex = 3) :
    σ.qClosure.levelCount 4 = σ.sClosure.levelCount 4 := by
  classical
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  letI : IsArtinianRing Aᵐᵒᵖ :=
    OpConjecture.isArtinianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Aᵐᵒᵖᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  let hNoParallel : NoParallelExtSupport (K := K) σ :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport σ
  by_cases hSource : Function.Injective
      (ExtGabrielArrowIndex.source (K := K) σ)
  · by_cases hTarget : Function.Injective
        (ExtGabrielArrowIndex.target (K := K) σ)
    · have hProfile : FullProfileEquality K
          { Carrier := A
            ring := inferInstance
            algebra := inferInstance
            finiteDimensional := inferInstance
            Index := ι
            finiteIndex := inferInstance
            skeleton := σ } :=
        fullProfileEquality_of_extSourceTarget_injective K
          { Carrier := A
            ring := inferInstance
            algebra := inferInstance
            finiteDimensional := inferInstance
            Index := ι
            finiteIndex := inferInstance
            skeleton := σ }
          hSource hTarget
      rw [← OpConjecture.SetClosure.levelPolynomial_coeff,
        hProfile, OpConjecture.SetClosure.levelPolynomial_coeff]
    · let τ :=
        OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A
      let D :=
        OpConjecture.Contragredient.alignedBiduality K A σ τ
      letI : Finite
          (OpConjecture.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
        D.forward.labelEquiv.finite_iff.mp inferInstance
      let hNoParallelTau : NoParallelExtSupport (K := K) τ :=
        OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport τ
      have hThreeTau : Nat.card τ.SimpleIndex = 3 := by
        calc
          Nat.card τ.SimpleIndex = Nat.card σ.SimpleIndex :=
            Nat.card_congr
              (OpConjecture.ExtDualTransport.AlignedAntiEquivalence.simpleIndexEquiv
                σ τ D.forward).symm
          _ = 3 := hThree
      have hTauNotSource : ¬ Function.Injective
          (ExtGabrielArrowIndex.source (K := K) τ) := by
        intro hTauSource
        apply hTarget
        exact
          OpConjecture.ExtDualTransport.AlignedAntiEquivalence.extTarget_injective_of_dualExtSource_injective
            σ τ D.forward hNoParallel hNoParallelTau hTauSource
      simp only [Function.Injective] at hTauNotSource
      push Not at hTauNotSource
      obtain ⟨left, right, hTauSource, hne⟩ := hTauNotSource
      have hHereditaryOp :
          OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
            Aᵐᵒᵖ :=
        finitelyGeneratedLeftHereditary_op K hHereditary
      have hTauLevel :
          τ.qClosure.levelCount 4 = τ.sClosure.levelCount 4 :=
        levelCount_four_eq_of_threeSimpleFork
          K τ hHereditaryOp hThreeTau left right hne hTauSource
      have hQToS :
          σ.qClosure.levelPolynomial = τ.sClosure.levelPolynomial :=
        OpConjecture.IndecomposableSkeleton.AlignedBiduality.quotientToSubmoduleLevelPolynomial_eq
          σ τ D
      have hSToQ :
          σ.sClosure.levelPolynomial = τ.qClosure.levelPolynomial :=
        OpConjecture.IndecomposableSkeleton.AlignedBiduality.submoduleToQuotientLevelPolynomial_eq
          σ τ D
      have hQLevel :
          σ.qClosure.levelCount 4 = τ.sClosure.levelCount 4 := by
        rw [← OpConjecture.SetClosure.levelPolynomial_coeff,
          hQToS, OpConjecture.SetClosure.levelPolynomial_coeff]
      have hSLevel :
          σ.sClosure.levelCount 4 = τ.qClosure.levelCount 4 := by
        rw [← OpConjecture.SetClosure.levelPolynomial_coeff,
          hSToQ, OpConjecture.SetClosure.levelPolynomial_coeff]
      exact hQLevel.trans (hTauLevel.symm.trans hSLevel.symm)
  · simp only [Function.Injective] at hSource
    push Not at hSource
    obtain ⟨left, right, hForkSource, hne⟩ := hSource
    exact levelCount_four_eq_of_threeSimpleFork
      K σ hHereditary hThree left right hne hForkSource

/-! ## Unconditional connected small-core endpoint -/

/-- The exact connected small-core input used by the degree-three/four
recurrence is now a theorem. -/
theorem connectedSmallCore_three_four_unconditional
    (B : AlgebraNode K) (n : ℕ) (hn : n = 3 ∨ n = 4)
    (hConnected :
      OpConjecture.BlockDecomposition.Node.IsBlockConnected K B)
    (hsmall : coreSize K B < n) :
    (AlgebraNode.faithfulQCount K B n =
        AlgebraNode.faithfulSCount K B n) ∨
      (AlgebraNode.qClosure K B).levelCount n =
        (AlgebraNode.sClosure K B).levelCount n := by
  rcases hn with rfl | rfl
  · exact Or.inr
      (OpConjecture.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.levelCount_three_eq
        K B)
  · rcases subsingleton_or_nontrivial B.Carrier with hzero | hnonzero
    · letI : Subsingleton B.Carrier := hzero
      exact Or.inr
        (AlgebraNode.levelCount_eq_of_subsingleton K B 4 (by omega))
    · letI : Nontrivial B.Carrier := hnonzero
      have hPositive : 0 < projectiveCount K B :=
        AlgebraNode.projectiveCount_pos K B
      have hBound : projectiveCount K B ≤ coreSize K B :=
        projectiveCount_le_coreSize K B
      by_cases hOne : projectiveCount K B = 1
      · exact Or.inr
          (levelCount_eq_of_projectiveCount_eq_one_of_coreSize_lt
            K B hOne hsmall)
      by_cases hTwo : projectiveCount K B = 2
      · by_cases hCoreThree : coreSize K B = 3
        · exact
            OpConjecture.BottomLevels.FiniteDimensionalRecurrence.twoSimpleCoreThree_four
              B hConnected hTwo hCoreThree
        · have hCoreTwo : coreSize K B = 2 := by omega
          have hEqual : projectiveCount K B = coreSize K B := by omega
          have hTwoSimple : Nat.card B.skeleton.SimpleIndex = 2 :=
            (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ncard_projectiveLabels_eq_natCard_simpleIndex
              B.skeleton).symm.trans hTwo
          have hIndexCard : Nat.card B.Index ≤ 3 :=
            OpConjecture.HereditaryTwoSimpleBoundary.AlgebraNode.indexCard_le_three_of_twoSimples_of_projectiveCount_eq_coreSize
              K B hTwoSimple hEqual
          exact Or.inr
            (levelCount_four_eq_of_indec_natCard_le_six
              K B.skeleton (by omega))
      · have hThreeProjective : projectiveCount K B = 3 := by omega
        have hCoreThree : coreSize K B = 3 := by omega
        have hEqual : projectiveCount K B = coreSize K B := by omega
        have hThreeSimple : Nat.card B.skeleton.SimpleIndex = 3 :=
          (OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ncard_projectiveLabels_eq_natCard_simpleIndex
            B.skeleton).symm.trans hThreeProjective
        have hHereditary :
            OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
              B.Carrier :=
          finitelyGeneratedLeftHereditary_of_projectiveCount_eq_coreSize
            K B hEqual
        exact Or.inr
          (levelCount_four_eq_of_threeSimples_of_finitelyGeneratedLeftHereditary
            K B.skeleton hHereditary hThreeSimple)

/-- Consequently, levels three and four agree for every finite-dimensional
algebra node without a project-local classification hypothesis. -/
theorem levelCount_three_and_four_eq_unconditional
    (B : AlgebraNode K) :
    (AlgebraNode.qClosure K B).levelCount 3 =
        (AlgebraNode.sClosure K B).levelCount 3 ∧
      (AlgebraNode.qClosure K B).levelCount 4 =
        (AlgebraNode.sClosure K B).levelCount 4 :=
  levelCount_three_and_four_eq_of_smallCore K
    (connectedSmallCore_three_four_unconditional K) B

end OpConjecture.HereditaryThreeSimpleUnconditional
