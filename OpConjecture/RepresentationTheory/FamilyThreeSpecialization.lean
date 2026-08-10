import OpConjecture.RepresentationTheory.LevelThreeNonUniserialShapes
import OpConjecture.RepresentationTheory.TwoTargetExtBridge

/-!
# Family-three radical specialization

Module-theoretic reductions for the family consisting of two length-two
indecomposables with a common simple top.
-/

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

/-- Every simple submodule of `M` has one of the two indicated isomorphism
types. -/
def HasSimpleConstituentsOfEitherType
    (M S T : Type x)
    [AddCommGroup M] [Module Aᵐᵒᵖ M]
    [AddCommGroup S] [Module Aᵐᵒᵖ S]
    [AddCommGroup T] [Module Aᵐᵒᵖ T] : Prop :=
  ∀ L : Submodule Aᵐᵒᵖ M, IsSimpleModule Aᵐᵒᵖ L →
    Nonempty (L ≃ₗ[Aᵐᵒᵖ] S) ∨ Nonempty (L ≃ₗ[Aᵐᵒᵖ] T)

theorem HasSimpleConstituentsOfEitherType.of_subsingleton
    {M S T : Type x}
    [AddCommGroup M] [Module Aᵐᵒᵖ M]
    [AddCommGroup S] [Module Aᵐᵒᵖ S]
    [AddCommGroup T] [Module Aᵐᵒᵖ T]
    [Subsingleton M] :
    HasSimpleConstituentsOfEitherType (A := A) M S T := by
  intro L hL
  letI : IsSimpleModule Aᵐᵒᵖ L := hL
  letI : Nontrivial L := IsSimpleModule.nontrivial Aᵐᵒᵖ L
  obtain ⟨z, hz⟩ := exists_ne (0 : L)
  exact False.elim (hz (Subsingleton.elim z 0))

theorem HasSimpleConstituentsOfEitherType.of_simple_left
    {M S T : Type x}
    [AddCommGroup M] [Module Aᵐᵒᵖ M]
    [AddCommGroup S] [Module Aᵐᵒᵖ S]
    [AddCommGroup T] [Module Aᵐᵒᵖ T]
    [IsSimpleModule Aᵐᵒᵖ M]
    (e : M ≃ₗ[Aᵐᵒᵖ] S) :
    HasSimpleConstituentsOfEitherType (A := A) M S T := by
  intro L hL
  letI : IsSimpleModule Aᵐᵒᵖ L := hL
  exact Or.inl ⟨
    ((IsIsotypicOfType.of_isSimpleModule Aᵐᵒᵖ M) L).some.trans e⟩

theorem HasSimpleConstituentsOfEitherType.of_simple_right
    {M S T : Type x}
    [AddCommGroup M] [Module Aᵐᵒᵖ M]
    [AddCommGroup S] [Module Aᵐᵒᵖ S]
    [AddCommGroup T] [Module Aᵐᵒᵖ T]
    [IsSimpleModule Aᵐᵒᵖ M]
    (e : M ≃ₗ[Aᵐᵒᵖ] T) :
    HasSimpleConstituentsOfEitherType (A := A) M S T := by
  intro L hL
  letI : IsSimpleModule Aᵐᵒᵖ L := hL
  exact Or.inr ⟨
    ((IsIsotypicOfType.of_isSimpleModule Aᵐᵒᵖ M) L).some.trans e⟩

theorem hasSimpleConstituentsOfEitherType_pi
    {J : Type} [Finite J]
    {M : J → Type x}
    [∀ t, AddCommGroup (M t)] [∀ t, Module Aᵐᵒᵖ (M t)]
    {S T : Type x}
    [AddCommGroup S] [Module Aᵐᵒᵖ S]
    [AddCommGroup T] [Module Aᵐᵒᵖ T]
    (hcomponent : ∀ t,
      HasSimpleConstituentsOfEitherType (A := A) (M t) S T) :
    HasSimpleConstituentsOfEitherType (A := A) (∀ t, M t) S T := by
  intro L hL
  letI : IsSimpleModule Aᵐᵒᵖ L := hL
  letI : Nontrivial L := IsSimpleModule.nontrivial Aᵐᵒᵖ L
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
  let f : L →ₗ[Aᵐᵒᵖ] M t :=
    (LinearMap.proj t).comp L.subtype
  have hf : f ≠ 0 := by
    intro hzero
    have hzmap : f z = 0 := by rw [hzero]; rfl
    exact hzt hzmap
  have hfinj : Function.Injective f := by
    rcases f.injective_or_eq_zero with hinj | hzero
    · exact hinj
    · exact (hf hzero).elim
  let e : L ≃ₗ[Aᵐᵒᵖ] LinearMap.range f :=
    LinearEquiv.ofInjective f hfinj
  have hrangeSimple :
      IsSimpleModule Aᵐᵒᵖ (LinearMap.range f) :=
    IsSimpleModule.congr e.symm
  rcases hcomponent t (LinearMap.range f) hrangeSimple with hS | hT
  · exact Or.inl ⟨e.trans hS.some⟩
  · exact Or.inr ⟨e.trans hT.some⟩

theorem moduleRadical_sumOver_hasSimpleConstituentsOfEitherType
    (J : FintypeCat.{0}) (a : J → ι)
    {S T : Type x}
    [AddCommGroup S] [Module Aᵐᵒᵖ S]
    [AddCommGroup T] [Module Aᵐᵒᵖ T]
    (hcomponent : ∀ t : J,
      HasSimpleConstituentsOfEitherType (A := A)
        (Module.jacobson Aᵐᵒᵖ (σ.obj (a t))) S T) :
    HasSimpleConstituentsOfEitherType (A := A)
      (Module.jacobson Aᵐᵒᵖ (σ.sumOver J a)) S T := by
  letI : Fintype J := FintypeCat.fintype
  let e :
      σ.sumOver J a ≅
        FGModuleCat.of Aᵐᵒᵖ (∀ t : J, σ.obj (a t)) :=
    OpConjecture.IndecomposableSkeleton.biproductIsoPiFG _
  let sourceRadical :
      Submodule Aᵐᵒᵖ (σ.sumOver J a) :=
    Module.jacobson Aᵐᵒᵖ (σ.sumOver J a)
  let componentRadical (t : J) :
      Submodule Aᵐᵒᵖ (σ.obj (a t)) :=
    Module.jacobson Aᵐᵒᵖ (σ.obj (a t))
  let coordinate (t : J) :
      sourceRadical →ₗ[Aᵐᵒᵖ] componentRadical t :=
    ((((LinearMap.proj t :
        (∀ s : J, σ.obj (a s)) →ₗ[Aᵐᵒᵖ] σ.obj (a t))).comp
          e.hom.hom.hom).domRestrict sourceRadical).codRestrict
      (componentRadical t) (fun z ↦ by
        apply Module.map_jacobson_le
          ((LinearMap.proj t :
            (∀ s : J, σ.obj (a s)) →ₗ[Aᵐᵒᵖ] σ.obj (a t)).comp
              e.hom.hom.hom)
        exact ⟨z.1, z.2, rfl⟩)
  let diagonal :
      sourceRadical →ₗ[Aᵐᵒᵖ] (∀ t : J, componentRadical t) :=
    LinearMap.pi coordinate
  have hdiagonal : Function.Injective diagonal := by
    intro z z' hzz'
    apply Subtype.ext
    apply (FGModuleCat.isoToLinearEquiv e).injective
    funext t
    exact congrArg Subtype.val (congrFun hzz' t)
  intro L hL
  letI : IsSimpleModule Aᵐᵒᵖ L := hL
  let f : L →ₗ[Aᵐᵒᵖ] (∀ t : J, componentRadical t) :=
    diagonal.comp L.subtype
  have hf : Function.Injective f :=
    hdiagonal.comp L.subtype_injective
  let eL : L ≃ₗ[Aᵐᵒᵖ] LinearMap.range f :=
    LinearEquiv.ofInjective f hf
  have hrangeSimple :
      IsSimpleModule Aᵐᵒᵖ (LinearMap.range f) :=
    IsSimpleModule.congr eL.symm
  have hproduct :
      HasSimpleConstituentsOfEitherType (A := A)
        (∀ t : J, componentRadical t) S T :=
    hasSimpleConstituentsOfEitherType_pi
      (A := A) (J := J) (M := fun t ↦ componentRadical t)
      (S := S) (T := T) (fun t ↦ hcomponent t)
  rcases hproduct (LinearMap.range f) hrangeSimple with hS | hT
  · exact Or.inl ⟨eL.trans hS.some⟩
  · exact Or.inr ⟨eL.trans hT.some⟩

theorem HasSimpleConstituentsOfEitherType.of_surjective_of_semisimple
    {M N S T : Type x}
    [AddCommGroup M] [Module Aᵐᵒᵖ M]
    [AddCommGroup N] [Module Aᵐᵒᵖ N]
    [AddCommGroup S] [Module Aᵐᵒᵖ S]
    [AddCommGroup T] [Module Aᵐᵒᵖ T]
    [IsSemisimpleModule Aᵐᵒᵖ M]
    (hM : HasSimpleConstituentsOfEitherType (A := A) M S T)
    (f : M →ₗ[Aᵐᵒᵖ] N) (hf : Function.Surjective f) :
    HasSimpleConstituentsOfEitherType (A := A) N S T := by
  intro L hL
  letI : IsSimpleModule Aᵐᵒᵖ L := hL
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
  let e : L ≃ₗ[Aᵐᵒᵖ] LinearMap.range l :=
    LinearEquiv.ofInjective l hlinj
  have hrangeSimple :
      IsSimpleModule Aᵐᵒᵖ (LinearMap.range l) :=
    IsSimpleModule.congr e.symm
  rcases hM (LinearMap.range l) hrangeSimple with hS | hT
  · exact Or.inl ⟨e.trans hS.some⟩
  · exact Or.inr ⟨e.trans hT.some⟩

/-- Split a dependent function on a sum type into its two restrictions. -/
def piSumLinearEquivProd
    {α β : Type} {M : α ⊕ β → Type x}
    [∀ i, AddCommGroup (M i)] [∀ i, Module Aᵐᵒᵖ (M i)] :
    ((i : α ⊕ β) → M i) ≃ₗ[Aᵐᵒᵖ]
      ((a : α) → M (.inl a)) × ((b : β) → M (.inr b)) where
  toFun f := (fun a ↦ f (.inl a), fun b ↦ f (.inr b))
  invFun f i := match i with
    | .inl a => f.1 a
    | .inr b => f.2 b
  left_inv f := by
    funext i
    cases i <;> rfl
  right_inv f := by
    rcases f with ⟨f, g⟩
    apply Prod.ext <;> funext i <;> rfl
  map_add' f g := by
    apply Prod.ext <;> funext i <;> rfl
  map_smul' r f := by
    apply Prod.ext <;> funext i <;> rfl

/-- A finite semisimple module whose simple constituents have one of two
types is a product of finite powers of those two types. -/
theorem exists_twoTypeDecomposition
    {M S T : Type x}
    [AddCommGroup M] [Module Aᵐᵒᵖ M]
    [AddCommGroup S] [Module Aᵐᵒᵖ S]
    [AddCommGroup T] [Module Aᵐᵒᵖ T]
    [IsSemisimpleModule Aᵐᵒᵖ M] [Module.Finite Aᵐᵒᵖ M]
    [IsSimpleModule Aᵐᵒᵖ S] [IsSimpleModule Aᵐᵒᵖ T]
    (h : HasSimpleConstituentsOfEitherType (A := A) M S T) :
    ∃ (J L : Type) (_ : Fintype J) (_ : Fintype L),
      Nonempty (M ≃ₗ[Aᵐᵒᵖ] (J → S) × (L → T)) := by
  classical
  obtain ⟨n, U, e, hU⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp Aᵐᵒᵖ M
  let P : Fin n → Prop := fun i ↦ Nonempty (U i ≃ₗ[Aᵐᵒᵖ] S)
  let J := {i : Fin n // P i}
  let L := {i : Fin n // ¬ P i}
  letI : Fintype J := Fintype.ofFinite J
  letI : Fintype L := Fintype.ofFinite L
  let eFun : M ≃ₗ[Aᵐᵒᵖ] (i : Fin n) → U i :=
    e.trans (DFinsupp.linearEquivFunOnFintype
      (R := Aᵐᵒᵖ) (M := fun i ↦ U i))
  let esum : J ⊕ L ≃ Fin n := Equiv.sumCompl P
  let eReindex :
      ((i : Fin n) → U i) ≃ₗ[Aᵐᵒᵖ]
        ((q : J ⊕ L) → U (esum q)) :=
    (LinearEquiv.piCongrLeft Aᵐᵒᵖ
      (fun i : Fin n ↦ U i) esum).symm
  let eSplit :
      ((q : J ⊕ L) → U (esum q)) ≃ₗ[Aᵐᵒᵖ]
        (((j : J) → U (esum (.inl j))) ×
          ((l : L) → U (esum (.inr l)))) :=
    piSumLinearEquivProd (A := A)
  let eLeft :
      ((j : J) → U (esum (.inl j))) ≃ₗ[Aᵐᵒᵖ]
        (J → S) :=
    LinearEquiv.piCongrRight (fun j ↦ by
      change U j.1 ≃ₗ[Aᵐᵒᵖ] S
      exact j.2.some)
  let eRight :
      ((l : L) → U (esum (.inr l))) ≃ₗ[Aᵐᵒᵖ]
        (L → T) :=
    LinearEquiv.piCongrRight (fun l ↦ by
      have hl : ¬ P l.1 := l.2
      have hT : Nonempty (U l.1 ≃ₗ[Aᵐᵒᵖ] T) :=
        (h (U l.1) (hU l.1)).resolve_left hl
      change U l.1 ≃ₗ[Aᵐᵒᵖ] T
      exact hT.some)
  exact ⟨J, L, inferInstance, inferInstance,
    ⟨eFun.trans eReindex |>.trans eSplit |>.trans (eLeft.prodCongr eRight)⟩⟩

theorem target_ne_of_ne_of_source_eq
    (hnoParallel :
      OpConjecture.GabrielArrowBridge.NoParallelExtSupport
        (K := K) (A := Aᵐᵒᵖ) σ)
    (e₁ e₂ : σ.LengthTwoIndex)
    (hne : e₁ ≠ e₂)
    (hsource :
      OpConjecture.GabrielArrowBridge.LengthTwo.source
          (A := Aᵐᵒᵖ) σ e₁ =
        OpConjecture.GabrielArrowBridge.LengthTwo.source
          (A := Aᵐᵒᵖ) σ e₂) :
    OpConjecture.GabrielArrowBridge.LengthTwo.target
        (A := Aᵐᵒᵖ) σ e₁ ≠
      OpConjecture.GabrielArrowBridge.LengthTwo.target
        (A := Aᵐᵒᵖ) σ e₂ := by
  intro htarget
  apply hne
  apply
    OpConjecture.GabrielArrowBridge.LengthTwo.toGabrielArrow_injective
      (K := K) σ
      hnoParallel
  apply Subtype.ext
  exact Prod.ext hsource htarget

theorem CommonSourcePair.exists_two_edges
    (p : σ.CommonSourcePair
      (OpConjecture.GabrielArrowBridge.LengthTwo.source
        (A := Aᵐᵒᵖ) σ)) :
    ∃ e₁ e₂ : σ.CommonSourceFiber
        (OpConjecture.GabrielArrowBridge.LengthTwo.source
          (A := Aᵐᵒᵖ) σ) p.1,
      e₁ ≠ e₂ ∧ ∀ e, e ∈ p.2.1 ↔ e = e₁ ∨ e = e₂ := by
  classical
  obtain ⟨e₁, e₂, hne, hp⟩ := Finset.card_eq_two.mp p.2.2
  refine ⟨e₁, e₂, hne, ?_⟩
  intro e
  rw [hp]
  simp

theorem facPresentation_sourceRadical_isSemisimple_commonSourcePair
    (p : σ.CommonSourcePair
      (OpConjecture.GabrielArrowBridge.LengthTwo.source
        (A := Aᵐᵒᵖ) σ))
    {j : ι}
    (P : σ.FacPresentation
      (σ.commonSourcePairSupport
        (OpConjecture.GabrielArrowBridge.LengthTwo.source
          (A := Aᵐᵒᵖ) σ) p)
      (σ.obj j)) :
    IsSemisimpleModule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ (σ.sumOver P.index P.label)) := by
  apply
    OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.moduleRadical_sumOver_isSemisimple
      σ P.index P.label
  intro t
  have hlabel := P.mem t
  rcases (by
    simpa [OpConjecture.IndecomposableSkeleton.commonSourcePairSupport]
      using hlabel) with hsource | hedge
  · letI : IsSimpleModule Aᵐᵒᵖ (σ.obj (P.label t)) :=
      (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
        (by simpa [hsource] using p.1.2)
    infer_instance
  · rcases hedge with ⟨e, -, he⟩
    change e.1.1 = P.label t at he
    have hlength : σ.compositionLength (P.label t) = 2 := by
      simpa [← he] using e.1.2
    letI : IsSimpleModule Aᵐᵒᵖ
        (Module.jacobson Aᵐᵒᵖ (σ.obj (P.label t))) :=
      OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.moduleRadical_isSimple_of_compositionLength_eq_two
        σ hlength
    infer_instance

theorem facPresentation_sourceRadical_hasEitherTargetType
    (p : σ.CommonSourcePair
      (OpConjecture.GabrielArrowBridge.LengthTwo.source
        (A := Aᵐᵒᵖ) σ))
    (e₁ e₂ : σ.CommonSourceFiber
      (OpConjecture.GabrielArrowBridge.LengthTwo.source
        (A := Aᵐᵒᵖ) σ) p.1)
    (hp : ∀ e, e ∈ p.2.1 ↔ e = e₁ ∨ e = e₂)
    {j : ι}
    (P : σ.FacPresentation
      (σ.commonSourcePairSupport
        (OpConjecture.GabrielArrowBridge.LengthTwo.source
          (A := Aᵐᵒᵖ) σ) p)
      (σ.obj j)) :
    HasSimpleConstituentsOfEitherType (A := A)
      (Module.jacobson Aᵐᵒᵖ (σ.sumOver P.index P.label))
      (σ.obj
        (OpConjecture.GabrielArrowBridge.LengthTwo.target
          (A := Aᵐᵒᵖ) σ e₁.1).1)
      (σ.obj
        (OpConjecture.GabrielArrowBridge.LengthTwo.target
          (A := Aᵐᵒᵖ) σ e₂.1).1) := by
  apply moduleRadical_sumOver_hasSimpleConstituentsOfEitherType
    (A := A) σ P.index P.label
  intro t
  have hlabel := P.mem t
  rcases (by
    simpa [OpConjecture.IndecomposableSkeleton.commonSourcePairSupport]
      using hlabel) with hsource | hedge
  · have hsimple : Simple (σ.obj (P.label t)) := by
      simpa [hsource] using p.1.2
    letI : IsSimpleModule Aᵐᵒᵖ (σ.obj (P.label t)) :=
      (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
        hsimple
    have hbot :
        Module.jacobson Aᵐᵒᵖ (σ.obj (P.label t)) = ⊥ :=
      IsSimpleModule.jacobson_eq_bot Aᵐᵒᵖ (σ.obj (P.label t))
    letI : Subsingleton
        (Module.jacobson Aᵐᵒᵖ (σ.obj (P.label t))) := by
      rw [Submodule.subsingleton_iff_eq_bot]
      exact hbot
    exact HasSimpleConstituentsOfEitherType.of_subsingleton (A := A)
  · rcases hedge with ⟨e, heP, he⟩
    change e.1.1 = P.label t at he
    rcases (hp e).1 heP with he₁ | he₂
    · subst e
      have hlength : σ.compositionLength (P.label t) = 2 := by
        simpa [← he] using e₁.1.2
      letI : IsSimpleModule Aᵐᵒᵖ
          (Module.jacobson Aᵐᵒᵖ (σ.obj (P.label t))) :=
        OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.moduleRadical_isSimple_of_compositionLength_eq_two
          σ hlength
      have erad : Nonempty
          (Module.jacobson Aᵐᵒᵖ (σ.obj (P.label t)) ≃ₗ[Aᵐᵒᵖ]
            σ.obj
              (OpConjecture.GabrielArrowBridge.LengthTwo.target
                (A := Aᵐᵒᵖ) σ e₁.1).1) := by
        rw [← he]
        exact
          OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.moduleRadical_linearEquiv_simpleSubmodule
            σ e₁.1.2
              (OpConjecture.GabrielArrowBridge.LengthTwo.submodule σ e₁.1)
      exact
        HasSimpleConstituentsOfEitherType.of_simple_left
          (A := A) erad.some
    · subst e
      have hlength : σ.compositionLength (P.label t) = 2 := by
        simpa [← he] using e₂.1.2
      letI : IsSimpleModule Aᵐᵒᵖ
          (Module.jacobson Aᵐᵒᵖ (σ.obj (P.label t))) :=
        OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.moduleRadical_isSimple_of_compositionLength_eq_two
          σ hlength
      have erad : Nonempty
          (Module.jacobson Aᵐᵒᵖ (σ.obj (P.label t)) ≃ₗ[Aᵐᵒᵖ]
            σ.obj
              (OpConjecture.GabrielArrowBridge.LengthTwo.target
                (A := Aᵐᵒᵖ) σ e₂.1).1) := by
        rw [← he]
        exact
          OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.moduleRadical_linearEquiv_simpleSubmodule
            σ e₂.1.2
              (OpConjecture.GabrielArrowBridge.LengthTwo.submodule σ e₂.1)
      exact
        HasSimpleConstituentsOfEitherType.of_simple_right
          (A := A) erad.some

theorem moduleRadical_isSemisimple_of_inFac_commonSourcePair
    (p : σ.CommonSourcePair
      (OpConjecture.GabrielArrowBridge.LengthTwo.source
        (A := Aᵐᵒᵖ) σ))
    {j : ι}
    (hj : σ.InFac
      (σ.commonSourcePairSupport
        (OpConjecture.GabrielArrowBridge.LengthTwo.source
          (A := Aᵐᵒᵖ) σ) p)
      (σ.obj j)) :
    IsSemisimpleModule Aᵐᵒᵖ (σ.moduleRadical j) := by
  obtain ⟨P⟩ := hj
  letI (t : P.index) : IsArtinian Aᵐᵒᵖ (σ.obj (P.label t)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength (P.label t))).2
  let e :
      σ.sumOver P.index P.label ≅
        FGModuleCat.of Aᵐᵒᵖ (∀ t : P.index, σ.obj (P.label t)) :=
    OpConjecture.IndecomposableSkeleton.biproductIsoPiFG _
  letI : IsArtinian Aᵐᵒᵖ (σ.sumOver P.index P.label) :=
    (LinearEquiv.isArtinian_iff
      (FGModuleCat.isoToLinearEquiv e)).mpr inferInstance
  letI : IsSemisimpleModule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ (σ.sumOver P.index P.label)) :=
    facPresentation_sourceRadical_isSemisimple_commonSourcePair σ p P
  letI : Epi P.map := P.epi
  have hsurj : Function.Surjective P.map.hom.hom :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective P.map).mp
      inferInstance
  have hradical :
      Submodule.map P.map.hom.hom
          (Module.jacobson Aᵐᵒᵖ (σ.sumOver P.index P.label)) =
        σ.moduleRadical j :=
    OpConjecture.LengthTwoGabrielBridge.map_jacobson_of_surjective_of_isArtinian
      P.map.hom.hom hsurj
  let sourceRadical : Submodule Aᵐᵒᵖ (σ.sumOver P.index P.label) :=
    Module.jacobson Aᵐᵒᵖ (σ.sumOver P.index P.label)
  let targetRadical : Submodule Aᵐᵒᵖ (σ.obj j) := σ.moduleRadical j
  let radicalMap : sourceRadical →ₗ[Aᵐᵒᵖ] targetRadical :=
    (P.map.hom.hom.domRestrict sourceRadical).codRestrict
      targetRadical (fun z ↦ by
        apply Module.map_jacobson_le P.map.hom.hom
        exact ⟨z.1, z.2, rfl⟩)
  have hradicalMap : Function.Surjective radicalMap := by
    intro y
    have hy : y.1 ∈ Submodule.map P.map.hom.hom sourceRadical := by
      rw [hradical]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact hzy
  exact IsSemisimpleModule.of_surjective radicalMap hradicalMap

theorem moduleRadical_hasEitherTargetType_of_inFac_commonSourcePair
    (p : σ.CommonSourcePair
      (OpConjecture.GabrielArrowBridge.LengthTwo.source
        (A := Aᵐᵒᵖ) σ))
    (e₁ e₂ : σ.CommonSourceFiber
      (OpConjecture.GabrielArrowBridge.LengthTwo.source
        (A := Aᵐᵒᵖ) σ) p.1)
    (hp : ∀ e, e ∈ p.2.1 ↔ e = e₁ ∨ e = e₂)
    {j : ι}
    (hj : σ.InFac
      (σ.commonSourcePairSupport
        (OpConjecture.GabrielArrowBridge.LengthTwo.source
          (A := Aᵐᵒᵖ) σ) p)
      (σ.obj j)) :
    HasSimpleConstituentsOfEitherType (A := A)
      (σ.moduleRadical j)
      (σ.obj
        (OpConjecture.GabrielArrowBridge.LengthTwo.target
          (A := Aᵐᵒᵖ) σ e₁.1).1)
      (σ.obj
        (OpConjecture.GabrielArrowBridge.LengthTwo.target
          (A := Aᵐᵒᵖ) σ e₂.1).1) := by
  obtain ⟨P⟩ := hj
  letI (t : P.index) : IsArtinian Aᵐᵒᵖ (σ.obj (P.label t)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength (P.label t))).2
  let e :
      σ.sumOver P.index P.label ≅
        FGModuleCat.of Aᵐᵒᵖ (∀ t : P.index, σ.obj (P.label t)) :=
    OpConjecture.IndecomposableSkeleton.biproductIsoPiFG _
  letI : IsArtinian Aᵐᵒᵖ (σ.sumOver P.index P.label) :=
    (LinearEquiv.isArtinian_iff
      (FGModuleCat.isoToLinearEquiv e)).mpr inferInstance
  letI : IsSemisimpleModule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ (σ.sumOver P.index P.label)) :=
    facPresentation_sourceRadical_isSemisimple_commonSourcePair σ p P
  have hsourceTypes :=
    facPresentation_sourceRadical_hasEitherTargetType
      (A := A) σ p e₁ e₂ hp P
  letI : Epi P.map := P.epi
  have hsurj : Function.Surjective P.map.hom.hom :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective P.map).mp
      inferInstance
  have hradical :
      Submodule.map P.map.hom.hom
          (Module.jacobson Aᵐᵒᵖ (σ.sumOver P.index P.label)) =
        σ.moduleRadical j :=
    OpConjecture.LengthTwoGabrielBridge.map_jacobson_of_surjective_of_isArtinian
      P.map.hom.hom hsurj
  let sourceRadical : Submodule Aᵐᵒᵖ (σ.sumOver P.index P.label) :=
    Module.jacobson Aᵐᵒᵖ (σ.sumOver P.index P.label)
  let targetRadical : Submodule Aᵐᵒᵖ (σ.obj j) := σ.moduleRadical j
  let radicalMap : sourceRadical →ₗ[Aᵐᵒᵖ] targetRadical :=
    (P.map.hom.hom.domRestrict sourceRadical).codRestrict
      targetRadical (fun z ↦ by
        apply Module.map_jacobson_le P.map.hom.hom
        exact ⟨z.1, z.2, rfl⟩)
  have hradicalMap : Function.Surjective radicalMap := by
    intro y
    have hy : y.1 ∈ Submodule.map P.map.hom.hom sourceRadical := by
      rw [hradical]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact hzy
  exact hsourceTypes.of_surjective_of_semisimple radicalMap hradicalMap

theorem exists_moduleRadical_twoTargetDecomposition_of_edges
    (p : σ.CommonSourcePair
      (OpConjecture.GabrielArrowBridge.LengthTwo.source
        (A := Aᵐᵒᵖ) σ))
    (e₁ e₂ : σ.CommonSourceFiber
      (OpConjecture.GabrielArrowBridge.LengthTwo.source
        (A := Aᵐᵒᵖ) σ) p.1)
    (hp : ∀ e, e ∈ p.2.1 ↔ e = e₁ ∨ e = e₂)
    {j : ι}
    (hj : σ.InFac
      (σ.commonSourcePairSupport
        (OpConjecture.GabrielArrowBridge.LengthTwo.source
          (A := Aᵐᵒᵖ) σ) p)
      (σ.obj j)) :
    ∃ (J L : Type) (_ : Fintype J) (_ : Fintype L),
      Nonempty
        (σ.moduleRadical j ≃ₗ[Aᵐᵒᵖ]
          (J → σ.obj
            (OpConjecture.GabrielArrowBridge.LengthTwo.target
              (A := Aᵐᵒᵖ) σ e₁.1).1) ×
          (L → σ.obj
            (OpConjecture.GabrielArrowBridge.LengthTwo.target
              (A := Aᵐᵒᵖ) σ e₂.1).1)) := by
  letI : IsSemisimpleModule Aᵐᵒᵖ (σ.moduleRadical j) :=
    moduleRadical_isSemisimple_of_inFac_commonSourcePair σ p hj
  letI : Module.Finite Aᵐᵒᵖ (σ.moduleRadical j) := inferInstance
  letI : IsSimpleModule Aᵐᵒᵖ
      (σ.obj
        (OpConjecture.GabrielArrowBridge.LengthTwo.target
          (A := Aᵐᵒᵖ) σ e₁.1).1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      (OpConjecture.GabrielArrowBridge.LengthTwo.target
        (A := Aᵐᵒᵖ) σ e₁.1).2
  letI : IsSimpleModule Aᵐᵒᵖ
      (σ.obj
        (OpConjecture.GabrielArrowBridge.LengthTwo.target
          (A := Aᵐᵒᵖ) σ e₂.1).1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      (OpConjecture.GabrielArrowBridge.LengthTwo.target
        (A := Aᵐᵒᵖ) σ e₂.1).2
  exact exists_twoTypeDecomposition (A := A)
    (moduleRadical_hasEitherTargetType_of_inFac_commonSourcePair
      (A := A) σ p e₁ e₂ hp hj)

/-- The available two-target Ext bridge: once the common top is already one
simple copy, indecomposability bounds both radical multiplicities by one. -/
theorem radicalMultiplicityBounds_of_simpleTop_twoTypeDecomposition
    (hnoParallel :
      OpConjecture.LoewyTwoRankCore.NoParallelExtOne σ K)
    {j s t r : ι}
    (hs : Simple (σ.obj s)) (ht : Simple (σ.obj t))
    (hr : Simple (σ.obj r))
    (n m : ℕ)
    (eRadical :
      ((Fin n → σ.obj s) × (Fin m → σ.obj t)) ≃ₗ[Aᵐᵒᵖ]
        σ.moduleRadical j)
    (eTop : σ.obj r ≃ₗ[Aᵐᵒᵖ] σ.moduleTop j) :
    n ≤ 1 ∧ m ≤ 1 := by
  let leftIso :
      ((⨁ fun _ : Fin n ↦ (σ.obj s).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (Fin n → σ.obj s) :=
    ModuleCat.biproductIsoPi (fun _ : Fin n ↦ (σ.obj s).obj)
  let rightIso :
      ((⨁ fun _ : Fin m ↦ (σ.obj t).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (Fin m → σ.obj t) :=
    ModuleCat.biproductIsoPi (fun _ : Fin m ↦ (σ.obj t).obj)
  let radicalIso :
      (((⨁ fun _ : Fin n ↦ (σ.obj s).obj) ⊞
          (⨁ fun _ : Fin m ↦ (σ.obj t).obj)) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (σ.moduleRadical j) :=
    biprod.mapIso leftIso rightIso ≪≫
      ModuleCat.biprodIsoProd
        (ModuleCat.of Aᵐᵒᵖ (Fin n → σ.obj s))
        (ModuleCat.of Aᵐᵒᵖ (Fin m → σ.obj t)) ≪≫
      eRadical.toModuleIso
  let topIso :
      ((⨁ fun _ : Unit ↦ (σ.obj r).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (σ.moduleTop j) :=
    ModuleCat.biproductIsoPi
        (fun _ : Unit ↦ (σ.obj r).obj) ≪≫
      (LinearEquiv.funUnique Unit Aᵐᵒᵖ (σ.obj r)).toModuleIso ≪≫
      eTop.toModuleIso
  let eRadical' :
      ((((⨁ fun _ : Fin n ↦ (σ.obj s).obj) ⊞
          (⨁ fun _ : Fin m ↦ (σ.obj t).obj)) :
          ModuleCat.{x} Aᵐᵒᵖ)) ≃ₗ[Aᵐᵒᵖ]
        σ.moduleRadical j :=
    radicalIso.toLinearEquiv
  let eMiddle : (σ.obj j) ≃ₗ[Aᵐᵒᵖ] (σ.obj j) :=
    LinearEquiv.refl Aᵐᵒᵖ (σ.obj j)
  let eTop' :
      (((⨁ fun _ : Unit ↦ (σ.obj r).obj) :
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
  have hbounds :=
    OpConjecture.YonedaExtReflection.shortExact_twoTarget_target_finrank_le_one
      (σ.obj r).obj (σ.obj s).obj (σ.obj t).obj (σ.obj j).obj
      hrNonzero hsNonzero htNonzero
      SC.f SC.g SC.zero hSC' (σ.indecomposable j)
      ell hell ell' hell' (by simp)
  simpa using hbounds

end OpConjecture.FamilyThreeSpecialization
