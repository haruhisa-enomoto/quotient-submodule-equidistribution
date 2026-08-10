import QuotientSubmoduleEquidistribution.RepresentationTheory.AnnihilatorInflation
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalAlgebra

/-!
# Canonical quotient skeleton and ambient alignment

This file constructs canonical indecomposable skeletons of `R/I`, embeds their
labels into a complete indecomposable skeleton of `R`, and proves exact
transport of the literal quotient and submodule closures.  When the ambient
skeleton is finite, the selected factor skeleton is finite as well.  It also
proves that every ambient support whose common annihilator is exactly `I` is
covered by those quotient labels.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.QuotientSkeletonAlignment

universe u

open QuotientSubmoduleEquidistribution.AnnihilatorInflation

section FactorInstances

/-- The canonical complete indecomposable skeleton over a left Artinian
ring.  Hopkins--Levitzki supplies the Noetherian instance needed by
`FGModuleCat`. -/
noncomputable def artinSkeleton
    (R : Type u) [Ring R] [IsArtinianRing R] :
    IndecomposableSkeleton.{u, u + 1, u} R
      (CanonicalIndecomposableIndex.{u, u} R) :=
  indecomposableSkeletonOfFiniteLength
    (fun X ↦
      ((IsArtinianRing.tfae R X).out 0 3).mp
        (inferInstance : Module.Finite R X))

/-- Every finitely generated module over the finite-dimensional factor
algebra has finite length. -/
theorem factor_isFiniteLength
    (K R : Type u) [Field K] [Ring R] [Algebra K R]
    [FiniteDimensional K R] (I : TwoSidedIdeal R)
    [IsNoetherianRing (Quotient.Factor I)]
    (X : FGModuleCat.{u} (Quotient.Factor I)) :
    IsFiniteLength (Quotient.Factor I) X := by
  letI : IsArtinianRing (Quotient.Factor I) :=
    IsArtinianRing.of_finite K _
  exact
    ((IsArtinianRing.tfae (Quotient.Factor I) X).out 0 3).mp
      (inferInstance : Module.Finite (Quotient.Factor I) X)

/-- The canonical complete duplicate-free skeleton of indecomposable factor
modules. -/
abbrev FactorIndex (R : Type u) [Ring R] (I : TwoSidedIdeal R)
    [IsNoetherianRing (Quotient.Factor I)] :=
  CanonicalIndecomposableIndex.{u, u} (Quotient.Factor I)

noncomputable def factorSkeleton
    (K R : Type u) [Field K] [Ring R] [Algebra K R]
    [FiniteDimensional K R] (I : TwoSidedIdeal R)
    [IsNoetherianRing (Quotient.Factor I)] :
    IndecomposableSkeleton.{u, u + 1, u} (Quotient.Factor I)
      (FactorIndex R I) :=
  indecomposableSkeletonOfFiniteLength
    (fun X ↦ factor_isFiniteLength K R I X)

/-- Every factor of a left Artinian ring has the canonical complete
indecomposable skeleton, without a field or finite-dimensionality
hypothesis. -/
noncomputable def artinFactorSkeleton
    (R : Type u) [Ring R] [IsArtinianRing R]
    (I : TwoSidedIdeal R) :
    IndecomposableSkeleton.{u, u + 1, u} (Quotient.Factor I)
      (FactorIndex R I) :=
  indecomposableSkeletonOfFiniteLength
    (fun X ↦
      ((IsArtinianRing.tfae (Quotient.Factor I) X).out 0 3).mp
        (inferInstance : Module.Finite (Quotient.Factor I) X))

end FactorInstances

/-! ## Indecomposability and quotient inflation -/

variable {R : Type u} [Ring R]

/-- A quotient indecomposable remains indecomposable after inflation.  The
key input is fullness: every ambient endomorphism of an inflated module is
already quotient-linear. -/
theorem indecomposable_inflation (I : TwoSidedIdeal R)
    (X : FGModuleCat.{u} (Quotient.Factor I))
    (hX : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (Quotient.Factor I) X) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R ((Quotient.functor I).obj X) := by
  rw [QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  refine ⟨hX.nontrivial, ?_⟩
  intro f hf
  letI : Module.Finite R ((Quotient.functor I).obj X) :=
    ((Quotient.functor I).obj X).property
  let fcat : (Quotient.functor I).obj X ⟶ (Quotient.functor I).obj X :=
    ConcreteCategory.ofHom f
  let gcat : X ⟶ X := (Quotient.functor I).preimage fcat
  let g : Module.End (Quotient.Factor I) X := gcat.hom.hom
  have hcat : gcat ≫ gcat = gcat := by
    apply (Quotient.functor I).map_injective
    rw [(Quotient.functor I).map_comp]
    change
      (Quotient.functor I).map ((Quotient.functor I).preimage fcat) ≫
          (Quotient.functor I).map ((Quotient.functor I).preimage fcat) =
        (Quotient.functor I).map ((Quotient.functor I).preimage fcat)
    rw [(Quotient.functor I).map_preimage fcat]
    apply FGModuleCat.hom_ext
    change f.comp f = f
    change f * f = f at hf
    simpa [Module.End.mul_eq_comp] using hf
  have hg : IsIdempotentElem g := by
    change g * g = g
    have hlinear := congrArg (fun q : X ⟶ X ↦ q.hom.hom) hcat
    simpa [g, Module.End.mul_eq_comp] using hlinear
  rcases hX.eq_zero_or_eq_one_of_isIdempotentElem hg with hzero | hone
  · left
    have hgcat : gcat = 0 := by
      apply FGModuleCat.hom_ext
      exact hzero
    have hfcat : fcat = 0 := by
      calc
        fcat = (Quotient.functor I).map gcat :=
          ((Quotient.functor I).map_preimage fcat).symm
        _ = (Quotient.functor I).map 0 := congrArg _ hgcat
        _ = 0 := (Quotient.functor I).map_zero X X
    ext x
    have hx := congrArg
      (fun q : (Quotient.functor I).obj X ⟶
          (Quotient.functor I).obj X ↦ q.hom.hom x) hfcat
    change f x = 0 at hx
    simpa using hx
  · right
    have hgcat : gcat = CategoryStruct.id X := by
      apply FGModuleCat.hom_ext
      simpa [g, Module.End.one_eq_id] using hone
    have hfcat : fcat = CategoryStruct.id ((Quotient.functor I).obj X) := by
      calc
        fcat = (Quotient.functor I).map gcat :=
          ((Quotient.functor I).map_preimage fcat).symm
        _ = (Quotient.functor I).map (CategoryStruct.id X) :=
          congrArg _ hgcat
        _ = CategoryStruct.id ((Quotient.functor I).obj X) :=
          (Quotient.functor I).map_id X
    ext x
    have hx := congrArg
      (fun q : (Quotient.functor I).obj X ⟶
          (Quotient.functor I).obj X ↦ q.hom.hom x) hfcat
    change f x = x at hx
    simpa [Module.End.one_eq_id] using hx

/-- Conversely, indecomposability of the inflated module reflects back to
the factor, by faithfulness of inflation. -/
theorem indecomposable_of_inflation (I : TwoSidedIdeal R)
    (X : FGModuleCat.{u} (Quotient.Factor I))
    (hX : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R ((Quotient.functor I).obj X)) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (Quotient.Factor I) X := by
  rw [QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  refine ⟨hX.nontrivial, ?_⟩
  intro f hf
  let fcat : X ⟶ X := ConcreteCategory.ofHom f
  let gcat : (Quotient.functor I).obj X ⟶ (Quotient.functor I).obj X :=
    (Quotient.functor I).map fcat
  let g : Module.End R ((Quotient.functor I).obj X) := gcat.hom.hom
  have hcat : fcat ≫ fcat = fcat := by
    apply FGModuleCat.hom_ext
    change f.comp f = f
    change f * f = f at hf
    simpa [Module.End.mul_eq_comp] using hf
  have hgcat : gcat ≫ gcat = gcat := by
    rw [← (Quotient.functor I).map_comp, hcat]
  have hg : IsIdempotentElem g := by
    change g * g = g
    have hlinear := congrArg
      (fun q : (Quotient.functor I).obj X ⟶
        (Quotient.functor I).obj X ↦ q.hom.hom) hgcat
    simpa [g, Module.End.mul_eq_comp] using hlinear
  rcases hX.eq_zero_or_eq_one_of_isIdempotentElem hg with hzero | hone
  · left
    have hgcat0 : gcat = 0 := by
      apply FGModuleCat.hom_ext
      exact hzero
    have hfcat0 : fcat = 0 := by
      apply (Quotient.functor I).map_injective
      simpa [gcat] using hgcat0
    have hlinear := congrArg (fun q : X ⟶ X ↦ q.hom.hom) hfcat0
    exact hlinear
  · right
    have hgcat1 : gcat = CategoryStruct.id ((Quotient.functor I).obj X) := by
      apply FGModuleCat.hom_ext
      simpa [g, Module.End.one_eq_id] using hone
    have hfcat1 : fcat = CategoryStruct.id X := by
      apply (Quotient.functor I).map_injective
      simpa [gcat] using hgcat1
    have hlinear := congrArg (fun q : X ⟶ X ↦ q.hom.hom) hfcat1
    change f = LinearMap.id
    change f = LinearMap.id at hlinear
    exact hlinear

/-! ## Descending modules killed by the ideal -/

/-- An ambient finitely generated module killed by `I` acquires its unique
factor-module structure. -/
def descendFG (I : TwoSidedIdeal R) (X : FGModuleCat.{u} R)
    (hI : ∀ r, r ∈ I → ∀ x : X, r • x = 0) :
    FGModuleCat.{u} (Quotient.Factor I) := by
  letI : SMul (Quotient.Factor I) X :=
    ⟨fun q x ↦ Quotient.liftOn' q (fun r : R ↦ r • x) (by
      intro a b hab
      have habI : a - b ∈ I.asIdeal :=
        (Submodule.quotientRel_def I.asIdeal).mp hab
      have hz := hI (a - b) habI x
      rw [sub_smul, sub_eq_zero] at hz
      exact hz)⟩
  letI : Module (Quotient.Factor I) X :=
    Function.Surjective.moduleLeft
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.Quotient.map I)
      Ideal.Quotient.mk_surjective (fun _ _ ↦ rfl)
  letI : IsScalarTower R (Quotient.Factor I) X := by
    constructor
    intro r q x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact mul_smul r s x
  letI : Module.Finite (Quotient.Factor I) X :=
    Module.Finite.of_restrictScalars_finite R _ X
  exact FGModuleCat.of _ X

/-- Inflating the descended structure recovers the original ambient module. -/
def descendInflateIso (I : TwoSidedIdeal R) (X : FGModuleCat.{u} R)
    (hI : ∀ r, r ∈ I → ∀ x : X, r • x = 0) :
    (Quotient.functor I).obj (descendFG I X hI) ≅ X where
  hom := ConcreteCategory.ofHom
    { toFun := id
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  inv := ConcreteCategory.ofHom
    { toFun := id
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  hom_inv_id := by
    ext x
    rfl
  inv_hom_id := by
    ext x
    rfl

/-! ## Alignment with a finite complete ambient skeleton -/

section Alignment

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {iota : Type (u + 1)} [Finite iota]
  (sigma : IndecomposableSkeleton.{u, u + 1, u} R iota)
  (I : TwoSidedIdeal R) [IsNoetherianRing (Quotient.Factor I)]
  (tau : IndecomposableSkeleton.{u, u + 1, u}
    (Quotient.Factor I) (FactorIndex R I))

/-- The ambient label selected for an inflated factor indecomposable. -/
noncomputable def inflationLabel (l : FactorIndex R I) : iota :=
  Classical.choose
    (sigma.complete ((Quotient.functor I).obj (tau.obj l))
      (indecomposable_inflation I (tau.obj l) (tau.indecomposable l)))

/-- The defining objectwise isomorphism for the selected label. -/
noncomputable def inflationObjIso (l : FactorIndex R I) :
    sigma.obj (inflationLabel sigma I tau l) ≅
      (Quotient.functor I).obj (tau.obj l) :=
  (Classical.choice
    (Classical.choose_spec
      (sigma.complete ((Quotient.functor I).obj (tau.obj l))
        (indecomposable_inflation I (tau.obj l) (tau.indecomposable l))))).symm

omit [Finite iota] in
/-- Distinct factor indecomposables receive distinct ambient labels. -/
theorem inflationLabel_injective :
    Function.Injective (inflationLabel sigma I tau) := by
  intro l m hlabel
  apply tau.eq_of_iso
  let e : (Quotient.functor I).obj (tau.obj l) ≅
      (Quotient.functor I).obj (tau.obj m) :=
    (inflationObjIso sigma I tau l).symm ≪≫
      eqToIso (congrArg sigma.obj hlabel) ≪≫
        inflationObjIso sigma I tau m
  exact ⟨(Quotient.fullyFaithful I).preimageIso e⟩

/-- The selected factor labels form a bundled finite complete skeleton
whenever the ambient skeleton is finite. -/
noncomputable def alignedFiniteFactorSkeleton :
    FiniteIndecomposableSkeleton.{u, u + 1, u} (Quotient.Factor I) where
  ι := FactorIndex R I
  finite_ι :=
    Finite.of_injective (inflationLabel sigma I tau)
      (inflationLabel_injective sigma I tau)
  skeleton := tau

/-- Package the selected labels as an embedding. -/
noncomputable def inflationLabelEmbedding : FactorIndex R I ↪ iota :=
  ⟨inflationLabel sigma I tau,
    inflationLabel_injective sigma I tau⟩

omit [Finite iota] in
/-- Any ambient skeleton label killed by `I` comes from a unique factor
label. -/
theorem inflation_covers_killed_label {k : iota}
    (hkilled : ∀ r, r ∈ I → ∀ x : sigma.obj k, r • x = 0) :
    k ∈ Set.range (inflationLabelEmbedding sigma I tau) := by
  let X : FGModuleCat.{u} (Quotient.Factor I) :=
    descendFG I (sigma.obj k) hkilled
  have hXin : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R
      ((Quotient.functor I).obj X) :=
    (sigma.indecomposable k).of_linearEquiv
      (FGModuleCat.isoToLinearEquiv
        (descendInflateIso I (sigma.obj k) hkilled).symm)
  have hX : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (Quotient.Factor I) X :=
    indecomposable_of_inflation I X hXin
  obtain ⟨l, ⟨e⟩⟩ := tau.complete X hX
  refine ⟨l, ?_⟩
  apply sigma.eq_of_iso
  exact ⟨inflationObjIso sigma I tau l ≪≫
    ((Quotient.functor I).mapIso e).symm ≪≫
      descendInflateIso I (sigma.obj k) hkilled⟩

omit [Finite iota] in
/-- Every support with exact annihilator `I` consists only of factor-module
labels. -/
theorem inflation_covers
    (S : Set iota)
    (hS : supportAnnihilator sigma.obj S = I) :
    S ⊆ Set.range (inflationLabelEmbedding sigma I tau) := by
  intro k hk
  have hkilled : ∀ r, r ∈ I → ∀ x : sigma.obj k, r • x = 0 := by
    intro r hr x
    have hr' : r ∈ supportAnnihilator sigma.obj S := by
      rw [hS]
      exact hr
    exact (mem_supportAnnihilator sigma.obj).mp hr' k hk x
  exact inflation_covers_killed_label sigma I tau hkilled

end Alignment

section Transport

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {iota : Type (u + 1)}
  (sigma : IndecomposableSkeleton.{u, u + 1, u} R iota)
  (I : TwoSidedIdeal R) [IsNoetherianRing (Quotient.Factor I)]
  (tau : IndecomposableSkeleton.{u, u + 1, u}
    (Quotient.Factor I) (FactorIndex R I))

def inflationPiIso (J : FintypeCat.{0})
    (a : J → FactorIndex R I) :
    FGModuleCat.of R
        (∀ t : J, (Quotient.functor I).obj (tau.obj (a t))) ≅
      (Quotient.functor I).obj
        (FGModuleCat.of (Quotient.Factor I)
          (∀ t : J, tau.obj (a t))) where
  hom := ConcreteCategory.ofHom
    { toFun := id
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  inv := ConcreteCategory.ofHom
    { toFun := id
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

def inflationBiproductIso (J : FintypeCat.{0})
    (a : J → FactorIndex R I) :
    (⨁ fun t ↦ (Quotient.functor I).obj (tau.obj (a t))) ≅
      (Quotient.functor I).obj (tau.sumOver J a) :=
  IndecomposableSkeleton.biproductIsoPiFG
      (fun t : J ↦ (Quotient.functor I).obj (tau.obj (a t))) ≪≫
    inflationPiIso I tau J a ≪≫
    ((Quotient.functor I).mapIso
      (IndecomposableSkeleton.biproductIsoPiFG
        (fun t : J ↦ tau.obj (a t)))).symm

def inflationSumIso (J : FintypeCat.{0})
    (a : J → FactorIndex R I) :
    sigma.sumOver J (fun t ↦ inflationLabel sigma I tau (a t)) ≅
      (Quotient.functor I).obj (tau.sumOver J a) :=
  biproduct.mapIso (fun t ↦ inflationObjIso sigma I tau (a t)) ≪≫
    inflationBiproductIso I tau J a

/-- Inflate a quotient presentation between selected factor labels. -/
def inflateFacPresentation {T : Set (FactorIndex R I)}
    {l : FactorIndex R I}
    (P : tau.FacPresentation T (tau.obj l)) :
    sigma.FacPresentation
      ((inflationLabelEmbedding sigma I tau) '' T)
      (sigma.obj (inflationLabel sigma I tau l)) where
  index := P.index
  label := fun t ↦ inflationLabel sigma I tau (P.label t)
  mem t := ⟨P.label t, P.mem t, rfl⟩
  map :=
    (inflationSumIso sigma I tau P.index P.label).hom ≫
      (Quotient.functor I).map P.map ≫
        (inflationObjIso sigma I tau l).inv
  epi := by
    letI : Epi P.map := P.epi
    have hsurj : Function.Surjective
        ((Quotient.functor I).map P.map).hom.hom :=
      (IndecomposableSkeleton.fg_epi_iff_surjective P.map).mp
        (inferInstance : Epi P.map)
    letI : Epi ((Quotient.functor I).map P.map) :=
      (IndecomposableSkeleton.fg_epi_iff_surjective _).mpr hsurj
    infer_instance

/-- Inflate a submodule presentation between selected factor labels. -/
def inflateSubPresentation {T : Set (FactorIndex R I)}
    {l : FactorIndex R I}
    (P : tau.SubPresentation T (tau.obj l)) :
    sigma.SubPresentation
      ((inflationLabelEmbedding sigma I tau) '' T)
      (sigma.obj (inflationLabel sigma I tau l)) where
  index := P.index
  label := fun t ↦ inflationLabel sigma I tau (P.label t)
  mem t := ⟨P.label t, P.mem t, rfl⟩
  map :=
    (inflationObjIso sigma I tau l).hom ≫
      (Quotient.functor I).map P.map ≫
        (inflationSumIso sigma I tau P.index P.label).inv
  mono := by
    letI : Mono P.map := P.mono
    have hinj : Function.Injective
        ((Quotient.functor I).map P.map).hom.hom :=
      (IndecomposableSkeleton.fg_mono_iff_injective P.map).mp
        (inferInstance : Mono P.map)
    letI : Mono ((Quotient.functor I).map P.map) :=
      (IndecomposableSkeleton.fg_mono_iff_injective _).mpr hinj
    infer_instance

/-- Reflect an ambient quotient presentation whose source and target labels
all belong to the factor image. -/
def reflectFacPresentation {T : Set (FactorIndex R I)}
    {l : FactorIndex R I}
    (P : sigma.FacPresentation
      ((inflationLabelEmbedding sigma I tau) '' T)
      (sigma.obj (inflationLabel sigma I tau l))) :
    tau.FacPresentation T (tau.obj l) := by
  let a : P.index → FactorIndex R I :=
    fun t ↦ Classical.choose (P.mem t)
  have ha_mem (t : P.index) : a t ∈ T :=
    (Classical.choose_spec (P.mem t)).1
  have ha_eq (t : P.index) :
      inflationLabel sigma I tau (a t) = P.label t :=
    (Classical.choose_spec (P.mem t)).2
  let relabelIso :
      sigma.sumOver P.index
          (fun t ↦ inflationLabel sigma I tau (a t)) ≅
        sigma.sumOver P.index P.label :=
    eqToIso (congrArg (sigma.sumOver P.index) (funext ha_eq))
  let f : (Quotient.functor I).obj (tau.sumOver P.index a) ⟶
      (Quotient.functor I).obj (tau.obj l) :=
    (inflationSumIso sigma I tau P.index a).inv ≫
      relabelIso.hom ≫ P.map ≫
        (inflationObjIso sigma I tau l).hom
  refine
    { index := P.index
      label := a
      mem := ha_mem
      map := (Quotient.functor I).preimage f
      epi := ?_ }
  letI : Epi P.map := P.epi
  haveI : Epi f := by
    dsimp only [f]
    infer_instance
  rw [IndecomposableSkeleton.fg_epi_iff_surjective]
  change Function.Surjective
    (((Quotient.functor I).map
      ((Quotient.functor I).preimage f)).hom.hom)
  rw [(Quotient.functor I).map_preimage f]
  exact
    (IndecomposableSkeleton.fg_epi_iff_surjective f).mp
      (inferInstance : Epi f)

/-- Reflect an ambient submodule presentation whose source and target labels
all belong to the factor image. -/
def reflectSubPresentation {T : Set (FactorIndex R I)}
    {l : FactorIndex R I}
    (P : sigma.SubPresentation
      ((inflationLabelEmbedding sigma I tau) '' T)
      (sigma.obj (inflationLabel sigma I tau l))) :
    tau.SubPresentation T (tau.obj l) := by
  let a : P.index → FactorIndex R I :=
    fun t ↦ Classical.choose (P.mem t)
  have ha_mem (t : P.index) : a t ∈ T :=
    (Classical.choose_spec (P.mem t)).1
  have ha_eq (t : P.index) :
      inflationLabel sigma I tau (a t) = P.label t :=
    (Classical.choose_spec (P.mem t)).2
  let relabelIso :
      sigma.sumOver P.index
          (fun t ↦ inflationLabel sigma I tau (a t)) ≅
        sigma.sumOver P.index P.label :=
    eqToIso (congrArg (sigma.sumOver P.index) (funext ha_eq))
  let f : (Quotient.functor I).obj (tau.obj l) ⟶
      (Quotient.functor I).obj (tau.sumOver P.index a) :=
    (inflationObjIso sigma I tau l).inv ≫ P.map ≫
      relabelIso.inv ≫
        (inflationSumIso sigma I tau P.index a).hom
  refine
    { index := P.index
      label := a
      mem := ha_mem
      map := (Quotient.functor I).preimage f
      mono := ?_ }
  letI : Mono P.map := P.mono
  haveI : Mono f := by
    dsimp only [f]
    infer_instance
  rw [IndecomposableSkeleton.fg_mono_iff_injective]
  change Function.Injective
    (((Quotient.functor I).map
      ((Quotient.functor I).preimage f)).hom.hom)
  rw [(Quotient.functor I).map_preimage f]
  exact
    (IndecomposableSkeleton.fg_mono_iff_injective f).mp
      (inferInstance : Mono f)

/-- Every scalar in the defining ideal kills every selected inflated factor
module. -/
theorem ideal_le_supportAnnihilator_image
    (T : Set (FactorIndex R I)) :
    I ≤ supportAnnihilator sigma.obj
      ((inflationLabelEmbedding sigma I tau) '' T) := by
  rw [supportAnnihilator_image_of_iso sigma.obj
    (inflationLabelEmbedding sigma I tau)
    (fun l ↦ (Quotient.functor I).obj (tau.obj l))
    (inflationObjIso sigma I tau) T]
  rw [Quotient.supportAnnihilator_inflation I tau.obj T]
  intro r hr
  change QuotientSubmoduleEquidistribution.AnnihilatorInflation.Quotient.map I r ∈
    supportAnnihilator tau.obj T
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  exact (supportAnnihilator tau.obj T).zero_mem

/-- Every ambient indecomposable in the quotient closure of selected inflated
factor labels is killed by the defining ideal. -/
theorem killed_of_mem_qSet_image
    {T : Set (FactorIndex R I)} {j : iota}
    (hj : j ∈ sigma.qSet
      ((inflationLabelEmbedding sigma I tau) '' T)) :
    ∀ r, r ∈ I → ∀ x : sigma.obj j, r • x = 0 := by
  intro r hr x
  have hrImage : r ∈ supportAnnihilator sigma.obj
      ((inflationLabelEmbedding sigma I tau) '' T) :=
    ideal_le_supportAnnihilator_image sigma I tau T hr
  have hrClosure : r ∈ supportAnnihilator sigma.obj
      (sigma.qSet ((inflationLabelEmbedding sigma I tau) '' T)) := by
    rw [AnnihilatorInflation.Skeleton.supportAnnihilator_qSet sigma]
    exact hrImage
  exact (mem_supportAnnihilator sigma.obj).mp hrClosure j hj x

/-- Every ambient indecomposable in the submodule closure of selected inflated
factor labels is killed by the defining ideal. -/
theorem killed_of_mem_sSet_image
    {T : Set (FactorIndex R I)} {j : iota}
    (hj : j ∈ sigma.sSet
      ((inflationLabelEmbedding sigma I tau) '' T)) :
    ∀ r, r ∈ I → ∀ x : sigma.obj j, r • x = 0 := by
  intro r hr x
  have hrImage : r ∈ supportAnnihilator sigma.obj
      ((inflationLabelEmbedding sigma I tau) '' T) :=
    ideal_le_supportAnnihilator_image sigma I tau T hr
  have hrClosure : r ∈ supportAnnihilator sigma.obj
      (sigma.sSet ((inflationLabelEmbedding sigma I tau) '' T)) := by
    rw [AnnihilatorInflation.Skeleton.supportAnnihilator_sSet sigma]
    exact hrImage
  exact (mem_supportAnnihilator sigma.obj).mp hrClosure j hj x

/-- Quotient-closure membership of an aligned label is exactly quotient-side
membership. -/
theorem inflation_mem_qSet_iff
    (T : Set (FactorIndex R I)) (l : FactorIndex R I) :
    inflationLabel sigma I tau l ∈
        sigma.qSet ((inflationLabelEmbedding sigma I tau) '' T) ↔
      l ∈ tau.qSet T := by
  constructor
  · intro hl
    exact hl.map (reflectFacPresentation sigma I tau)
  · intro hl
    exact hl.map (inflateFacPresentation sigma I tau)

/-- Submodule-closure membership of an aligned label is exactly quotient-side
membership. -/
theorem inflation_mem_sSet_iff
    (T : Set (FactorIndex R I)) (l : FactorIndex R I) :
    inflationLabel sigma I tau l ∈
        sigma.sSet ((inflationLabelEmbedding sigma I tau) '' T) ↔
      l ∈ tau.sSet T := by
  constructor
  · intro hl
    exact hl.map (reflectSubPresentation sigma I tau)
  · intro hl
    exact hl.map (inflateSubPresentation sigma I tau)

/-- Inflation identifies quotient closure on the factor skeleton with the
literal ambient quotient closure of the image. -/
theorem qSet_image (T : Set (FactorIndex R I)) :
    sigma.qSet ((inflationLabelEmbedding sigma I tau) '' T) =
      (inflationLabelEmbedding sigma I tau) '' tau.qSet T := by
  ext j
  constructor
  · intro hj
    obtain ⟨l, rfl⟩ := inflation_covers_killed_label sigma I tau
      (killed_of_mem_qSet_image sigma I tau hj)
    exact ⟨l, (inflation_mem_qSet_iff sigma I tau T l).mp hj, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact (inflation_mem_qSet_iff sigma I tau T l).mpr hl

/-- Inflation identifies submodule closure on the factor skeleton with the
literal ambient submodule closure of the image. -/
theorem sSet_image (T : Set (FactorIndex R I)) :
    sigma.sSet ((inflationLabelEmbedding sigma I tau) '' T) =
      (inflationLabelEmbedding sigma I tau) '' tau.sSet T := by
  ext j
  constructor
  · intro hj
    obtain ⟨l, rfl⟩ := inflation_covers_killed_label sigma I tau
      (killed_of_mem_sSet_image sigma I tau hj)
    exact ⟨l, (inflation_mem_sSet_iff sigma I tau T l).mp hj, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact (inflation_mem_sSet_iff sigma I tau T l).mpr hl

/-- A quotient-side `q`-closed set is closed exactly when its aligned image
is ambient `q`-closed. -/
theorem qClosed_image_iff (T : Set (FactorIndex R I)) :
    sigma.qClosure.IsClosed
        ((inflationLabelEmbedding sigma I tau) '' T) ↔
      tau.qClosure.IsClosed T := by
  rw [sigma.qClosure.isClosed_iff, tau.qClosure.isClosed_iff]
  change
    sigma.qSet ((inflationLabelEmbedding sigma I tau) '' T) =
          (inflationLabelEmbedding sigma I tau) '' T ↔
      tau.qSet T = T
  rw [qSet_image sigma I tau T]
  constructor
  · intro h
    exact
      (inflationLabelEmbedding sigma I tau).injective.image_injective h
  · intro h
    exact congrArg
      (fun U : Set (FactorIndex R I) ↦
        (inflationLabelEmbedding sigma I tau) '' U) h

/-- A quotient-side `s`-closed set is closed exactly when its aligned image
is ambient `s`-closed. -/
theorem sClosed_image_iff (T : Set (FactorIndex R I)) :
    sigma.sClosure.IsClosed
        ((inflationLabelEmbedding sigma I tau) '' T) ↔
      tau.sClosure.IsClosed T := by
  rw [sigma.sClosure.isClosed_iff, tau.sClosure.isClosed_iff]
  change
    sigma.sSet ((inflationLabelEmbedding sigma I tau) '' T) =
          (inflationLabelEmbedding sigma I tau) '' T ↔
      tau.sSet T = T
  rw [sSet_image sigma I tau T]
  constructor
  · intro h
    exact
      (inflationLabelEmbedding sigma I tau).injective.image_injective h
  · intro h
    exact congrArg
      (fun U : Set (FactorIndex R I) ↦
        (inflationLabelEmbedding sigma I tau) '' U) h

/-- The canonical factor skeleton, aligned with a complete ambient skeleton,
supplies all quotient-inflation data required by the annihilator recurrence. -/
noncomputable def inflationData :
    AnnihilatorInflation.Skeleton.InflationData sigma I tau where
  label := inflationLabelEmbedding sigma I tau
  objIso := inflationObjIso sigma I tau
  qClosed_image_iff := qClosed_image_iff sigma I tau
  sClosed_image_iff := sClosed_image_iff sigma I tau
  covers := inflation_covers sigma I tau

end Transport

/-! ## Canonical Artinian specialization -/

section ArtinTransport

variable {R : Type u} [Ring R] [IsArtinianRing R]
  {iota : Type (u + 1)}
  (sigma : IndecomposableSkeleton.{u, u + 1, u} R iota)

/-- Canonical factor alignment for an arbitrary complete ambient skeleton
over a left Artinian ring. -/
noncomputable def artinInflationData (I : TwoSidedIdeal R) :
    AnnihilatorInflation.Skeleton.InflationData sigma I
      (artinFactorSkeleton R I) :=
  inflationData sigma I (artinFactorSkeleton R I)

/-- The fully canonical ambient/factor alignment over a left Artinian
ring. -/
noncomputable def canonicalArtinInflationData (I : TwoSidedIdeal R) :
    AnnihilatorInflation.Skeleton.InflationData
      (artinSkeleton R) I (artinFactorSkeleton R I) :=
  inflationData (artinSkeleton R) I (artinFactorSkeleton R I)

end ArtinTransport

end QuotientSubmoduleEquidistribution.QuotientSkeletonAlignment
