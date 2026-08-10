import OpConjecture.RepresentationTheory.ConnectedSmallCoreHereditary
import OpConjecture.RepresentationTheory.ProjectiveRadicalExt
import OpConjecture.RepresentationTheory.ProjectiveSimpleRecognition
import OpConjecture.RepresentationTheory.RingelEtaCoreCardinality

/-!
# Finite heredity excludes simple self-extensions

For a finite complete indecomposable skeleton, finite left heredity forces
`Ext¹(S,S) = 0` for every simple module `S`.  The proof uses no quiver
presentation or concrete module classification.  A hypothetical nonzero
self-extension makes the corresponding indecomposable projective occur as
a direct summand of its own radical; the resulting monic endomorphism is an
isomorphism by finite length, contradicting properness of the radical.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.HereditaryNoSelfExt

universe u v

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

open OpConjecture.GabrielArrowBridge
open OpConjecture.IndecomposableSkeleton
open OpConjecture.IndecomposableSkeleton.FaithfulCore
open OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore
open OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank

variable {K R : Type u}
  [Field K]
  [Ring R] [Small.{u} R] [Algebra K R] [IsNoetherianRing R]
  {iota : Type v}
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)

include K in
/-- Over a finite-left-hereditary ring, every simple module represented in
the complete skeleton has vanishing degree-one self-extension
space. -/
theorem selfExtOne_subsingleton_of_finitelyGeneratedLeftHereditary
    (hHereditary : FinitelyGeneratedLeftHereditary R)
    (s : sigma.SimpleIndex) :
    Subsingleton (ExtOne sigma s s) := by
  let p : ProjectiveIndex sigma :=
    (projectiveIndexEquivSimpleIndex sigma).symm s
  have hpTop : projectiveTopIndex sigma p = s :=
    (projectiveIndexEquivSimpleIndex sigma).apply_symm_apply s
  let eTopCat : projectiveTop sigma p ≅ sigma.obj s.1 :=
    projectiveTopIso sigma p ≪≫
      eqToIso (congrArg (fun t : sigma.SimpleIndex ↦ sigma.obj t.1) hpTop)
  let eTop :
      (sigma.obj p.1 ⧸ Module.jacobson R (sigma.obj p.1)) ≃ₗ[R]
        sigma.obj s.1 :=
    FGModuleCat.isoToLinearEquiv eTopCat
  letI : CategoryTheory.Projective (sigma.obj p.1) := p.2
  letI : Module.Projective R (sigma.obj p.1) :=
    moduleProjective_of_fgProjective (sigma.obj p.1) p.2
  letI : CategoryTheory.Projective
      (ModuleCat.of R (sigma.obj p.1)) := inferInstance
  letI : Simple (sigma.obj s.1) := s.2
  letI : IsSimpleModule R (sigma.obj s.1) :=
    (simple_iff_isSimpleModule_fg (sigma.obj s.1)).mp s.2
  let radicalExt :=
    OpConjecture.ProjectiveRadicalExt.radicalHomLinearEquivExtOne
      (K := K) (R := R)
      (P := sigma.obj p.1) (S := sigma.obj s.1) (T := sigma.obj s.1)
      eTop
  constructor
  intro x y
  suffices hz : ∀ z : ExtOne sigma s s, z = 0 by
    exact (hz x).trans (hz y).symm
  intro z
  apply radicalExt.symm.injective
  rw [map_zero]
  let J : Submodule R (sigma.obj p.1) := sigma.moduleRadical p.1
  let Jfg : FGModuleCat.{u} R := FGModuleCat.of R J
  let fMod : ModuleCat.of R J ⟶ ModuleCat.of R (sigma.obj s.1) :=
    radicalExt.symm z
  let f : Jfg ⟶ sigma.obj s.1 := FGModuleCat.ofHom fMod.hom
  by_contra hfMod
  have hf : f ≠ 0 := by
    intro hzero
    apply hfMod
    apply ModuleCat.hom_ext
    have hzero' :=
      congrArg (fun q : Jfg ⟶ sigma.obj s.1 ↦ q.hom.hom) hzero
    dsimp only [f] at hzero'
    exact hzero'
  have hJModuleProjective : Module.Projective R J :=
    hHereditary (sigma.obj p.1) p.2 J
  have hJProjective : CategoryTheory.Projective Jfg :=
    OpConjecture.RingelStable.fgProjective_of_moduleProjective
      Jfg hJModuleProjective
  obtain ⟨D⟩ :=
    OpConjecture.RingelStable.FaithfulCoreAdapter.inAdd_projectiveLabels_of_projective
      sigma Jfg hJProjective
  let g : sigma.sumOver D.index D.label ⟶ sigma.obj s.1 :=
    D.iso.inv ≫ f
  haveI : Epi f := epi_of_nonzero_to_simple hf
  haveI : Epi g := by
    dsimp [g]
    infer_instance
  have hg : g ≠ 0 := by
    intro hzero
    exact Simple.not_isZero (sigma.obj s.1)
      (IsZero.of_epi_eq_zero g hzero)
  have hcomponent :
      ∃ t : D.index,
        biproduct.ι (fun a : D.index ↦ sigma.obj (D.label a)) t ≫ g ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    apply biproduct.hom_ext'
    intro t
    exact h t
  obtain ⟨t, ht⟩ := hcomponent
  let c : sigma.obj (D.label t) ⟶ sigma.obj s.1 :=
    biproduct.ι (fun a : D.index ↦ sigma.obj (D.label a)) t ≫ g
  have hc : c ≠ 0 := ht
  letI : Epi c := epi_of_nonzero_to_simple hc
  obtain ⟨eP⟩ :=
    projective_iso_of_indec_of_epi_to_simple sigma
      (sigma.obj (D.label t)) (D.mem t)
      (sigma.indecomposable (D.label t)) s c
  let inclusion : Jfg ⟶ sigma.obj p.1 :=
    FGModuleCat.ofHom J.subtype
  haveI : Mono inclusion := by
    apply (fg_mono_iff_injective inclusion).mpr
    exact J.subtype_injective
  let componentIntoRadical : sigma.obj (D.label t) ⟶ Jfg :=
    biproduct.ι (fun a : D.index ↦ sigma.obj (D.label a)) t ≫
      D.iso.inv
  haveI : Mono componentIntoRadical := by
    dsimp [componentIntoRadical]
    infer_instance
  let m : sigma.obj (D.label t) ⟶ sigma.obj p.1 :=
    componentIntoRadical ≫ inclusion
  haveI : Mono m := by
    dsimp [m]
    infer_instance
  let endo : sigma.obj p.1 ⟶ sigma.obj p.1 := eP.inv ≫ m
  haveI : Mono endo := by
    dsimp [endo]
    infer_instance
  letI : IsIso endo :=
    sigma.isIso_of_mono_of_compositionLength_eq endo rfl
  haveI : Epi endo := inferInstance
  let before : sigma.obj p.1 ⟶ Jfg := eP.inv ≫ componentIntoRadical
  have hfactor : before ≫ inclusion = endo := by
    simp only [before, endo, m, Category.assoc]
  letI : Epi inclusion := epi_of_epi_fac hfactor
  have hinclusionSurjective : Function.Surjective inclusion.hom.hom :=
    (fg_epi_iff_surjective inclusion).mp inferInstance
  have hJtop : J = ⊤ := by
    apply top_unique
    intro x _hx
    obtain ⟨y, hy⟩ := hinclusionSurjective x
    rw [← hy]
    exact y.2
  letI : Nontrivial (sigma.obj p.1) :=
    (sigma.indecomposable p.1).nontrivial
  exact (Module.jacobson_lt_top R (sigma.obj p.1)).ne hJtop

end OpConjecture.HereditaryNoSelfExt
