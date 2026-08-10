import OpConjecture.RepresentationTheory.ArtinFaithfulCore
import OpConjecture.RepresentationTheory.GenericArtinStableDescent
import OpConjecture.RepresentationTheory.RingelCoreEquivalence

/-!
# Abstract Artin duality interface

Mathlib does not currently construct the usual duality on finite modules
over an arbitrary Artin algebra.  This file records that finite-module
anti-equivalence as the sole input.  Generic stable descent constructs its
torsionless/cotorsionless stable equivalence automatically.  The same input
also supplies a finite injective cogenerator and the projective--injective
boundary used in Ringel's correspondence.

The interface is instantiated below by the maintained finite-dimensional
vector-space duality.  It can also be supplied directly for an Artin
algebra over a general commutative Artinian base.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Set

namespace OpConjecture.ArtinDuality

universe u v

open OpConjecture.IndecomposableSkeleton
open OpConjecture.IndecomposableSkeleton.FaithfulCore
open OpConjecture.RingelStable
open OpConjecture.RingelStable.FaithfulCoreAdapter

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable {R : Type u} [Ring R]

/-- The sole Artin-duality input used by the general proof: an
anti-equivalence of finite module categories. -/
structure Data (R : Type u) [Ring R] where
  moduleEquiv :
    (FGModuleCat.{u} Rᵐᵒᵖ)ᵒᵖ ≌ FGModuleCat.{u} R

/-- Stable Artin duality is a theorem of the finite-module
anti-equivalence, not an additional field of the interface. -/
def Data.stableEquiv (D : Data R) :
    (TorsionlessStableCategory (R := Rᵐᵒᵖ))ᵒᵖ ≌
      CotorsionlessStableCategory (R := R) :=
  torsionlessCotorsionlessStableEquivalence D.moduleEquiv

/-- The image of the right regular module under finite-module duality. -/
abbrev dualRegular (D : Data R) : FGModuleCat.{u} R :=
  D.moduleEquiv.functor.obj
    (Opposite.op (regularFGModule (R := Rᵐᵒᵖ)))

/-- An abstract finite-module anti-equivalence carries a finite sum of
right regular modules to the corresponding finite sum of dual regular
modules. -/
def dualRegularSumIso (D : Data R) (L : FintypeCat.{0}) :
    D.moduleEquiv.functor.obj
        (Opposite.op
          (⨁ fun _ : L ↦ regularFGModule (R := Rᵐᵒᵖ))) ≅
      ⨁ fun _ : L ↦ dualRegular D :=
  D.moduleEquiv.functor.mapIso
      ((biproduct.isoCoproduct
        (fun _ : L ↦ regularFGModule (R := Rᵐᵒᵖ))).op.symm ≪≫
        opCoproductIsoProduct
          (fun _ : L ↦ regularFGModule (R := Rᵐᵒᵖ))) ≪≫
    PreservesProduct.iso D.moduleEquiv.functor
      (fun _ : L ↦ Opposite.op (regularFGModule (R := Rᵐᵒᵖ))) ≪≫
    (biproduct.isoProduct (fun _ : L ↦ dualRegular D)).symm

/-- The abstract dual regular module is injective. -/
theorem injective_dualRegular (D : Data R) :
    Injective (dualRegular D) := by
  have hP : Projective (regularFGModule (R := Rᵐᵒᵖ)) :=
    projective_regularFGModule (R := Rᵐᵒᵖ)
  have hPop :
      Injective (Opposite.op (regularFGModule (R := Rᵐᵒᵖ))) :=
    Injective.projective_iff_injective_op.mp hP
  exact (D.moduleEquiv.map_injective_iff _).2 hPop

variable [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]

/-- Every finite left module embeds into a finite sum of copies of the
abstract dual regular module. -/
theorem dualRegular_cogenerates (D : Data R)
    (X : FGModuleCat.{u} R) :
    InSubOfModule (dualRegular D) X := by
  let NX : FGModuleCat.{u} Rᵐᵒᵖ :=
    (D.moduleEquiv.inverse.obj X).unop
  obtain ⟨L, p, hp⟩ :=
    regularFGModule_generates (R := Rᵐᵒᵖ) NX
  letI : Epi p := hp
  let dp := D.moduleEquiv.functor.map p.op
  letI : Mono p.op := inferInstance
  letI : Mono dp := by
    dsimp only [dp]
    infer_instance
  let intoDual := (D.moduleEquiv.counitIso.app X).inv
  let out := (dualRegularSumIso D L).hom
  letI : Mono intoDual := by
    dsimp only [intoDual]
    infer_instance
  letI : Mono out := by
    dsimp only [out]
    infer_instance
  let m : X ⟶ (⨁ fun _ : L ↦ dualRegular D) :=
    intoDual ≫ dp ≫ out
  refine ⟨L, m, ?_⟩
  apply (fg_mono_iff_injective m).2
  intro x y hxy
  have hinto : Function.Injective intoDual.hom.hom :=
    (fg_mono_iff_injective intoDual).1 inferInstance
  have hdp : Function.Injective dp.hom.hom :=
    (fg_mono_iff_injective dp).1 inferInstance
  have hout : Function.Injective out.hom.hom :=
    (fg_mono_iff_injective out).1 inferInstance
  exact hinto (hdp (hout hxy))

/-- Every abstract finite-module duality supplies the finite injective
cogenerator needed by the faithful-core theorem. -/
theorem dualRegularCogeneratorData (D : Data R) :
    FiniteInjectiveCogeneratorData (R := R) (dualRegular D) where
  injective := injective_dualRegular D
  cogenerates := dualRegular_cogenerates D

/-- The Artinian faithful-core normal form obtained from abstract Artin
duality. -/
theorem faithfulNormalForm [IsArtinianRing R]
    (D : Data R)
    {ι : Type v}
    (σ : IndecomposableSkeleton.{u, v, u} R ι) :
    ClosedFaithfulNormalForm σ
      (OpConjecture.AnnihilatorInflation.IsFaithfulSupport σ.obj)
      (OpConjecture.AnnihilatorInflation.IsFaithfulSupport σ.obj) :=
  closedFaithfulNormalForm_of_artinian σ (dualRegular D)
    (dualRegularCogeneratorData D)

/-- Compose Ringel's strong-Hom anti-equivalence with the supplied stable
Artin duality. -/
def ringelEtaStableEquivalence (D : Data R) :
    TorsionlessStableCategory (R := R) ≌
      CotorsionlessStableCategory (R := R) :=
  (OpConjecture.RingelEta.ringelTorsionlessStableAntiEquivalence
      (OpConjecture.RingelEta.regularHomProjectiveAntiEquivalence
        (R := R))).rightOp |>.trans D.stableEquiv

/-- The finite-module anti-equivalence supplies the projective--injective
boundary pairing on any chosen indecomposable skeleton. -/
def projectiveInjectiveLabelEquiv (D : Data R)
    {ι : Type v}
    (σ : IndecomposableSkeleton.{u, v, u} R ι) :
    {i // i ∈ projectiveSet σ} ≃ {i // i ∈ injectiveSet σ} :=
  OpConjecture.RingelStable.projectiveInjectiveLabelEquivOfAntiEquivalence
    σ D.moduleEquiv

/-- Abstract Ringel correspondence for an Artinian setting equipped with
the two standard Artin-duality equivalences. -/
def ringelCoreEquiv (D : Data R)
    {ι : Type v}
    (σ : IndecomposableSkeleton.{u, v, u} R ι) :
    {i // i ∈ (submoduleCore σ : Set ι)} ≃
      {i // i ∈ (quotientCore σ : Set ι)} :=
  OpConjecture.RingelStable.coreEquivOfEtaStableData σ
    (projectiveInjectiveLabelEquiv D σ)
    (etaStableDataOfAmbientEquivalence σ
      (ringelEtaStableEquivalence D))

/-- The maintained vector-space duality is an instance of the abstract
interface. -/
def ofFiniteDimensional
    (K : Type u) [Field K] [Algebra K R] [FiniteDimensional K R] :
    Data R where
  moduleEquiv :=
    OpConjecture.Contragredient.reverseDualityEquivalence K R

end OpConjecture.ArtinDuality
