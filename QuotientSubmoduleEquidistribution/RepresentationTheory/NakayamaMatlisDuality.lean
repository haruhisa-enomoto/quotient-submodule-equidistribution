import QuotientSubmoduleEquidistribution.RepresentationTheory.CoefficientDual
import QuotientSubmoduleEquidistribution.RepresentationTheory.NakayamaMatlisComparison
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectivePresentationHom
import QuotientSubmoduleEquidistribution.RepresentationTheory.StableHomExtLinearDuality

/-!
# Stable Hom--Ext duality from a Nakayama--Matlis comparison

For a chosen two-step projective presentation, the scalar comparison in
`NakayamaMatlisComparison` defines a boundary pairing between the quotient
computing `Ext¹(-, DTr_P X)` and the coefficient dual of projective-stable
`Hom(X,-)`.

This file proves that the pairing is an equivalence when its coefficient
module is injective.  Injectivity is used twice: to identify the kernel of
the dual presentation map and to extend a stable-Hom functional across the
augmentation.  Surjectivity then uses an arbitrary projective epimorphism
onto the target module.  No cogenerator or reflexivity hypothesis, minimal
projective presentation, concrete algebra, or module classification occurs.

Composing with the injective-presentation computation of `Ext¹` gives the
presentation-dependent scalar stable Hom--Ext duality for `DTr_P X`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace QuotientSubmoduleEquidistribution.AuslanderTranspose.TwoStepProjectivePresentation

open QuotientSubmoduleEquidistribution.RingelStable

universe uk uE w u

variable
    {k : Type uk} [CommRing k]
    {R : Type u} [Ring R]
    [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
    [Linear k (FGModuleCat.{u} R)]
    {X : FGModuleCat.{u} R}
    (P : TwoStepProjectivePresentation X)
    (D : QuotientSubmoduleEquidistribution.ArtinDuality.Data R)
    (E : Type uE) [AddCommGroup E] [Module k E]

namespace TwoStepNakayamaMatlisComparison

variable {P D E}
  [Small.{uE} k] [Module.Injective k E]

/-- Before quotienting the boundary variable, the kernel of the pairing is
exactly the displayed image of `Hom(Y,νP₁)`. -/
theorem ker_ordinaryBoundaryLinear
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R) :
    LinearMap.ker (N.ordinaryBoundaryLinear Y) =
      P.dTransposeExtPresentationRange (k := k) D Y := by
  apply le_antisymm
  · intro c hc
    let phi : (P.augmentation.p ⟶ Y) →ₗ[k] E :=
      N.equiv₀ Y (c ≫ P.dTransposeCokernelι D)
    have hphi : phi ∈ QuotientSubmoduleEquidistribution.CoefficientDual.annihilator (E := E)
        (LinearMap.ker (P.differentialPrecompLinear (k := k) Y)) := by
      rw [← P.range_augmentationPrecompLinear (k := k) Y]
      rw [QuotientSubmoduleEquidistribution.CoefficientDual.mem_annihilator_iff]
      intro f hf
      obtain ⟨g, rfl⟩ := hf
      have hz := LinearMap.congr_fun (LinearMap.mem_ker.mp hc) g
      exact hz
    have hphiRange : phi ∈ LinearMap.range
        (LinearMap.lcomp k E (P.differentialPrecompLinear (k := k) Y)) := by
      rw [QuotientSubmoduleEquidistribution.CoefficientDual.range_lcomp_eq_annihilator_ker]
      exact hphi
    obtain ⟨psi, hpsi⟩ := hphiRange
    let a : Y ⟶ P.nakayamaP₁ D := (N.equiv₁ Y).symm psi
    have ha : a ≫ P.dTransposeNext D =
        c ≫ P.dTransposeCokernelι D := by
      apply (N.equiv₀ Y).injective
      apply LinearMap.ext
      intro f
      rw [N.differential]
      have hvalue := LinearMap.congr_fun hpsi f
      simpa [a, phi, differentialPrecompLinear, LinearMap.lcomp_apply]
        using hvalue
    rw [P.mem_dTransposeExtPresentationRange_iff (k := k) D Y]
    refine ⟨a, ?_⟩
    apply (cancel_mono (P.dTransposeCokernelι D)).1
    rw [Category.assoc, P.dTransposeCokernelπ_comp_ι]
    exact ha
  · intro c hc
    rw [LinearMap.mem_ker]
    exact N.ordinaryBoundaryLinear_eq_zero_of_mem_presentationRange Y c hc

variable
  [Linear k (ProjectiveStableCategory (R := R))]
  [Functor.Linear k (projectiveStableFunctor (R := R))]

/-- The descended boundary pairing is injective. -/
theorem boundaryStableLinear_injective
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R) :
    Function.Injective (N.boundaryStableLinear Y) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [Submodule.Quotient.mk_eq_zero]
  rw [← N.ker_ordinaryBoundaryLinear Y]
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro f
  have hvalue := LinearMap.congr_fun hq
    ((projectiveStableFunctor (R := R)).map f)
  simpa using hvalue

/-- Every coefficient-valued functional on stable Hom is represented by a
boundary element. -/
theorem boundaryStableLinear_surjective
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R) :
    Function.Surjective (N.boundaryStableLinear Y) := by
  intro lambda
  let phiX : (X ⟶ Y) →ₗ[k] E :=
    lambda.comp (ProjectiveStableScalar.mapLinear k R)
  obtain ⟨phi₀, hphi₀⟩ := Module.Injective.extension_property k E
    (X ⟶ Y) (P.augmentation.p ⟶ Y)
    (P.augmentationPrecompLinear (k := k) Y)
    (P.augmentationPrecompLinear_injective (k := k) Y) phiX
  let a₀ : Y ⟶ P.nakayamaP₀ D := (N.equiv₀ Y).symm phi₀
  let Q : ProjectivePresentation Y := (EnoughProjectives.presentation Y).some
  let psi₀ : (P.augmentation.p ⟶ Q.p) →ₗ[k] E :=
    N.equiv₀ Q.p (Q.f ≫ a₀)
  have hpsi₀ : psi₀ ∈ QuotientSubmoduleEquidistribution.CoefficientDual.annihilator (E := E)
      (LinearMap.ker (P.differentialPrecompLinear (k := k) Q.p)) := by
    rw [← P.range_augmentationPrecompLinear (k := k) Q.p]
    rw [QuotientSubmoduleEquidistribution.CoefficientDual.mem_annihilator_iff]
    intro b hb
    obtain ⟨f, rfl⟩ := hb
    have hstable : ProjectiveStableScalar.mapLinear k R (f ≫ Q.f) = 0 := by
      rw [ProjectiveStableScalar.mapLinear_eq_zero_iff]
      exact ⟨{
        middle := Q.p
        projective := Q.projective
        left := f
        right := Q.f
        fac := rfl }⟩
    calc
      psi₀ (P.augmentationPrecompLinear (k := k) Q.p f) =
          N.equiv₀ Y a₀ ((P.augmentation.f ≫ f) ≫ Q.f) := by
        exact N.naturality₀ Q.f a₀ (P.augmentation.f ≫ f)
      _ = phi₀ (P.augmentationPrecompLinear (k := k) Y (f ≫ Q.f)) := by
        simp only [a₀, LinearEquiv.apply_symm_apply,
          augmentationPrecompLinear_apply, Category.assoc]
      _ = phiX (f ≫ Q.f) := LinearMap.congr_fun hphi₀ (f ≫ Q.f)
      _ = lambda (ProjectiveStableScalar.mapLinear k R (f ≫ Q.f)) := rfl
      _ = 0 := by rw [hstable, map_zero]
  have hpsi₀Range : psi₀ ∈ LinearMap.range
      (LinearMap.lcomp k E (P.differentialPrecompLinear (k := k) Q.p)) := by
    rw [QuotientSubmoduleEquidistribution.CoefficientDual.range_lcomp_eq_annihilator_ker]
    exact hpsi₀
  obtain ⟨psi₁, hpsi₁⟩ := hpsi₀Range
  let a₁ : Q.p ⟶ P.nakayamaP₁ D := (N.equiv₁ Q.p).symm psi₁
  have ha₁ : a₁ ≫ P.dTransposeNext D = Q.f ≫ a₀ := by
    apply (N.equiv₀ Q.p).injective
    apply LinearMap.ext
    intro f
    rw [N.differential]
    have hvalue := LinearMap.congr_fun hpsi₁ f
    simpa [a₁, psi₀, differentialPrecompLinear,
      LinearMap.lcomp_apply] using hvalue
  have ha₀zero : a₀ ≫ cokernel.π (P.dTransposeCokernelι D) = 0 := by
    apply (cancel_epi Q.f).1
    simp only [comp_zero]
    calc
      Q.f ≫ a₀ ≫ cokernel.π (P.dTransposeCokernelι D) =
          (Q.f ≫ a₀) ≫ cokernel.π (P.dTransposeCokernelι D) :=
        (Category.assoc _ _ _).symm
      _ = (a₁ ≫ P.dTransposeNext D) ≫
          cokernel.π (P.dTransposeCokernelι D) := by rw [ha₁]
      _ = 0 := by
        rw [← P.dTransposeCokernelπ_comp_ι]
        simp only [Category.assoc, cokernel.condition, comp_zero]
  let c : Y ⟶ P.dTransposeCokernel D :=
    Abelian.monoLift (P.dTransposeCokernelι D) a₀ ha₀zero
  refine ⟨Submodule.Quotient.mk c, ?_⟩
  apply LinearMap.ext
  intro a
  obtain ⟨f, rfl⟩ := ProjectiveStableScalar.mapLinear_surjective k R a
  change N.boundaryStableLinear Y (Submodule.Quotient.mk c)
      ((projectiveStableFunctor (R := R)).map f) =
    lambda ((projectiveStableFunctor (R := R)).map f)
  rw [N.boundaryStableLinear_mk_map]
  rw [N.ordinaryBoundaryLinear_apply]
  rw [show c ≫ P.dTransposeCokernelι D = a₀ by
    exact Abelian.monoLift_comp _ _ _]
  rw [show N.equiv₀ Y a₀ = phi₀ by simp [a₀]]
  exact LinearMap.congr_fun hphi₀ f

/-- The boundary pairing is bijective for an injective coefficient module. -/
theorem boundaryStableLinear_bijective
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R) :
    Function.Bijective (N.boundaryStableLinear Y) :=
  ⟨N.boundaryStableLinear_injective Y,
    N.boundaryStableLinear_surjective Y⟩

/-- The quotient computing `Ext¹(Y,DTr_P X)` is the coefficient dual of
projective-stable `Hom(X,Y)`. -/
def boundaryStableLinearEquiv
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R) :
    ((Y ⟶ P.dTransposeCokernel D) ⧸
        P.dTransposeExtPresentationRange (k := k) D Y) ≃ₗ[k]
      (((projectiveStableFunctor (R := R)).obj X ⟶
          (projectiveStableFunctor (R := R)).obj Y) →ₗ[k] E) :=
  LinearEquiv.ofBijective (N.boundaryStableLinear Y)
    (N.boundaryStableLinear_bijective Y)

section Ext

variable [HasExt.{w} (FGModuleCat.{u} R)]

/-- A fixed-presentation Nakayama--Matlis comparison gives the scalar stable
Auslander--Reiten formula for the associated object `DTr_P X`. -/
def toStableHomExtLinearDuality
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E) :
    QuotientSubmoduleEquidistribution.StableHomExtLinearDuality (k := k)
      (projectiveStableFunctor (R := R)) X (P.dTranspose D) E where
  equiv Y :=
    (P.dTransposeExtOneQuotientLinearEquiv (k := k) D Y).symm.trans
      (N.boundaryStableLinearEquiv Y)
  naturality := by
    intro Y Z a g xi
    rw [LinearEquiv.trans_apply]
    rw [P.dTransposeExtOneQuotientLinearEquiv_symm_pullback]
    exact N.boundaryStableLinear_naturality g
      ((P.dTransposeExtOneQuotientLinearEquiv (k := k) D Z).symm xi) a

end Ext

end TwoStepNakayamaMatlisComparison

end QuotientSubmoduleEquidistribution.AuslanderTranspose.TwoStepProjectivePresentation
