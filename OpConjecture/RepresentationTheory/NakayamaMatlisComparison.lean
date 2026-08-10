import OpConjecture.RepresentationTheory.ArtinDTransposeExt
import OpConjecture.RepresentationTheory.ProjectivePresentationHom
import OpConjecture.RepresentationTheory.StableQuotientLinear

/-!
# Scalar Nakayama--Matlis comparison for a fixed presentation

`ArtinDuality.Data` records an additive duality of finitely generated module
categories.  It does not assert compatibility with a selected scalar ring or
identify morphisms into a Nakayama term with coefficient-valued duals of Hom
spaces.

This file supplies that missing scalar information explicitly, and only on
the two projective terms of a chosen two-step presentation.  From it we
construct the usual boundary pairing

`Hom(Y, C_P) × Hom(X, Y) ⟶ E`,

where `C_P` is the image object in the `DTr` copresentation.  The pairing
vanishes on the displayed presentation range in its first variable and on
morphisms factoring through projectives in its second variable.  It therefore
descends naturally to the presentation quotient and projective-stable Hom.

No injectivity or cogenerator property of `E` is imposed here.  In particular,
this file does not prove that the descended map is an equivalence, construct a
stable Hom--Ext duality, or use a concrete algebra or module classification.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.AuslanderTranspose.TwoStepProjectivePresentation

open OpConjecture.RingelStable

universe uk uE u

variable
    {k : Type uk} [CommRing k]
    {R : Type u} [Ring R]
    [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
    [Linear k (FGModuleCat.{u} R)]
    {X : FGModuleCat.{u} R}
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R)
    (E : Type uE) [AddCommGroup E] [Module k E]

/-- The scalar Nakayama--Matlis comparison needed on the two projective terms
of a chosen presentation.

Only the zeroth comparison must be natural in the variable module.  The first
comparison is used pointwise, through compatibility with the one differential
of the chosen presentation.  Naturality in arbitrary morphisms between
projective objects would be a stronger global interface and is not needed for
the quotient construction below. -/
structure TwoStepNakayamaMatlisComparison where
  equiv₀ :
    ∀ Y : FGModuleCat.{u} R,
      (Y ⟶ P.nakayamaP₀ D) ≃ₗ[k]
        ((P.augmentation.p ⟶ Y) →ₗ[k] E)
  equiv₁ :
    ∀ Y : FGModuleCat.{u} R,
      (Y ⟶ P.nakayamaP₁ D) ≃ₗ[k]
        ((P.syzygyPresentation.p ⟶ Y) →ₗ[k] E)
  naturality₀ :
    ∀ {Y Z : FGModuleCat.{u} R} (g : Y ⟶ Z)
      (a : Z ⟶ P.nakayamaP₀ D) (f : P.augmentation.p ⟶ Y),
      equiv₀ Y (g ≫ a) f = equiv₀ Z a (f ≫ g)
  differential :
    ∀ (Y : FGModuleCat.{u} R)
      (a : Y ⟶ P.nakayamaP₁ D) (f : P.augmentation.p ⟶ Y),
      equiv₀ Y (a ≫ P.dTransposeNext D) f =
        equiv₁ Y a (P.differential ≫ f)

namespace TwoStepNakayamaMatlisComparison

variable {P D E}

/-- The Nakayama--Matlis boundary pairing before quotienting either
variable. -/
def ordinaryBoundaryLinear
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R) :
    (Y ⟶ P.dTransposeCokernel D) →ₗ[k]
      ((X ⟶ Y) →ₗ[k] E) :=
  (LinearMap.lcomp k E (P.augmentationPrecompLinear (k := k) Y)).comp
    ((N.equiv₀ Y).toLinearMap.comp
      (CategoryTheory.Linear.rightComp k Y (P.dTransposeCokernelι D)))

@[simp]
theorem ordinaryBoundaryLinear_apply
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R)
    (c : Y ⟶ P.dTransposeCokernel D) (f : X ⟶ Y) :
    N.ordinaryBoundaryLinear Y c f =
      N.equiv₀ Y (c ≫ P.dTransposeCokernelι D)
        (P.augmentation.f ≫ f) := by
  rfl

/-- Naturality of the unquotiented pairing in the variable module. -/
theorem ordinaryBoundaryLinear_naturality
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    {Y Z : FGModuleCat.{u} R} (g : Y ⟶ Z)
    (c : Z ⟶ P.dTransposeCokernel D) (f : X ⟶ Y) :
    N.ordinaryBoundaryLinear Y (g ≫ c) f =
      N.ordinaryBoundaryLinear Z c (f ≫ g) := by
  exact N.naturality₀ g (c ≫ P.dTransposeCokernelι D)
    (P.augmentation.f ≫ f)

/-- The pairing kills the displayed image of
`Hom(Y, νP₁) ⟶ Hom(Y, C_P)`. -/
theorem ordinaryBoundaryLinear_eq_zero_of_mem_presentationRange
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R)
    (c : Y ⟶ P.dTransposeCokernel D)
    (hc : c ∈ P.dTransposeExtPresentationRange (k := k) D Y) :
    N.ordinaryBoundaryLinear Y c = 0 := by
  obtain ⟨a, rfl⟩ :=
    (P.mem_dTransposeExtPresentationRange_iff (k := k) D Y c).mp hc
  apply LinearMap.ext
  intro f
  rw [ordinaryBoundaryLinear_apply, Category.assoc,
    P.dTransposeCokernelπ_comp_ι]
  rw [N.differential]
  rw [← Category.assoc, P.differential_comp_augmentation]
  simp

/-- The pairing kills every morphism from `X` which factors through a
projective object. -/
theorem ordinaryBoundaryLinear_apply_eq_zero_of_factorsThroughProjective
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R)
    (c : Y ⟶ P.dTransposeCokernel D)
    {f : X ⟶ Y} (hf : FactorsThroughProjective f) :
    N.ordinaryBoundaryLinear Y c f = 0 := by
  letI : Projective hf.middle := hf.projective
  let a : hf.middle ⟶ P.nakayamaP₁ D :=
    Projective.factorThru (hf.right ≫ c) (P.dTransposeCokernelπ D)
  have ha : a ≫ P.dTransposeCokernelπ D = hf.right ≫ c := by
    exact Projective.factorThru_comp _ _
  rw [ordinaryBoundaryLinear_apply, ← hf.fac, ← Category.assoc]
  rw [← N.naturality₀ hf.right
    (c ≫ P.dTransposeCokernelι D)
    (P.augmentation.f ≫ hf.left)]
  rw [← Category.assoc, ← ha, Category.assoc,
    P.dTransposeCokernelπ_comp_ι]
  rw [N.differential]
  rw [← Category.assoc, P.differential_comp_augmentation]
  simp

section Quotients

variable
    [Linear k (ProjectiveStableCategory (R := R))]
    [Functor.Linear k (projectiveStableFunctor (R := R))]

/-- The pairing with a fixed presentation representative, descended across
projective factorizations in its second argument. -/
def stableQuotientBoundary
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R)
    (c : Y ⟶ P.dTransposeCokernel D) :
    ((X ⟶ Y) ⧸
        ProjectiveStableScalar.factorsThroughProjectiveSubmodule k R X Y)
      →ₗ[k] E :=
  (ProjectiveStableScalar.factorsThroughProjectiveSubmodule k R X Y).liftQ
    (N.ordinaryBoundaryLinear Y c) (by
      intro f hf
      rw [LinearMap.mem_ker]
      obtain ⟨hf⟩ :=
        (ProjectiveStableScalar.mem_factorsThroughProjectiveSubmodule_iff
          k R f).mp hf
      exact N.ordinaryBoundaryLinear_apply_eq_zero_of_factorsThroughProjective
        Y c hf)

@[simp]
theorem stableQuotientBoundary_mk
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R)
    (c : Y ⟶ P.dTransposeCokernel D) (f : X ⟶ Y) :
    N.stableQuotientBoundary Y c (Submodule.Quotient.mk f) =
      N.ordinaryBoundaryLinear Y c f := by
  rfl

/-- The pairing, linear in its first argument after quotienting the second. -/
def stableQuotientBoundaryLinear
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R) :
    (Y ⟶ P.dTransposeCokernel D) →ₗ[k]
      (((X ⟶ Y) ⧸
          ProjectiveStableScalar.factorsThroughProjectiveSubmodule k R X Y)
        →ₗ[k] E) where
  toFun := N.stableQuotientBoundary Y
  map_add' c c' := by
    apply LinearMap.ext
    intro q
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    simp [stableQuotientBoundary_mk]
  map_smul' a c := by
    apply LinearMap.ext
    intro q
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    simp [stableQuotientBoundary_mk]

/-- The pairing descended across the presentation range in its first
argument as well. -/
def boundaryQuotientLinear
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R) :
    ((Y ⟶ P.dTransposeCokernel D) ⧸
        P.dTransposeExtPresentationRange (k := k) D Y) →ₗ[k]
      (((X ⟶ Y) ⧸
          ProjectiveStableScalar.factorsThroughProjectiveSubmodule k R X Y)
        →ₗ[k] E) :=
  (P.dTransposeExtPresentationRange (k := k) D Y).liftQ
    (N.stableQuotientBoundaryLinear Y) (by
      intro c hc
      rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro q
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      exact LinearMap.congr_fun
        (N.ordinaryBoundaryLinear_eq_zero_of_mem_presentationRange Y c hc) f)

@[simp]
theorem boundaryQuotientLinear_mk_mk
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R)
    (c : Y ⟶ P.dTransposeCokernel D) (f : X ⟶ Y) :
    N.boundaryQuotientLinear Y (Submodule.Quotient.mk c)
        (Submodule.Quotient.mk f) =
      N.ordinaryBoundaryLinear Y c f := by
  rfl

/-- Transport the explicit quotient dual to the selected scalar-linear
projective-stable Hom space. -/
def boundaryStableLinear
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R) :
    ((Y ⟶ P.dTransposeCokernel D) ⧸
        P.dTransposeExtPresentationRange (k := k) D Y) →ₗ[k]
      (((projectiveStableFunctor (R := R)).obj X ⟶
          (projectiveStableFunctor (R := R)).obj Y) →ₗ[k] E) :=
  (LinearEquiv.congrLeft E k
      (ProjectiveStableScalar.homQuotientLinearEquiv k R X Y)).toLinearMap.comp
    (N.boundaryQuotientLinear Y)

@[simp]
theorem boundaryStableLinear_mk_map
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    (Y : FGModuleCat.{u} R)
    (c : Y ⟶ P.dTransposeCokernel D) (f : X ⟶ Y) :
    N.boundaryStableLinear Y (Submodule.Quotient.mk c)
        ((projectiveStableFunctor (R := R)).map f) =
      N.ordinaryBoundaryLinear Y c f := by
  simp [boundaryStableLinear]

/-- The descended pairing has exactly the contravariant/covariant variance
required by `StableHomExtLinearDuality`. -/
theorem boundaryStableLinear_naturality
    (N : TwoStepNakayamaMatlisComparison (k := k) P D E)
    {Y Z : FGModuleCat.{u} R} (g : Y ⟶ Z)
    (q : (Z ⟶ P.dTransposeCokernel D) ⧸
      P.dTransposeExtPresentationRange (k := k) D Z)
    (a : (projectiveStableFunctor (R := R)).obj X ⟶
      (projectiveStableFunctor (R := R)).obj Y) :
    N.boundaryStableLinear Y
        (P.dTransposePrecompQuotient (k := k) D g q) a =
      N.boundaryStableLinear Z q
        (a ≫ (projectiveStableFunctor (R := R)).map g) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨f, rfl⟩ :=
    ProjectiveStableScalar.mapLinear_surjective k R a
  change
    N.boundaryStableLinear Y (Submodule.Quotient.mk (g ≫ c))
        ((projectiveStableFunctor (R := R)).map f) =
      N.boundaryStableLinear Z (Submodule.Quotient.mk c)
        ((projectiveStableFunctor (R := R)).map f ≫
          (projectiveStableFunctor (R := R)).map g)
  rw [← (projectiveStableFunctor (R := R)).map_comp]
  rw [N.boundaryStableLinear_mk_map, N.boundaryStableLinear_mk_map]
  exact N.ordinaryBoundaryLinear_naturality g c f

end Quotients

end TwoStepNakayamaMatlisComparison

end OpConjecture.AuslanderTranspose.TwoStepProjectivePresentation
