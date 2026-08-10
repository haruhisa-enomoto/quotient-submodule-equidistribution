import QuotientSubmoduleEquidistribution.RepresentationTheory.AuslanderTranspose
import Mathlib.CategoryTheory.Linear.Basic

/-!
# Hom exactness for a two-step projective presentation

This file packages the two precomposition maps induced by a two-step
projective presentation

`P₁ ⟶ P₀ ⟶ X`

as linear maps on Hom spaces.  Precomposition with the augmentation is
injective, and its range is the kernel of precomposition with the
differential.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.AuslanderTranspose.TwoStepProjectivePresentation

universe uk u

variable {k : Type uk} [CommRing k]
  {R : Type u} [Ring R] [IsNoetherianRing R]
  [Linear k (FGModuleCat.{u} R)]
  {X : FGModuleCat.{u} R}

/-- Precomposition with the augmentation `P₀ ⟶ X`. -/
def augmentationPrecompLinear
    (P : TwoStepProjectivePresentation X) (Y : FGModuleCat.{u} R) :
    (X ⟶ Y) →ₗ[k] (P.augmentation.p ⟶ Y) :=
  CategoryTheory.Linear.leftComp k Y P.augmentation.f

/-- Precomposition with the differential `P₁ ⟶ P₀`. -/
def differentialPrecompLinear
    (P : TwoStepProjectivePresentation X) (Y : FGModuleCat.{u} R) :
    (P.augmentation.p ⟶ Y) →ₗ[k] (P.syzygyPresentation.p ⟶ Y) :=
  CategoryTheory.Linear.leftComp k Y P.differential

@[simp]
theorem augmentationPrecompLinear_apply
    (P : TwoStepProjectivePresentation X) (Y : FGModuleCat.{u} R)
    (f : X ⟶ Y) :
    P.augmentationPrecompLinear (k := k) Y f = P.augmentation.f ≫ f :=
  rfl

@[simp]
theorem differentialPrecompLinear_apply
    (P : TwoStepProjectivePresentation X) (Y : FGModuleCat.{u} R)
    (f : P.augmentation.p ⟶ Y) :
    P.differentialPrecompLinear (k := k) Y f = P.differential ≫ f :=
  rfl

/-- Precomposition with the epimorphic augmentation is injective. -/
theorem augmentationPrecompLinear_injective
    (P : TwoStepProjectivePresentation X) (Y : FGModuleCat.{u} R) :
    Function.Injective (P.augmentationPrecompLinear (k := k) Y) := by
  intro f g h
  apply (cancel_epi P.augmentation.f).1
  exact h

/-- Applying `Hom(-,Y)` to the projective presentation is exact at
`Hom(P₀,Y)`. -/
theorem range_augmentationPrecompLinear
    (P : TwoStepProjectivePresentation X) (Y : FGModuleCat.{u} R) :
    LinearMap.range (P.augmentationPrecompLinear (k := k) Y) =
      LinearMap.ker (P.differentialPrecompLinear (k := k) Y) := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    change P.differential ≫ P.augmentation.f ≫ f = 0
    rw [← Category.assoc, P.differential_comp_augmentation, zero_comp]
  · intro f hf
    rw [LinearMap.mem_ker] at hf
    letI : Epi P.presentationComplex.g := by
      dsimp [presentationComplex]
      infer_instance
    obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc'
      (P.presentationComplex_exact.gIsCokernel) f hf
    exact ⟨g, hg⟩

end QuotientSubmoduleEquidistribution.AuslanderTranspose.TwoStepProjectivePresentation
