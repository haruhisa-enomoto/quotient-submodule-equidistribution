import OpConjecture.RepresentationTheory.ArtinDTranspose
import OpConjecture.RepresentationTheory.InjectivePresentationExt
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# The injective-presentation Ext quotient for `DTr`

For a chosen finite two-step projective presentation and finite-module Artin
duality, the presentation-dependent object `DTr_P X` embeds in `νP₁`.  This
file names its actual cokernel `C_P`, proves that `C_P` embeds in `νP₀`, and
identifies it with the image of `νP₁ ⟶ νP₀`.

After choosing a scalar-linear structure, the short exact sequence

`0 ⟶ DTr_P X ⟶ νP₁ ⟶ C_P ⟶ 0`

specializes the general injective-presentation theorem to a pullback-natural
linear quotient computing `Ext¹(Y,DTr_P X)`.  The numerator is
`Hom(Y,C_P)`, not all of `Hom(Y,νP₀)`: the latter would be valid only if the
second copresentation morphism were epic.

No compatibility between the categorical Artin duality and the selected
scalar structure is asserted here.  In particular this file does not yet
construct a Nakayama--Matlis duality, identify `DTr_P X` with the conventional
AR translate, or construct an almost-split sequence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace OpConjecture.AuslanderTranspose.TwoStepProjectivePresentation

universe uk w u

variable {R : Type u} [Ring R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
  {X : FGModuleCat.{u} R}

/-- The inclusion of `DTr_P X` in `νP₁`, packaged as an injective
presentation. -/
def dTransposeInjectivePresentation
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R) :
    InjectivePresentation (P.dTranspose D) where
  J := P.nakayamaP₁ D
  injective := P.injective_nakayamaP₁ D
  f := P.dTransposeι D
  mono := inferInstance

/-- The actual quotient term `C_P = cokernel(DTr_P X ⟶ νP₁)`. -/
abbrev dTransposeCokernel
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R) : FGModuleCat.{u} R :=
  cokernel (P.dTransposeι D)

/-- The cokernel projection `νP₁ ⟶ C_P`. -/
abbrev dTransposeCokernelπ
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R) :
    P.nakayamaP₁ D ⟶ P.dTransposeCokernel D :=
  cokernel.π (P.dTransposeι D)

/-- The copresentation morphism `νP₁ ⟶ νP₀` descends to `C_P ⟶ νP₀`. -/
def dTransposeCokernelι
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R) :
    P.dTransposeCokernel D ⟶ P.nakayamaP₀ D :=
  cokernel.desc (P.dTransposeι D) (P.dTransposeNext D)
    (P.dTransposeι_comp_dTransposeNext D)

/-- The factorization `νP₁ ⟶ C_P ⟶ νP₀` recovers the second
copresentation morphism. -/
@[simp]
theorem dTransposeCokernelπ_comp_ι
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R) :
    P.dTransposeCokernelπ D ≫ P.dTransposeCokernelι D =
      P.dTransposeNext D := by
  exact cokernel.π_desc _ _ _

/-- Exactness of the `DTr` copresentation makes `C_P ⟶ νP₀` monic. -/
instance dTransposeCokernelι_mono
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R) :
    Mono (P.dTransposeCokernelι D) := by
  exact (P.dTransposeCopresentation_exact D).mono_cokernelDesc

/-- The embedding `C_P ⟶ νP₀`, packaged as a second injective
presentation. -/
def dTransposeCokernelInjectivePresentation
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R) :
    InjectivePresentation (P.dTransposeCokernel D) where
  J := P.nakayamaP₀ D
  injective := P.injective_nakayamaP₀ D
  f := P.dTransposeCokernelι D
  mono := inferInstance

/-- The actual cokernel `C_P` is canonically isomorphic to the image of
`νP₁ ⟶ νP₀`. -/
def dTransposeCokernelIsoImage
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R) :
    P.dTransposeCokernel D ≅ image (P.dTransposeNext D) :=
  IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (P.dTransposeι D))
    (P.dTransposeCopresentation_exact D).isColimitImage

/-- Under the cokernel--image isomorphism, the cokernel projection becomes
the canonical epimorphism onto the image. -/
@[simp]
theorem dTransposeCokernelπ_comp_cokernelIsoImage_hom
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R) :
    P.dTransposeCokernelπ D ≫ (P.dTransposeCokernelIsoImage D).hom =
      factorThruImage (P.dTransposeNext D) := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (P.dTransposeι D))
    (P.dTransposeCopresentation_exact D).isColimitImage
    WalkingParallelPair.one

/-- Under the cokernel--image isomorphism, the embedding into `νP₀` becomes
the canonical image inclusion. -/
@[simp]
theorem dTransposeCokernelIsoImage_hom_comp_image_ι
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R) :
    (P.dTransposeCokernelIsoImage D).hom ≫
        image.ι (P.dTransposeNext D) =
      P.dTransposeCokernelι D := by
  apply (cancel_epi (P.dTransposeCokernelπ D)).1
  rw [← Category.assoc]
  have hfac :
      P.dTransposeCokernelπ D ≫ (P.dTransposeCokernelIsoImage D).hom =
        factorThruImage (P.dTransposeNext D) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (P.dTransposeι D))
      (P.dTransposeCopresentation_exact D).isColimitImage
      WalkingParallelPair.one
  rw [hfac, Limits.image.fac]
  exact (P.dTransposeCokernelπ_comp_ι D).symm

section Scalar

variable {k : Type uk} [CommRing k]
  [Linear k (FGModuleCat.{u} R)]
  [HasExt.{w} (FGModuleCat.{u} R)]

/-- The short exact injective presentation used to compute
`Ext¹(-,DTr_P X)`. -/
abbrev dTransposeExtShortComplex
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R) :
    ShortComplex (FGModuleCat.{u} R) :=
  (P.dTransposeInjectivePresentation D).shortComplex

/-- The displayed image of `Hom(Y,νP₁) ⟶ Hom(Y,C_P)`. -/
abbrev dTransposeExtPresentationRange
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R)
    (Y : FGModuleCat.{u} R) :
    Submodule k (Y ⟶ P.dTransposeCokernel D) :=
  OpConjecture.InjectivePresentationExt.presentationRange
    (k := k) (P.dTransposeExtShortComplex D) Y

omit [HasExt (FGModuleCat.{u} R)] in
/-- Membership in the `DTr` presentation range is exactly factorization
through the displayed cokernel projection. -/
@[simp]
theorem mem_dTransposeExtPresentationRange_iff
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R)
    (Y : FGModuleCat.{u} R) (f : Y ⟶ P.dTransposeCokernel D) :
    f ∈ P.dTransposeExtPresentationRange (k := k) D Y ↔
      ∃ a : Y ⟶ P.nakayamaP₁ D,
        a ≫ P.dTransposeCokernelπ D = f := by
  exact OpConjecture.InjectivePresentationExt.mem_presentationRange_iff
    (k := k) (P.dTransposeExtShortComplex D) Y f

/-- The connecting map `Hom(Y,C_P) ⟶ Ext¹(Y,DTr_P X)`. -/
abbrev dTransposeConnectingLinear
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R)
    (Y : FGModuleCat.{u} R) :
    (Y ⟶ P.dTransposeCokernel D) →ₗ[k]
      Ext.{w} Y (P.dTranspose D) 1 :=
  OpConjecture.InjectivePresentationExt.connectingLinear
    (k := k) (P.dTransposeInjectivePresentation D).shortExact_shortComplex Y

/-- The sound `DTr` specialization of the injective-presentation Ext
quotient. -/
def dTransposeExtOneQuotientLinearEquiv
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R)
    (Y : FGModuleCat.{u} R) :
    ((Y ⟶ P.dTransposeCokernel D) ⧸
        P.dTransposeExtPresentationRange (k := k) D Y) ≃ₗ[k]
      Ext.{w} Y (P.dTranspose D) 1 :=
  OpConjecture.InjectivePresentationExt.quotientLinearEquivExtOne
    (k := k) (P.dTransposeInjectivePresentation D).shortExact_shortComplex Y

/-- The quotient equivalence sends a representative to its connecting
class. -/
@[simp]
theorem dTransposeExtOneQuotientLinearEquiv_mk
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R)
    (Y : FGModuleCat.{u} R)
    (f : Y ⟶ P.dTransposeCokernel D) :
    P.dTransposeExtOneQuotientLinearEquiv (k := k) D Y
        (Submodule.Quotient.mk f) =
      P.dTransposeConnectingLinear (k := k) D Y f := by
  exact OpConjecture.InjectivePresentationExt.quotientLinearEquivExtOne_mk
    (k := k) (P.dTransposeInjectivePresentation D).shortExact_shortComplex Y f

/-- Pullback on the `DTr` presentation quotient. -/
abbrev dTransposePrecompQuotient
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R)
    {Y Z : FGModuleCat.{u} R} (g : Y ⟶ Z) :
    ((Z ⟶ P.dTransposeCokernel D) ⧸
        P.dTransposeExtPresentationRange (k := k) D Z) →ₗ[k]
      ((Y ⟶ P.dTransposeCokernel D) ⧸
        P.dTransposeExtPresentationRange (k := k) D Y) :=
  OpConjecture.InjectivePresentationExt.precompQuotient
    (k := k) (P.dTransposeExtShortComplex D) g

/-- The `DTr` quotient equivalence is natural under pullback. -/
theorem dTransposeExtOneQuotientLinearEquiv_precomp
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R)
    {Y Z : FGModuleCat.{u} R} (g : Y ⟶ Z)
    (q : (Z ⟶ P.dTransposeCokernel D) ⧸
      P.dTransposeExtPresentationRange (k := k) D Z) :
    P.dTransposeExtOneQuotientLinearEquiv (k := k) D Y
        (P.dTransposePrecompQuotient (k := k) D g q) =
      (Ext.mk₀ g).comp
        (P.dTransposeExtOneQuotientLinearEquiv (k := k) D Z q)
        (zero_add 1) := by
  exact
    OpConjecture.InjectivePresentationExt.quotientLinearEquivExtOne_precompQuotient
      (k := k) (P.dTransposeInjectivePresentation D).shortExact_shortComplex g q

/-- Inverse-form naturality, oriented for an eventual map out of `Ext¹`. -/
theorem dTransposeExtOneQuotientLinearEquiv_symm_pullback
    (P : TwoStepProjectivePresentation X)
    (D : OpConjecture.ArtinDuality.Data R)
    {Y Z : FGModuleCat.{u} R} (g : Y ⟶ Z)
    (ξ : Ext.{w} Z (P.dTranspose D) 1) :
    (P.dTransposeExtOneQuotientLinearEquiv (k := k) D Y).symm
        ((Ext.mk₀ g).comp ξ (zero_add 1)) =
      P.dTransposePrecompQuotient (k := k) D g
        ((P.dTransposeExtOneQuotientLinearEquiv (k := k) D Z).symm ξ) := by
  apply (P.dTransposeExtOneQuotientLinearEquiv (k := k) D Y).injective
  simp [dTransposeExtOneQuotientLinearEquiv_precomp]

end Scalar

end OpConjecture.AuslanderTranspose.TwoStepProjectivePresentation
