import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalNakayamaMatlisComparison
import QuotientSubmoduleEquidistribution.RepresentationTheory.NakayamaMatlisDuality
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# Stable Hom--Ext duality over a finite-dimensional algebra

The finite-dimensional Nakayama--Matlis comparison is combined here with the
presentation quotient computing `Ext¹`.  For every chosen two-step
projective presentation of `X`, this gives the natural equivalence

`Ext¹(Y, DTr_P X) ≃ D_K (stable Hom(X,Y))`.

The construction is presentation-dependent but otherwise general.  It uses
no representation-finiteness, minimality, concrete algebra, or module
classification.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace QuotientSubmoduleEquidistribution.AuslanderTranspose.TwoStepProjectivePresentation

open QuotientSubmoduleEquidistribution.RingelStable

universe w u

variable (K R : Type u) [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
  {X : FGModuleCat.{u} R}
  (P : TwoStepProjectivePresentation X)
  [HasExt.{w} (FGModuleCat.{u} R)]

local instance : Linear K (ProjectiveStableCategory (R := R)) :=
  ProjectiveStableScalar.linear K R

local instance : Functor.Linear K (projectiveStableFunctor (R := R)) :=
  ProjectiveStableScalar.functorLinear K R

local instance : Module.Injective K K :=
  Module.injective_of_isSemisimpleRing K K

/-- The presentation quotient before identifying it with `Ext¹`. -/
def finiteDimensionalBoundaryStableLinearEquiv
    (Y : FGModuleCat.{u} R) :
    ((Y ⟶ P.dTransposeCokernel
        (QuotientSubmoduleEquidistribution.ArtinDuality.ofFiniteDimensional K)) ⧸
      P.dTransposeExtPresentationRange (k := K)
        (QuotientSubmoduleEquidistribution.ArtinDuality.ofFiniteDimensional K) Y) ≃ₗ[K]
      (((projectiveStableFunctor (R := R)).obj X ⟶
        (projectiveStableFunctor (R := R)).obj Y) →ₗ[K] K) :=
  (finiteDimensionalTwoStepNakayamaMatlisComparison K R P).boundaryStableLinearEquiv Y

/-- The fixed-presentation stable Auslander--Reiten formula over a
finite-dimensional algebra over a field. -/
def finiteDimensionalStableHomExtLinearDuality :
    QuotientSubmoduleEquidistribution.StableHomExtLinearDuality (k := K)
      (projectiveStableFunctor (R := R)) X
      (P.dTranspose (QuotientSubmoduleEquidistribution.ArtinDuality.ofFiniteDimensional K)) K :=
  (finiteDimensionalTwoStepNakayamaMatlisComparison K R P).toStableHomExtLinearDuality

/-- Pointwise form of the fixed-presentation stable Auslander--Reiten formula. -/
def finiteDimensionalStableHomExtLinearEquiv
    (Y : FGModuleCat.{u} R) :
    Ext.{w} Y
        (P.dTranspose (QuotientSubmoduleEquidistribution.ArtinDuality.ofFiniteDimensional K)) 1
      ≃ₗ[K]
        (((projectiveStableFunctor (R := R)).obj X ⟶
          (projectiveStableFunctor (R := R)).obj Y) →ₗ[K] K) :=
  (P.dTransposeExtOneQuotientLinearEquiv (k := K)
      (QuotientSubmoduleEquidistribution.ArtinDuality.ofFiniteDimensional K) Y).symm.trans
    (finiteDimensionalBoundaryStableLinearEquiv K R P Y)

/-- Evaluation on a connecting class and an ordinary representative of a
stable morphism. -/
@[simp]
theorem finiteDimensionalStableHomExtLinearEquiv_connecting_map
    (Y : FGModuleCat.{u} R)
    (c : Y ⟶ P.dTransposeCokernel
      (QuotientSubmoduleEquidistribution.ArtinDuality.ofFiniteDimensional K))
    (f : X ⟶ Y) :
    finiteDimensionalStableHomExtLinearEquiv K R P Y
        (P.dTransposeConnectingLinear (k := K)
          (QuotientSubmoduleEquidistribution.ArtinDuality.ofFiniteDimensional K) Y c)
        ((projectiveStableFunctor (R := R)).map f) =
      FiniteProjectiveNakayama.fieldNakayamaHomEquiv
        (K := K) (R := R) P.P₀ Y
        (c ≫ P.dTransposeCokernelι
          (QuotientSubmoduleEquidistribution.ArtinDuality.ofFiniteDimensional K))
        (P.augmentation.f ≫ f) := by
  let D : QuotientSubmoduleEquidistribution.ArtinDuality.Data R :=
    QuotientSubmoduleEquidistribution.ArtinDuality.ofFiniteDimensional K
  let N := finiteDimensionalTwoStepNakayamaMatlisComparison K R P
  have hq :
      (P.dTransposeExtOneQuotientLinearEquiv (k := K) D Y).symm
          (P.dTransposeConnectingLinear (k := K) D Y c) =
        Submodule.Quotient.mk c := by
    apply (P.dTransposeExtOneQuotientLinearEquiv (k := K) D Y).injective
    rw [LinearEquiv.apply_symm_apply]
    exact P.dTransposeExtOneQuotientLinearEquiv_mk (k := K) D Y c
  change N.boundaryStableLinear Y
      ((P.dTransposeExtOneQuotientLinearEquiv (k := K) D Y).symm
        (P.dTransposeConnectingLinear (k := K) D Y c))
      ((projectiveStableFunctor (R := R)).map f) = _
  rw [hq, N.boundaryStableLinear_mk_map]
  rfl

/-- Pullback naturality of the pointwise field equivalence. -/
theorem finiteDimensionalStableHomExtLinearEquiv_naturality
    {Y Z : FGModuleCat.{u} R}
    (a : (projectiveStableFunctor (R := R)).obj X ⟶
      (projectiveStableFunctor (R := R)).obj Y)
    (g : Y ⟶ Z)
    (ξ : Ext.{w} Z
      (P.dTranspose (QuotientSubmoduleEquidistribution.ArtinDuality.ofFiniteDimensional K)) 1) :
    finiteDimensionalStableHomExtLinearEquiv K R P Y
        ((Ext.mk₀ g).comp ξ (zero_add 1)) a =
      finiteDimensionalStableHomExtLinearEquiv K R P Z ξ
        (a ≫ (projectiveStableFunctor (R := R)).map g) :=
  (finiteDimensionalStableHomExtLinearDuality K R P).naturality a g ξ

end QuotientSubmoduleEquidistribution.AuslanderTranspose.TwoStepProjectivePresentation
