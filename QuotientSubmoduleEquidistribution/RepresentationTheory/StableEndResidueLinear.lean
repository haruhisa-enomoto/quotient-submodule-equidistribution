import QuotientSubmoduleEquidistribution.RepresentationTheory.StableEndResidue
import QuotientSubmoduleEquidistribution.RepresentationTheory.StableHomExtLinearDuality
import QuotientSubmoduleEquidistribution.RepresentationTheory.StableQuotientLinear
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Scalar-valued projective-stable residue functionals

For a nonprojective representative in an indecomposable skeleton, the kernel
of the projective-stable endomorphism residue map is closed under any
compatible field action.  Linear separation of the stable identity from this
kernel then produces a scalar-valued identity functional, together with the
linear lift required by `StableHomExtLinearDuality.toSoclePairing`.

This argument is purely structural.  It uses no classification of modules and
no concrete presentation of the algebra.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution

universe uk uC vC uQ vQ uOmega uE

/-- A scalar-linear identity functional together with its underlying
identity-detecting additive functional. -/
structure StableEndIdentityFunctional.ScalarData
    {k : Type uk} [CommRing k]
    {C : Type uC} [Category.{vC} C]
    {QCat : Type uQ} [Category.{vQ} QCat] [Preadditive QCat]
    [Linear k QCat]
    (Q : C ⥤ QCat) (X : C)
    (E : Type uE) [AddCommGroup E] [Module k E] where
  functional : StableEndIdentityFunctional Q X E
  lift : StableEndIdentityFunctional.ScalarLift (k := k) functional

namespace StableEndIdentityFunctional

variable
    {k : Type uk} [CommRing k]
    {C : Type uC} [Category.{vC} C]
    {QCat : Type uQ} [Category.{vQ} QCat] [Preadditive QCat]
    [Linear k QCat]
    {Q : C ⥤ QCat} {X : C}
    {Omega : Type uOmega} [AddCommGroup Omega]
    {E : Type uE} [AddCommGroup E] [Module k E]

/-- The kernel of an additive identity functional, regarded as a scalar
submodule once scalar stability of that kernel is supplied. -/
def scalarKernel
    (L : StableEndIdentityFunctional Q X Omega)
    (hsmul : ∀ (a : k) (f : Q.obj X ⟶ Q.obj X),
      L.functional f = 0 → L.functional (a • f) = 0) :
    Submodule k (Q.obj X ⟶ Q.obj X) where
  carrier := {f | L.functional f = 0}
  zero_mem' := map_zero L.functional
  add_mem' := by
    intro f g hf hg
    change L.functional f = 0 at hf
    change L.functional g = 0 at hg
    change L.functional (f + g) = 0
    rw [map_add, hf, hg, add_zero]
  smul_mem' := hsmul

@[simp]
theorem mem_scalarKernel_iff
    (L : StableEndIdentityFunctional Q X Omega)
    (hsmul : ∀ (a : k) (f : Q.obj X ⟶ Q.obj X),
      L.functional f = 0 → L.functional (a • f) = 0)
    (f : Q.obj X ⟶ Q.obj X) :
    f ∈ L.scalarKernel hsmul ↔ L.functional f = 0 :=
  Iff.rfl

/-- Scalarize an additive identity functional by applying a linear map to
the quotient by its scalar-stable kernel. -/
def scalarized
    (L : StableEndIdentityFunctional Q X Omega)
    (hsmul : ∀ (a : k) (f : Q.obj X ⟶ Q.obj X),
      L.functional f = 0 → L.functional (a • f) = 0)
    (phi : ((Q.obj X ⟶ Q.obj X) ⧸ L.scalarKernel hsmul) →ₗ[k] E)
    (hphi : phi ((L.scalarKernel hsmul).mkQ (𝟙 (Q.obj X))) ≠ 0) :
    StableEndIdentityFunctional Q X E where
  functional := (phi.comp (L.scalarKernel hsmul).mkQ).toAddMonoidHom
  identity_ne_zero := hphi
  nonretraction_eq_zero := by
    intro r hr
    change phi ((L.scalarKernel hsmul).mkQ (Q.map r)) = 0
    rw [show (L.scalarKernel hsmul).mkQ (Q.map r) = 0 by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact L.nonretraction_eq_zero r hr, map_zero]

/-- The scalarized functional has its tautological scalar lift. -/
def scalarizedScalarLift
    (L : StableEndIdentityFunctional Q X Omega)
    (hsmul : ∀ (a : k) (f : Q.obj X ⟶ Q.obj X),
      L.functional f = 0 → L.functional (a • f) = 0)
    (phi : ((Q.obj X ⟶ Q.obj X) ⧸ L.scalarKernel hsmul) →ₗ[k] E)
    (hphi : phi ((L.scalarKernel hsmul).mkQ (𝟙 (Q.obj X))) ≠ 0) :
    ScalarLift (k := k) (L.scalarized hsmul phi hphi) where
  linear := phi.comp (L.scalarKernel hsmul).mkQ
  toAddMonoidHom_eq := rfl

/-- Package a chosen quotient functional and its identity-separation proof as
scalar identity data. -/
def scalarData
    (L : StableEndIdentityFunctional Q X Omega)
    (hsmul : ∀ (a : k) (f : Q.obj X ⟶ Q.obj X),
      L.functional f = 0 → L.functional (a • f) = 0)
    (phi : ((Q.obj X ⟶ Q.obj X) ⧸ L.scalarKernel hsmul) →ₗ[k] E)
    (hphi : phi ((L.scalarKernel hsmul).mkQ (𝟙 (Q.obj X))) ≠ 0) :
    ScalarData (k := k) Q X E where
  functional := L.scalarized hsmul phi hphi
  lift := L.scalarizedScalarLift hsmul phi hphi

/-- A reusable coefficient condition for scalarization: linear functionals
into `E` separate the points of `M`. -/
def SeparatesPoints
    (M : Type*) [AddCommGroup M] [Module k M] : Prop :=
  ∀ m : M, m ≠ 0 → ∃ phi : M →ₗ[k] E, phi m ≠ 0

/-- Point separation of the scalar residue quotient constructs a scalar
identity functional and its lift.  Injectivity of `E` is not needed here. -/
noncomputable def scalarDataOfSeparatesPoints
    (L : StableEndIdentityFunctional Q X Omega)
    (hsmul : ∀ (a : k) (f : Q.obj X ⟶ Q.obj X),
      L.functional f = 0 → L.functional (a • f) = 0)
    (hsep : SeparatesPoints (k := k) (E := E)
      ((Q.obj X ⟶ Q.obj X) ⧸ L.scalarKernel hsmul)) :
    ScalarData (k := k) Q X E := by
  let W := L.scalarKernel hsmul
  have hid : W.mkQ (𝟙 (Q.obj X)) ≠ 0 := by
    rw [ne_eq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact L.identity_ne_zero
  let hex := hsep _ hid
  let phi := Classical.choose hex
  have hphi := Classical.choose_spec hex
  exact L.scalarData hsmul phi hphi

/-- Over a field, every scalar-stable additive identity functional admits a
field-valued scalarization.  No finite-dimensionality assumption is needed. -/
noncomputable def fieldScalarData
    {K : Type uk} [Field K]
    {C : Type uC} [Category.{vC} C]
    {QCat : Type uQ} [Category.{vQ} QCat] [Preadditive QCat]
    [Linear K QCat]
    {Q : C ⥤ QCat} {X : C}
    {Omega : Type uOmega} [AddCommGroup Omega]
    (L : StableEndIdentityFunctional Q X Omega)
    (hsmul : ∀ (a : K) (f : Q.obj X ⟶ Q.obj X),
      L.functional f = 0 → L.functional (a • f) = 0) :
    ScalarData (k := K) Q X K := by
  let W := L.scalarKernel hsmul
  have hid : W.mkQ (𝟙 (Q.obj X)) ≠ 0 := by
    rw [ne_eq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact L.identity_ne_zero
  let hex := Module.Projective.exists_dual_eq_one K hid
  let phi := Classical.choose hex
  have hphiOne := Classical.choose_spec hex
  have hphi : phi (W.mkQ (𝟙 (Q.obj X))) ≠ 0 := by
    rw [hphiOne]
    exact one_ne_zero
  exact L.scalarData hsmul phi hphi

end StableEndIdentityFunctional

namespace IndecomposableSkeleton

open QuotientSubmoduleEquidistribution.RingelStable

universe uR uIota w

variable {K : Type uk} [Field K]
  {R : Type uR} [Ring R] [IsNoetherianRing R]
  [Linear K (FGModuleCat.{uR} R)]
  [Linear K (ProjectiveStableCategory (R := R))]
  [Functor.Linear K (projectiveStableFunctor (R := R))]
  {Iota : Type uIota}
  (sigma : IndecomposableSkeleton.{uR, uIota, uR} R Iota)

omit [IsNoetherianRing R]
  [Linear K (ProjectiveStableCategory (R := R))]
  [Functor.Linear K (projectiveStableFunctor (R := R))] in
/-- If a scalar multiple of a morphism is a retraction, then the original
morphism is already a retraction. -/
theorem isSplitEpi_of_smul
    {X Y : FGModuleCat.{uR} R} (a : K) (f : X ⟶ Y)
    (h : IsSplitEpi (a • f)) : IsSplitEpi f := by
  letI : IsSplitEpi (a • f) := h
  exact IsSplitEpi.mk' {
    section_ := a • section_ (a • f)
    id := by
      rw [Linear.smul_comp, ← Linear.comp_smul]
      exact IsSplitEpi.id (a • f) }

/-- The kernel of the canonical stable residue functional is closed under
the selected scalar action. -/
theorem projectiveStableEndIdentityFunctional_kernel_smul
    (x : Iota) (hx : ¬ Projective (sigma.obj x))
    (a : K)
    (q : (projectiveStableFunctor (R := R)).obj (sigma.obj x) ⟶
      (projectiveStableFunctor (R := R)).obj (sigma.obj x))
    (hq : (projectiveStableEndIdentityFunctional sigma x hx).functional q = 0) :
    (projectiveStableEndIdentityFunctional sigma x hx).functional (a • q) = 0 := by
  obtain ⟨f, rfl⟩ := ProjectiveStableScalar.mapLinear_surjective K R q
  change projectiveStableResidueMap sigma x hx
    (a • (projectiveStableFunctor (R := R)).map f) = 0
  change projectiveStableResidueMap sigma x hx
    ((projectiveStableFunctor (R := R)).map f) = 0 at hq
  have hf : ¬ IsSplitEpi f :=
    (projectiveStableResidueMap_map_eq_zero_iff sigma x hx f).mp hq
  rw [← (projectiveStableFunctor (R := R)).map_smul]
  exact (projectiveStableResidueMap_map_eq_zero_iff sigma x hx (a • f)).mpr
    (fun hsplit ↦ hf (isSplitEpi_of_smul a f hsplit))

/-- The kernel of the additive stable residue map, packaged as a submodule. -/
def projectiveStableResidueKernelSubmodule
    (x : Iota) (hx : ¬ Projective (sigma.obj x)) :
    Submodule K
      ((projectiveStableFunctor (R := R)).obj (sigma.obj x) ⟶
        (projectiveStableFunctor (R := R)).obj (sigma.obj x)) :=
  (projectiveStableEndIdentityFunctional sigma x hx).scalarKernel
    (projectiveStableEndIdentityFunctional_kernel_smul (K := K) sigma x hx)

/-- Over a field, linear separation of the stable identity from the residue
kernel gives the scalar identity functional needed by the stable Hom--Ext
socle pairing. -/
def projectiveStableScalarEndIdentityData
    (x : Iota) (hx : ¬ Projective (sigma.obj x)) :
    StableEndIdentityFunctional.ScalarData (k := K)
      (projectiveStableFunctor (R := R)) (sigma.obj x) K :=
  (projectiveStableEndIdentityFunctional sigma x hx).fieldScalarData
    (projectiveStableEndIdentityFunctional_kernel_smul (K := K) sigma x hx)

/-- Combine the field-valued stable residue with any scalar stable
Hom--`Ext¹` duality to obtain its identity-detecting socle pairing. -/
def projectiveStableHomExtSoclePairing
    [HasExt.{w} (FGModuleCat.{uR} R)]
    {T : FGModuleCat.{uR} R}
    (x : Iota) (hx : ¬ Projective (sigma.obj x))
    (D : StableHomExtLinearDuality (k := K)
      (projectiveStableFunctor (R := R)) (sigma.obj x) T K) :
    StableHomExtSoclePairing
      (projectiveStableFunctor (R := R)) (sigma.obj x) T K := by
  let L := projectiveStableScalarEndIdentityData (K := K) sigma x hx
  exact D.toSoclePairing L.functional L.lift

end IndecomposableSkeleton

end QuotientSubmoduleEquidistribution
