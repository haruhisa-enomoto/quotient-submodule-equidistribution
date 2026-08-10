import Mathlib.RingTheory.Artinian.Module
import OpConjecture.RepresentationTheory.MaximalFlagAuslanderPackage

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace OpConjecture
namespace IndecomposableSkeleton
namespace LegalQuotientDeletionChain

open AuslanderEquivalence
open AuslanderEquivalence.CoordinateIdempotent

universe uR uι wR uK

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι}
  (σ : IndecomposableSkeleton.{uR, uι, wR} R ι)
  [Fintype ι]
  {K : Type uK} [Field K] [Algebra K R]
  [∀ i : ι, Module K (σ.obj i)]
  [∀ i : ι, IsScalarTower K R (σ.obj i)]
  [∀ i : ι, FiniteDimensional K (σ.obj i)]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The additive generator of a finite-dimensional skeleton is itself
finite-dimensional over the common ground field. -/
theorem finiteDimensional_skeletonGenerator :
    letI : Module K (skeletonGenerator σ) :=
      Module.restrictScalars K R (skeletonGenerator σ)
    FiniteDimensional K (skeletonGenerator σ) := by
  letI : Module K (skeletonGenerator σ) :=
    Module.restrictScalars K R (skeletonGenerator σ)
  letI : IsScalarTower K R (skeletonGenerator σ) :=
    IsScalarTower.restrictScalars K R (skeletonGenerator σ)
  let ε : ι ≃ Fin (Fintype.card ι) :=
    Fintype.equivFin ι
  let a : Fin (Fintype.card ι) → ι :=
    fun t ↦ ε.symm t
  let reindex :
      skeletonGenerator σ ≅
        ⨁ fun t : Fin (Fintype.card ι) ↦ σ.obj (a t) :=
    biproduct.whiskerEquiv ε
      (fun t ↦ eqToIso (by
        simp only [a, Equiv.symm_apply_apply]))
  let F :=
    forget₂ (FGModuleCat.{wR} R) (ModuleCat.{wR} R)
  let diagram :
      Fin (Fintype.card ι) → FGModuleCat.{wR} R :=
    fun t ↦ σ.obj (a t)
  letI : PreservesBiproduct diagram F :=
    preservesBiproduct_of_preservesProduct F
  let e :
      skeletonGenerator σ ≅
        FGModuleCat.of R
          (∀ t : Fin (Fintype.card ι), σ.obj (a t)) :=
    reindex ≪≫
      F.preimageIso
        (F.mapBiproduct diagram ≪≫
          ModuleCat.biproductIsoPi
            (fun t ↦ F.obj (diagram t)))
  exact
    (Module.Finite.equiv_iff
      ((FGModuleCat.isoToLinearEquiv e).restrictScalars K)).mpr
      (inferInstance :
        Module.Finite K
          (∀ t : Fin (Fintype.card ι), σ.obj (a t)))

private def moduleEndToFGEnd (X : FGModuleCat.{wR} R) :
    Module.End R X →+* End X where
  toFun f :=
    ObjectProperty.homMk (ModuleCat.ofHom f)
  map_one' := by
    apply FGModuleCat.hom_ext
    rfl
  map_mul' f g := by
    apply FGModuleCat.hom_ext
    rfl
  map_zero' := by
    apply FGModuleCat.hom_ext
    rfl
  map_add' f g := by
    apply FGModuleCat.hom_ext
    rfl

omit [IsNoetherianRing R] in
private theorem moduleEndToFGEnd_surjective
    (X : FGModuleCat.{wR} R) :
    Function.Surjective (moduleEndToFGEnd X) := by
  intro f
  refine ⟨f.hom.hom, ?_⟩
  apply FGModuleCat.hom_ext
  rfl

omit [IsNoetherianRing R] in
/-- A finite-dimensional finitely generated module also has an Artinian
categorical endomorphism ring.  This bridges Mathlib's raw
`Module.End` theorem to `CategoryTheory.End`. -/
theorem isArtinianRing_end_fgModuleCat_of_finiteDimensional
    {K' : Type uK} [Field K'] [Algebra K' R]
    (X : FGModuleCat.{wR} R)
    [Module K' X] [IsScalarTower K' R X]
    [FiniteDimensional K' X] :
    IsArtinianRing (End X) := by
  letI : IsArtinianRing (Module.End R X) :=
    OpConjecture.isArtinianRing_moduleEnd_of_finiteDimensional
      (K := K') (B := R) (M := X)
  exact
    (moduleEndToFGEnd_surjective X).isArtinianRing

include K

/-- The Auslander endomorphism algebra attached to a finite-dimensional
skeleton is left Artinian. -/
theorem isArtinianRing_skeletonAuslanderAlgebra :
    IsArtinianRing (skeletonAuslanderAlgebra σ) := by
  letI : Module K (skeletonGenerator σ) :=
    Module.restrictScalars K R (skeletonGenerator σ)
  letI : IsScalarTower K R (skeletonGenerator σ) :=
    IsScalarTower.restrictScalars K R (skeletonGenerator σ)
  letI : FiniteDimensional K (skeletonGenerator σ) :=
    finiteDimensional_skeletonGenerator (K := K) σ
  exact
    isArtinianRing_end_fgModuleCat_of_finiteDimensional
      (K' := K) (skeletonGenerator σ)

/-- Consequently every quotient by a coordinate principal ideal has the
Artinian instance required by the radical-sandwich bridge. -/
theorem isArtinianRing_skeletonAuslanderQuotient
    (p : ι → Prop) :
    IsArtinianRing
      (skeletonAuslanderAlgebra σ ⧸
        (Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ p)).asIdeal) := by
  letI : IsArtinianRing (skeletonAuslanderAlgebra σ) :=
    isArtinianRing_skeletonAuslanderAlgebra (K := K) σ
  infer_instance

end LegalQuotientDeletionChain
end IndecomposableSkeleton
end OpConjecture
