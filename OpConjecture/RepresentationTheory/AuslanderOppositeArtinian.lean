import OpConjecture.RepresentationTheory.AuslanderEndArtinian
import OpConjecture.RepresentationTheory.CoordinateSimpleCovers

/-!
# Artinianity of the opposite skeleton Auslander algebra

The finite-dimensionality bridge from a finite-dimensional skeleton to
the opposite of its categorical endomorphism algebra, followed by the
coordinate-simple-cover classification.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace OpConjecture
namespace IndecomposableSkeleton
namespace LegalQuotientDeletionChain

open AuslanderEquivalence
open AuslanderEquivalence.CoordinateIdempotent

universe uR uK uι wR

variable {R : Type uR} [Ring R]
  {K : Type uK} [Field K] [Algebra K R]

/-- The faithful underlying `K`-linear endomorphism representation of
the categorical endomorphism ring of an `R`-module. -/
def fgEndRestrict
    (X : FGModuleCat.{wR} R)
    [Module K X] [IsScalarTower K R X] :
    End X →ₗ[K] Module.End K X where
  toFun f := f.hom.hom.restrictScalars K
  map_add' f g := by
    ext x
    rfl
  map_smul' r f := by
    ext x
    change (algebraMap K R r) • f.hom.hom x = r • f.hom.hom x
    exact IsScalarTower.algebraMap_smul R r _

/-- Faithfulness of the underlying endomorphism representation. -/
theorem fgEndRestrict_injective
    (X : FGModuleCat.{wR} R)
    [Module K X] [IsScalarTower K R X] :
    Function.Injective (fgEndRestrict (R := R) (K := K) X) := by
  intro f g h
  apply FGModuleCat.hom_ext
  exact LinearMap.restrictScalars_injective (R := K) (S := R) h

/-- Categorical endomorphisms of a finite-dimensional finitely
generated module form a finite-dimensional vector space. -/
theorem moduleFinite_end_fgModuleCat_of_finiteDimensional
    (X : FGModuleCat.{wR} R)
    [Module K X] [IsScalarTower K R X] [FiniteDimensional K X] :
    Module.Finite K (End X) := by
  exact Module.Finite.of_injective
    (fgEndRestrict (R := R) (K := K) X)
    (fgEndRestrict_injective (R := R) (K := K) X)

/-- The opposite categorical endomorphism ring remains
finite-dimensional over the ground field. -/
theorem moduleFinite_end_fgModuleCat_op_of_finiteDimensional
    (X : FGModuleCat.{wR} R)
    [Module K X] [IsScalarTower K R X] [FiniteDimensional K X] :
    Module.Finite K (End X)ᵐᵒᵖ := by
  letI : Module.Finite K (End X) :=
    moduleFinite_end_fgModuleCat_of_finiteDimensional
      (R := R) (K := K) X
  infer_instance

/-- The opposite categorical endomorphism ring of a finite-dimensional
finitely generated module is Artinian. -/
theorem isArtinianRing_end_fgModuleCat_op_of_finiteDimensional
    (X : FGModuleCat.{wR} R)
    [Module K X] [IsScalarTower K R X] [FiniteDimensional K X] :
    IsArtinianRing (End X)ᵐᵒᵖ := by
  letI : Module.Finite K (End X) :=
    moduleFinite_end_fgModuleCat_of_finiteDimensional
      (R := R) (K := K) X
  letI : Module.Finite K (End X)ᵐᵒᵖ := by
    infer_instance
  exact isArtinian_of_tower K inferInstance

variable [IsNoetherianRing R]
  {ι : Type uι}
  (σ : IndecomposableSkeleton.{uR, uι, wR} R ι)
  [Fintype ι]
  [∀ i : ι, Module K (σ.obj i)]
  [∀ i : ι, IsScalarTower K R (σ.obj i)]
  [∀ i : ι, FiniteDimensional K (σ.obj i)]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

include K

/-- The opposite Auslander algebra attached to a finite-dimensional
skeleton is Artinian. -/
theorem isArtinianRing_skeletonAuslanderAlgebra_op :
    IsArtinianRing (skeletonAuslanderAlgebra σ)ᵐᵒᵖ := by
  letI : Module K (skeletonGenerator σ) :=
    Module.restrictScalars K R (skeletonGenerator σ)
  letI : IsScalarTower K R (skeletonGenerator σ) :=
    IsScalarTower.restrictScalars K R (skeletonGenerator σ)
  letI : FiniteDimensional K (skeletonGenerator σ) :=
    finiteDimensional_skeletonGenerator (K := K) σ
  exact
    isArtinianRing_end_fgModuleCat_op_of_finiteDimensional
      (K := K) (skeletonGenerator σ)

end LegalQuotientDeletionChain
end IndecomposableSkeleton
end OpConjecture

namespace OpConjecture.AuslanderEquivalence.CoordinateIdempotent

open OpConjecture.IndecomposableSkeleton

universe uR uK uκ wR

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {κ : Type uκ}
  (σ : IndecomposableSkeleton.{uR, uκ, wR} R κ)
  [Finite κ]
  {K : Type uK} [Field K] [Algebra K R]
  [∀ i : κ, Module K (σ.obj i)]
  [∀ i : κ, IsScalarTower K R (σ.obj i)]
  [∀ i : κ, FiniteDimensional K (σ.obj i)]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The paper's finite-dimensional skeleton hypotheses automatically
supply the complete coordinate-simple/projective-cover package. -/
abbrev coordinateSimpleCoverClassificationOfFiniteDimensional :
    CoordinateSimpleCoverClassification σ := by
  letI : Fintype κ := Fintype.ofFinite κ
  letI : IsArtinianRing (skeletonAuslanderAlgebra σ)ᵐᵒᵖ :=
    OpConjecture.IndecomposableSkeleton.LegalQuotientDeletionChain.isArtinianRing_skeletonAuslanderAlgebra_op
      (K := K) σ
  exact coordinateSimpleCoverClassificationOfIsArtinian σ

end OpConjecture.AuslanderEquivalence.CoordinateIdempotent
