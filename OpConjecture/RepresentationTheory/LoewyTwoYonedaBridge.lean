import OpConjecture.RepresentationTheory.ExtClassReflection
import OpConjecture.RepresentationTheory.ExtMatrixBridge

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace OpConjecture.YonedaExtReflection

universe u v

variable {K R : Type u} [Field K] [Ring R] [Algebra K R] [Small.{v} R]

/--
For a short exact sequence whose two endpoints are finite isotypic
biproducts, an injectively scalarized `Ext¹`-matrix is an
idempotent-indecomposable one-arrow representation whenever the middle module
is finite-length and indecomposable.
-/
theorem shortExact_scalarizedExtLinearMap_isIdempotentIndecomposable
    {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (X Y M : ModuleCat.{v} R)
    (hX : 𝟙 X ≠ 0) (hY : 𝟙 Y ≠ 0)
    (f : (⨁ fun _ : J ↦ Y) ⟶ M)
    (g : M ⟶ (⨁ fun _ : I ↦ X))
    (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian R M] [IsArtinian R M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule R M)
    (ℓ : Ext X Y 1 →ₗ[K] K) (hℓ : Function.Injective ℓ) :
    LoewyTwoRankCore.IsIdempotentIndecomposable
      (scalarizedExtLinearMap X Y ℓ hS.extClass) := by
  apply scalarizedExtLinearMap_isIdempotentIndecomposable
    X Y hX hY ℓ hℓ hS.extClass
  intro a₁ a₃ ha₁ ha₃ hcompat
  exact endpoint_idempotents_trivial_of_extClass_compatibility
    hS hM a₁ a₃ ha₁ ha₃ hcompat

end OpConjecture.YonedaExtReflection
