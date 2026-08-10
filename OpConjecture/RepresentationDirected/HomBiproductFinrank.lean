import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Hom dimensions and finite biproducts

Finite biproduct universal properties give linear equivalences between Hom
spaces and finite products of Hom spaces.  Their finrank formulas supply the
additivity used by directed mixed coordinates and multiplicity objects.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RepresentationDirected

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

universe uK uC vC uJ

variable {K : Type uK} [Field K]
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear K C]
  [HasFiniteBiproducts C]

/-- A finite index for `n i` copies of each object on finite support. -/
def MultiplicityIndex {I : Type*} [DecidableEq I]
    (support : Finset I) (n : I → ℕ) :=
  Σ i : support, Fin (n i)

instance {I : Type*} [DecidableEq I] (support : Finset I) (n : I → ℕ) :
    Fintype (MultiplicityIndex support n) := by
  dsimp only [MultiplicityIndex]
  infer_instance

/-- The heterogeneous finite biproduct encoded by a natural multiplicity
vector. -/
def multiplicityBiproduct {I : Type*} [DecidableEq I]
    (X : I → C) (support : Finset I) (n : I → ℕ) : C :=
  ⨁ fun p : MultiplicityIndex support n => X p.1

/-- Covariant additivity of Hom as a linear equivalence. -/
def homLinearEquivBiproduct
    {J : Type uJ} [Fintype J] (X : C) (Y : J → C) :
    (X ⟶ ⨁ Y) ≃ₗ[K] ∀ j, X ⟶ Y j where
  toFun f j := f ≫ biproduct.π Y j
  invFun f := biproduct.lift f
  left_inv f := by
    apply biproduct.hom_ext
    intro j
    simp
  right_inv f := by
    funext j
    simp
  map_add' f g := by
    funext j
    simp
  map_smul' r f := by
    funext j
    simp

/-- Contravariant additivity of Hom as a linear equivalence. -/
def biproductHomLinearEquiv
    {J : Type uJ} [Fintype J] (Y : J → C) (X : C) :
    (⨁ Y ⟶ X) ≃ₗ[K] ∀ j, Y j ⟶ X where
  toFun f j := biproduct.ι Y j ≫ f
  invFun f := biproduct.desc f
  left_inv f := by
    apply biproduct.hom_ext'
    intro j
    simp
  right_inv f := by
    funext j
    simp
  map_add' f g := by
    funext j
    simp
  map_smul' r f := by
    funext j
    simp

/-- Binary covariant additivity of Hom as a linear equivalence. -/
def homLinearEquivBiprod (X Y Z : C) :
    (X ⟶ Y ⊞ Z) ≃ₗ[K] (X ⟶ Y) × (X ⟶ Z) where
  toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
  invFun f := biprod.lift f.1 f.2
  left_inv f := by
    apply biprod.hom_ext
    · simp
    · simp
  right_inv f := by simp
  map_add' f g := by simp
  map_smul' r f := by simp

/-- Binary contravariant additivity of Hom as a linear equivalence. -/
def biprodHomLinearEquiv (X Y Z : C) :
    (X ⊞ Y ⟶ Z) ≃ₗ[K] (X ⟶ Z) × (Y ⟶ Z) where
  toFun f := (biprod.inl ≫ f, biprod.inr ≫ f)
  invFun f := biprod.desc f.1 f.2
  left_inv f := by
    apply biprod.hom_ext'
    · simp
    · simp
  right_inv f := by simp
  map_add' f g := by simp
  map_smul' r f := by simp

theorem finrank_hom_biproduct
    {J : Type uJ} [Fintype J] (X : C) (Y : J → C)
    [Module.Finite K (X ⟶ ⨁ Y)]
    [∀ j, Module.Finite K (X ⟶ Y j)] :
    Module.finrank K (X ⟶ ⨁ Y) =
      ∑ j, Module.finrank K (X ⟶ Y j) := by
  rw [(homLinearEquivBiproduct X Y).finrank_eq,
    Module.finrank_pi_fintype K]

theorem finrank_biproduct_hom
    {J : Type uJ} [Fintype J] (Y : J → C) (X : C)
    [Module.Finite K (⨁ Y ⟶ X)]
    [∀ j, Module.Finite K (Y j ⟶ X)] :
    Module.finrank K (⨁ Y ⟶ X) =
      ∑ j, Module.finrank K (Y j ⟶ X) := by
  rw [(biproductHomLinearEquiv Y X).finrank_eq,
    Module.finrank_pi_fintype K]

theorem finrank_hom_biprod (X Y Z : C)
    [Module.Finite K (X ⟶ Y ⊞ Z)]
    [Module.Finite K (X ⟶ Y)] [Module.Finite K (X ⟶ Z)] :
    Module.finrank K (X ⟶ Y ⊞ Z) =
      Module.finrank K (X ⟶ Y) + Module.finrank K (X ⟶ Z) := by
  rw [(homLinearEquivBiprod X Y Z).finrank_eq, Module.finrank_prod]

theorem finrank_biprod_hom (X Y Z : C)
    [Module.Finite K (X ⊞ Y ⟶ Z)]
    [Module.Finite K (X ⟶ Z)] [Module.Finite K (Y ⟶ Z)] :
    Module.finrank K (X ⊞ Y ⟶ Z) =
      Module.finrank K (X ⟶ Z) + Module.finrank K (Y ⟶ Z) := by
  rw [(biprodHomLinearEquiv X Y Z).finrank_eq, Module.finrank_prod]

end OpConjecture.RepresentationDirected
