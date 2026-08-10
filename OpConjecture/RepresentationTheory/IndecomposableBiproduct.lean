import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import OpConjecture.RepresentationTheory.EndomorphismRadical

/-!
# Indecomposable modules and finite biproducts

An indecomposable finite-length module that is exhibited as a finite
biproduct of indecomposable modules is isomorphic to one of the displayed
summands.  The proof uses the local endomorphism ring of the source: the
identity is a finite sum of the component projection/inclusion composites,
so one composite is a unit.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace OpConjecture.IndecomposableBiproduct

universe u w

variable {R : Type u} [Ring R]

/-- An indecomposable finite-length module is isomorphic to one summand of
any finite biproduct decomposition into indecomposables. -/
theorem exists_iso_summand
    (X : FGModuleCat.{w} R)
    (hXfinite : IsFiniteLength R X)
    (hXindec : OpConjecture.Foundation.IsIndecomposableModule R X)
    {J : Type} [Fintype J]
    (Y : J → FGModuleCat.{w} R)
    (hYindec : ∀ j, OpConjecture.Foundation.IsIndecomposableModule R (Y j))
    (e : X ≅ biproduct Y) :
    ∃ j, Nonempty (X ≅ Y j) := by
  let comp : J → Module.End R X :=
    fun j ↦
      (biproduct.ι Y j ≫ e.inv).hom.hom.comp
        (e.hom ≫ biproduct.π Y j).hom.hom
  have hcat :
      ∑ j : J,
          (e.hom ≫ biproduct.π Y j) ≫
            (biproduct.ι Y j ≫ e.inv) =
        𝟙 X := by
    calc
      _ =
          e.hom ≫
            (∑ j : J, biproduct.π Y j ≫ biproduct.ι Y j) ≫
            e.inv := by
          simp only [Category.assoc, Preadditive.comp_sum,
            Preadditive.sum_comp]
      _ = e.hom ≫ e.inv := by rw [biproduct.total]; simp
      _ = 𝟙 X := e.hom_inv_id
  let underlying :
      (X ⟶ X) →+ Module.End R X :=
    { toFun := fun f ↦ f.hom.hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hsum :
      (∑ j : J,
          ((e.hom ≫ biproduct.π Y j) ≫
            (biproduct.ι Y j ≫ e.inv)).hom.hom) =
        ∑ j : J, comp j := by
    apply Finset.sum_congr rfl
    intro j _
    rfl
  have hcompSum : (∑ j : J, comp j) = 1 := by
    calc
      _ =
          ∑ j : J,
            underlying
              ((e.hom ≫ biproduct.π Y j) ≫
                (biproduct.ι Y j ≫ e.inv)) := hsum.symm
      _ =
          underlying
            (∑ j : J,
              (e.hom ≫ biproduct.π Y j) ≫
                (biproduct.ι Y j ≫ e.inv)) := by
            symm
            exact map_sum underlying _ Finset.univ
      _ = underlying (𝟙 X) := congrArg underlying hcat
      _ = 1 := rfl
  letI : IsLocalRing (Module.End R X) :=
    OpConjecture.Foundation.isLocalRing_end_of_isIndecomposable hXfinite hXindec
  have hunit : IsUnit (∑ j : J, comp j) := by
    rw [hcompSum]
    exact isUnit_one
  obtain ⟨j, _, hjunit⟩ :=
    IsLocalRing.exists_of_isUnit_sum
      (s := Finset.univ) (f := comp) hunit
  obtain ⟨el⟩ :=
    OpConjecture.nonempty_linearEquiv_of_isUnit_comp
      hXindec (hYindec j)
      (biproduct.ι Y j ≫ e.inv).hom.hom
      (e.hom ≫ biproduct.π Y j).hom.hom
      hjunit
  exact ⟨j, ⟨el.toFGModuleCatIso⟩⟩

end OpConjecture.IndecomposableBiproduct
