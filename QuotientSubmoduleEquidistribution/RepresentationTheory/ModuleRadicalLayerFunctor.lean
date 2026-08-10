import Mathlib.Algebra.Category.ModuleCat.Basic
import QuotientSubmoduleEquidistribution.CategoryTheory.IdempotentLifting
import QuotientSubmoduleEquidistribution.RepresentationTheory.ModuleRadicalLayerComparison

/-!
# The categorical radical-layer functor

This file packages the functorial maps on module radicals and tops as an
additive functor.  Its target deliberately remembers only the two linear
layers, not yet the radical-action maps of a separated representation.  The
kernel is nevertheless already the kernel occurring in the manuscript, and is
proved square-zero here.

The eventual separated-representation category refines this target by imposing
compatibility with radical action.  Fullness belongs to that refinement; it is
not asserted for the raw two-layer functor.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.ModuleRadicalLayerFunctor

open ModuleRadicalLayerComparison

universe u v

variable (R : Type u) [Ring R]

/-- A module regarded only as the source of its radical and top layers.  The
wrapper permits a category structure whose morphisms are pairs of layer maps,
rather than module homomorphisms. -/
structure RadicalLayerObject where
  module : ModuleCat.{v} R

/-- A morphism of raw radical-layer objects is an independent pair of maps on
the radical and on the top. -/
abbrev RadicalLayerObject.Hom
    (X Y : RadicalLayerObject R) :=
  RadicalLayerHom (R := R) X.module Y.module

instance radicalLayerCategory : Category.{v} (RadicalLayerObject R) where
  Hom := RadicalLayerObject.Hom R
  id _ := (LinearMap.id, LinearMap.id)
  comp f g := (g.1.comp f.1, g.2.comp f.2)
  assoc := by intros; rfl
  id_comp := by intros; rfl
  comp_id := by intros; rfl

instance radicalLayerPreadditive : Preadditive (RadicalLayerObject R) where
  homGroup := fun X Y ↦
    inferInstanceAs
      (AddCommGroup (RadicalLayerHom (R := R) X.module Y.module))
  add_comp := by
    intro P Q S f f' g
    apply Prod.ext
    · ext x
      exact congrArg Subtype.val (g.1.map_add (f.1 x) (f'.1 x))
    · ext x
      exact g.2.map_add
        (f.2 ((Module.jacobson R P.module).mkQ x))
        (f'.2 ((Module.jacobson R P.module).mkQ x))
  comp_add := by
    intro P Q S f g g'
    apply Prod.ext
    · ext x
      rfl
    · ext x
      rfl

/-- The additive functor which retains the maps induced on the module radical
and semisimple top. -/
def radicalLayerFunctor :
    ModuleCat.{v} R ⥤ RadicalLayerObject R where
  obj X := ⟨X⟩
  map f := layerMap f.hom
  map_id _ := by
    apply Prod.ext
    · exact radicalMap_id
    · exact topMap_id
  map_comp f g := by
    apply Prod.ext
    · exact radicalMap_comp g.hom f.hom
    · exact topMap_comp g.hom f.hom

instance radicalLayerFunctor_additive :
    (radicalLayerFunctor R).Additive where
  map_add := by
    intro X Y f g
    apply Prod.ext
    · ext x
      rfl
    · ext x
      change (Module.jacobson R Y).mkQ ((f + g).hom x) =
        (Module.jacobson R Y).mkQ (f.hom x) +
          (Module.jacobson R Y).mkQ (g.hom x)
      simp

/-- The kernel ideal of the categorical top-and-radical comparison is
square-zero. -/
theorem radicalLayerFunctor_kernelSquareZero :
    QuotientSubmoduleEquidistribution.CategoryTheory.IdempotentLifting.FunctorKernelSquareZero
      (radicalLayerFunctor R) := by
  intro X Y Z f g hf hg
  change layerMap f.hom =
    (0 : RadicalLayerHom (R := R) X Y) at hf
  change layerMap g.hom =
    (0 : RadicalLayerHom (R := R) Y Z) at hg
  ext m
  exact LinearMap.congr_fun
    (comp_eq_zero_of_layerMap_eq_zero f.hom g.hom hf hg) m

end QuotientSubmoduleEquidistribution.ModuleRadicalLayerFunctor
