import Mathlib.RingTheory.Morita.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Restricting a Morita equivalence to finitely generated modules

For modules over Artinian rings, finite generation is equivalent to the
ascending chain condition.  The latter is invariant under a category
equivalence because such an equivalence induces an order isomorphism on
subobjects.  This gives a restriction of Mathlib's `MoritaEquivalence`,
whose datum lives on all `ModuleCat`s, to `FGModuleCat`.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.MoritaRestriction

universe uK uA uB

section Order

variable {α : Type*} {β : Type*} [PartialOrder α] [PartialOrder β]

/-- Well-foundedness of strict descent is invariant under an order
isomorphism. -/
theorem wellFoundedGT_iff_of_orderIso (e : α ≃o β) :
    WellFoundedGT α ↔ WellFoundedGT β := by
  rw [wellFoundedGT_iff_monotone_chain_condition,
    wellFoundedGT_iff_monotone_chain_condition]
  constructor
  · intro h f
    let g : ℕ →o α :=
      ⟨fun n ↦ e.symm (f n), e.symm.monotone.comp f.monotone⟩
    obtain ⟨n, hn⟩ := h g
    exact ⟨n, fun m hm ↦ e.symm.injective (hn m hm)⟩
  · intro h f
    let g : ℕ →o β :=
      ⟨fun n ↦ e (f n), e.monotone.comp f.monotone⟩
    obtain ⟨n, hn⟩ := h g
    exact ⟨n, fun m hm ↦ e.injective (hn m hm)⟩

end Order

section Equivalence

variable {A : Type uA} [Ring A] {B : Type uB} [Ring B]

/-- A category equivalence of module categories induces the expected order
isomorphism between the lattices of algebraic submodules. -/
def submoduleOrderIso
    (e : ModuleCat.{max uA uB} A ≌ ModuleCat.{max uA uB} B)
    (M : ModuleCat.{max uA uB} A) :
    Submodule A M ≃o Submodule B (e.functor.obj M) :=
  (ModuleCat.subobjectModule M).symm |>.trans
    ((Subobject.lowerEquivalence
      (MonoOver.congr M e)).toOrderIso) |>.trans
    (ModuleCat.subobjectModule (e.functor.obj M))

/-- An equivalence between module categories over Artinian rings preserves
finite generation. -/
theorem finite_map
    [IsArtinianRing A] [IsArtinianRing B]
    (e : ModuleCat.{max uA uB} A ≌ ModuleCat.{max uA uB} B)
    (M : ModuleCat.{max uA uB} A)
    (hM : Module.Finite A M) :
    Module.Finite B (e.functor.obj M) := by
  have hnoethA : IsNoetherian A M :=
    ((IsArtinianRing.tfae A M).out 0 1).mp hM
  have hwfA : WellFoundedGT (Submodule A M) :=
    isNoetherian_iff'.mp hnoethA
  have hwfB : WellFoundedGT
      (Submodule B (e.functor.obj M)) :=
    (wellFoundedGT_iff_of_orderIso
      (submoduleOrderIso e M)).mp hwfA
  have hnoethB : IsNoetherian B (e.functor.obj M) :=
    isNoetherian_iff'.mpr hwfB
  exact ((IsArtinianRing.tfae B (e.functor.obj M)).out 0 1).mpr
    hnoethB

/-- An equivalence between module categories over Artinian rings preserves
and reflects finite generation. -/
theorem finite_map_iff
    [IsArtinianRing A] [IsArtinianRing B]
    (e : ModuleCat.{max uA uB} A ≌ ModuleCat.{max uA uB} B)
    (M : ModuleCat.{max uA uB} A) :
    Module.Finite B (e.functor.obj M) ↔ Module.Finite A M := by
  constructor
  · intro h
    have h' : Module.Finite A
        (e.inverse.obj (e.functor.obj M)) :=
      finite_map e.symm (e.functor.obj M) h
    letI : Module.Finite A ((e.functor ⋙ e.inverse).obj M) := h'
    exact Module.Finite.equiv
      (e.unitIso.app M).symm.toLinearEquiv
  · exact finite_map e M

/-- The object property of finite generation is closed under module
isomorphisms.  This instance is not currently supplied by
`FGModuleCat.Basic`. -/
instance isFG_isClosedUnderIsomorphisms (R : Type*) [Ring R] :
    (ModuleCat.isFG R).IsClosedUnderIsomorphisms where
  of_iso i h := by
    change Module.Finite R _ at h ⊢
    letI := h
    exact Module.Finite.equiv i.toLinearEquiv

/-- Under an equivalence of module categories over Artinian rings, the
inverse image of the finitely-generated object property is exactly the
finitely-generated object property. -/
theorem inverseImage_isFG_eq
    [IsArtinianRing A] [IsArtinianRing B]
    (e : ModuleCat.{max uA uB} A ≌ ModuleCat.{max uA uB} B) :
    (ModuleCat.isFG B).inverseImage e.functor =
      ModuleCat.isFG A := by
  funext M
  apply propext
  exact finite_map_iff e M

/-- Restriction of an arbitrary equivalence of module categories over
Artinian rings to the full subcategories of finitely generated modules. -/
def fgEquivalence
    [IsArtinianRing A] [IsArtinianRing B]
    (e : ModuleCat.{max uA uB} A ≌ ModuleCat.{max uA uB} B) :
    FGModuleCat.{max uA uB} A ≌ FGModuleCat.{max uA uB} B :=
  e.congrFullSubcategory (inverseImage_isFG_eq e)

end Equivalence

section Morita

variable (K : Type uK) [CommSemiring K]
  (A : Type uA) [Ring A] [Algebra K A]
  (B : Type uB) [Ring B] [Algebra K B]
  [IsArtinianRing A] [IsArtinianRing B]

/-- Mathlib's Morita equivalence restricted to finitely generated module
categories. -/
def _root_.MoritaEquivalence.fgEquivalence
    (e : MoritaEquivalence K A B) :
    FGModuleCat.{max uA uB} A ≌ FGModuleCat.{max uA uB} B :=
  OpConjecture.MoritaRestriction.fgEquivalence e.eqv

end Morita

section FiniteDimensionalMorita

variable (K : Type uK) [Field K]
  (A : Type uA) [Ring A] [Algebra K A] [FiniteDimensional K A]
  (B : Type uB) [Ring B] [Algebra K B] [FiniteDimensional K B]

/-- The paper-facing specialization: a Morita equivalence between
finite-dimensional algebras restricts to their finitely generated module
categories, with Artinianity discharged from finite dimensionality. -/
def _root_.MoritaEquivalence.finiteDimensionalFgEquivalence
    (e : MoritaEquivalence K A B) :
    FGModuleCat.{max uA uB} A ≌ FGModuleCat.{max uA uB} B := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  exact e.fgEquivalence

end FiniteDimensionalMorita

end OpConjecture.MoritaRestriction
