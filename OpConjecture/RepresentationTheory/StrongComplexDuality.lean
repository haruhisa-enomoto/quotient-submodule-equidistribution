import OpConjecture.RepresentationTheory.ShortComplexDuality
import Mathlib.CategoryTheory.ObjectProperty.Opposite
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Restricting an anti-equivalence to mutually exact objects

The construction is abstract: for an anti-equivalence `A : Cᵒᵖ ≌ D`
and isomorphism-invariant object properties `P` and `Q`, the objects of `C`
for which both `P X` and `Q (A X)` hold are anti-equivalent to the analogous
objects of `D`.  Applied to ambient exactness of projective short complexes,
this proves that degreewise projective Hom duality sends Ringel's category
`E(Λ)` anti-equivalently to the corresponding category on the opposite side.
-/

noncomputable section

open CategoryTheory Opposite

namespace OpConjecture.RingelEta

universe u v u' v'

section Abstract

variable {C : Type u} {D : Type u'}
  [Category.{v} C] [Category.{v'} D]

/-- Objects on the source side satisfying a property together with the
target property after applying an anti-equivalence. -/
def antiStrongLeftProperty
    (A : Cᵒᵖ ≌ D) (P : ObjectProperty C) (Q : ObjectProperty D) :
    ObjectProperty C :=
  fun X ↦ P X ∧ Q (A.functor.obj (Opposite.op X))

/-- The symmetric object property on the target side. -/
def antiStrongRightProperty
    (A : Cᵒᵖ ≌ D) (P : ObjectProperty C) (Q : ObjectProperty D) :
    ObjectProperty D :=
  fun Y ↦ Q Y ∧
    P ((A.rightOp.symm).functor.obj (Opposite.op Y))

instance antiStrongLeftProperty_isoClosed
    (A : Cᵒᵖ ≌ D) (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms] :
    (antiStrongLeftProperty A P Q).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    refine ⟨P.prop_of_iso e hX.1, ?_⟩
    exact Q.prop_of_iso (A.functor.mapIso e.op).symm hX.2

instance antiStrongRightProperty_isoClosed
    (A : Cᵒᵖ ≌ D) (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms] :
    (antiStrongRightProperty A P Q).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    refine ⟨Q.prop_of_iso e hX.1, ?_⟩
    exact P.prop_of_iso
      ((A.rightOp.symm).functor.mapIso e.op).symm hX.2

/-- The target mutually-exact property pulls back to the opposite of the
source mutually-exact property.  The only non-definitional step is the unit
isomorphism of the ambient anti-equivalence. -/
theorem antiStrongRight_inverseImage
    (A : Cᵒᵖ ≌ D) (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] :
    (antiStrongRightProperty A P Q).inverseImage A.functor =
      (antiStrongLeftProperty A P Q).op := by
  ext X
  constructor
  · rintro ⟨hQ, hP⟩
    refine ⟨?_, hQ⟩
    exact P.prop_of_iso (A.unitIso.app X).unop hP
  · rintro ⟨hP, hQ⟩
    refine ⟨hQ, ?_⟩
    exact P.prop_of_iso (A.unitIso.app X).unop.symm hP

/-- Restriction of an anti-equivalence to the objects satisfying a property
and whose duals satisfy the opposite property. -/
def antiStrongEquivalence
    (A : Cᵒᵖ ≌ D) (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms] :
    (antiStrongLeftProperty A P Q).FullSubcategoryᵒᵖ ≌
      (antiStrongRightProperty A P Q).FullSubcategory :=
  (ObjectProperty.opEquivalence
      (antiStrongLeftProperty A P Q)).symm |>.trans
    (A.congrFullSubcategory
      (antiStrongRight_inverseImage A P Q))

end Abstract

section ProjectiveComplexes

open OpConjecture.RingelStable

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {S : Type u'} [Ring S] [IsNoetherianRing S]

/-- Ambient exactness as an isomorphism-invariant object property of
projective short complexes. -/
def projectiveComplexExactProperty (R : Type u)
    [Ring R] [IsNoetherianRing R] :
    ObjectProperty (ProjectiveComplex R) :=
  fun P ↦ P.Exact

instance projectiveComplexExactProperty_isoClosed :
    (projectiveComplexExactProperty R).IsClosedUnderIsomorphisms where
  of_iso e h := h.isoInvariant e

/-- The target-side strong exactness property formed using the inverse
anti-equivalence. -/
def targetStronglyExactProperty
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    ObjectProperty (ProjectiveComplex S) :=
  antiStrongRightProperty
    (mapShortComplexAntiEquivalence H)
    (projectiveComplexExactProperty R)
    (projectiveComplexExactProperty S)

theorem stronglyExactProperty_eq_antiStrongLeft
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    stronglyExactProperty H =
      antiStrongLeftProperty
        (mapShortComplexAntiEquivalence H)
        (projectiveComplexExactProperty R)
        (projectiveComplexExactProperty S) :=
  rfl

/-- Degreewise projective Hom duality gives an anti-equivalence between
the strongly exact projective complexes on the two sides. -/
def stronglyExactComplexAntiEquivalence
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    (StronglyExactComplexCategory H)ᵒᵖ ≌
      (targetStronglyExactProperty H).FullSubcategory :=
  antiStrongEquivalence
    (mapShortComplexAntiEquivalence H)
    (projectiveComplexExactProperty R)
    (projectiveComplexExactProperty S)

section Ringel

variable [IsNoetherianRing Rᵐᵒᵖ]

/-- The formal `Hom(-,Λ)` anti-equivalence on Ringel's strongly exact
complex category `E(Λ)`. -/
abbrev ringelEStrongHomAntiEquivalence :
    (RingelE (R := R))ᵒᵖ ≌
      (targetStronglyExactProperty
        (regularHomProjectiveAntiEquivalence (R := R))).FullSubcategory :=
  stronglyExactComplexAntiEquivalence
    (regularHomProjectiveAntiEquivalence (R := R))

end Ringel

end ProjectiveComplexes

end OpConjecture.RingelEta
