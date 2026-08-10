import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import OpConjecture.RepresentationTheory.AuslanderEquivalence
import OpConjecture.RepresentationTheory.RejectiveEquivalenceTransport
import OpConjecture.RepresentationTheory.RejectiveLattice

/-!
# Generic additive, summand-closed, rejective subcategories

This module removes the module-specific restriction from the
Auslander--rejective target.  It provides:

* a generic poset of object properties closed under finite biproducts
  and retracts;
* an order isomorphism on this poset along an equivalence of
  preadditive categories with finite biproducts;
* restrictions of that order isomorphism to all categorically right-
  and left-rejective additive subcategories; and
* literal order isomorphisms from the existing finitely generated
  module packages to the generic packages.

No essential-image subtype is used: equivalence transport is proved
surjective on the entire generic target poset.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace OpConjecture.CategoricalAdditiveSubcategory

universe vC vD uC uD

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasFiniteBiproducts C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasFiniteBiproducts D]

/-- A full, replete additive subcategory represented by its object
property.  Finite-biproduct closure includes the empty biproduct;
retract closure implies repleteness. -/
structure Subcategory (C : Type uC) [Category.{vC} C]
    [Preadditive C] [HasFiniteBiproducts C] where
  carrier : ObjectProperty C
  biproduct_mem :
    ∀ (J : FintypeCat.{0}) (F : J → C),
      (∀ j, carrier (F j)) → carrier (biproduct F)
  retract_mem :
    ∀ {X Y : C}, Retract X Y → carrier Y → carrier X

omit [HasFiniteBiproducts D] in
/-- A category equivalent to a preadditive category with finite
biproducts itself has finite biproducts.  Additivity of the equivalence
functor is obtained from preservation of binary products. -/
theorem hasFiniteBiproductsOfEquivalence (E : C ≌ D) :
    HasFiniteBiproducts D := by
  letI : E.functor.Additive :=
    Functor.additive_of_preserves_binary_products E.functor
  letI : HasFiniteProducts D :=
    Functor.hasFiniteProducts_of_additive_of_essSurj E.functor
  exact HasFiniteBiproducts.of_hasFiniteProducts

namespace Subcategory

/-- The literal full subcategory determined by the carrier. -/
abbrev FullSubcategory (P : Subcategory C) :=
  P.carrier.FullSubcategory

/-- Retract closure entails closure under isomorphisms. -/
theorem iso_mem (P : Subcategory C)
    {X Y : C} (e : X ≅ Y) (hX : P.carrier X) :
    P.carrier Y :=
  P.retract_mem (Retract.ofIso e.symm) hX

/-- The carrier of a generic additive subcategory is replete. -/
instance carrier_isClosedUnderIsomorphisms
    (P : Subcategory C) :
    P.carrier.IsClosedUnderIsomorphisms where
  of_iso := fun e h ↦ P.iso_mem e h

@[ext]
theorem ext {P Q : Subcategory C}
    (h : ∀ X, P.carrier X ↔ Q.carrier X) :
    P = Q := by
  cases P with
  | mk P hPb hPr =>
    cases Q with
    | mk Q hQb hQr =>
      have hPQ : P = Q := by
        funext X
        exact propext (h X)
      subst hPQ
      rfl

instance : LE (Subcategory C) where
  le P Q := P.carrier ≤ Q.carrier

instance : PartialOrder (Subcategory C) where
  le_refl P := fun _ h ↦ h
  le_trans P Q T hPQ hQT := fun X hX ↦ hQT X (hPQ X hX)
  le_antisymm P Q hPQ hQP :=
    ext fun X ↦ ⟨hPQ X, hQP X⟩

/-- Replete image of a generic additive subcategory under an ambient
equivalence. -/
def transport (E : C ≌ D) (P : Subcategory C) :
    Subcategory D where
  carrier :=
    CategoricalRejective.imageProperty E P.carrier
  biproduct_mem J F hF := by
    letI : PreservesBiproduct F E.inverse :=
      preservesBiproduct_of_preservesProduct E.inverse
    apply P.iso_mem (E.inverse.mapBiproduct F).symm
    exact P.biproduct_mem J
      (fun j ↦ E.inverse.obj (F j)) hF
  retract_mem r hY :=
    P.retract_mem (r.map E.inverse) hY

@[simp]
theorem transport_carrier
    (E : C ≌ D) (P : Subcategory C) :
    (P.transport E).carrier =
      CategoricalRejective.imageProperty E P.carrier :=
  rfl

/-- Transport is monotone. -/
theorem transport_monotone (E : C ≌ D) :
    Monotone (transport E : Subcategory C → Subcategory D) := by
  intro P Q hPQ Y hY
  exact hPQ (E.inverse.obj Y) hY

/-- Pulling a transported additive subcategory back through the inverse
equivalence recovers it. -/
theorem transport_symm_transport
    (E : C ≌ D) (P : Subcategory C) :
    (P.transport E).transport E.symm = P := by
  apply ext
  intro X
  change
    P.carrier (E.inverse.obj (E.functor.obj X)) ↔
      P.carrier X
  exact
    ⟨fun h ↦ P.iso_mem (E.unitIso.app X).symm h,
      fun h ↦ P.iso_mem (E.unitIso.app X) h⟩

/-- Transporting back after pullback likewise recovers the target
subcategory. -/
theorem transport_transport_symm
    (E : C ≌ D) (Q : Subcategory D) :
    (Q.transport E.symm).transport E = Q := by
  apply ext
  intro Y
  change
    Q.carrier (E.functor.obj (E.inverse.obj Y)) ↔
      Q.carrier Y
  exact
    ⟨fun h ↦ Q.iso_mem (E.counitIso.app Y) h,
      fun h ↦ Q.iso_mem (E.counitIso.app Y).symm h⟩

/-- Equivalence transport is an order isomorphism on all generic
additive, replete, summand-closed subcategories. -/
def transportOrderIso (E : C ≌ D) :
    Subcategory C ≃o Subcategory D where
  toFun := transport E
  invFun := transport E.symm
  left_inv := transport_symm_transport E
  right_inv := transport_transport_symm E
  map_rel_iff' := by
    intro P Q
    constructor
    · intro h
      rw [← transport_symm_transport E P,
        ← transport_symm_transport E Q]
      exact transport_monotone E.symm h
    · intro h
      exact transport_monotone E h

end Subcategory

/-- All generic additive subcategories which are categorically right
rejective in their ambient category. -/
abbrev RightRejectiveSubcategory
    (C : Type uC) [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C] :=
  {P : Subcategory C //
    CategoricalRejective.IsRightRejective P.carrier}

/-- All generic additive subcategories which are categorically left
rejective in their ambient category. -/
abbrev LeftRejectiveSubcategory
    (C : Type uC) [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C] :=
  {P : Subcategory C //
    CategoricalRejective.IsLeftRejective P.carrier}

/-- Ambient equivalence transport is an order isomorphism on all
right-rejective additive subcategories. -/
def rightRejectiveTransportOrderIso (E : C ≌ D) :
    RightRejectiveSubcategory C ≃o
      RightRejectiveSubcategory D where
  toFun P :=
    ⟨P.1.transport E,
      (CategoricalRejective.Equivalence.isRightRejective_iff_image
        E P.1.carrier).1 P.2⟩
  invFun Q :=
    ⟨Q.1.transport E.symm,
      (CategoricalRejective.Equivalence.isRightRejective_iff_image
        E.symm Q.1.carrier).1 Q.2⟩
  left_inv P := by
    apply Subtype.ext
    exact Subcategory.transport_symm_transport E P.1
  right_inv Q := by
    apply Subtype.ext
    exact Subcategory.transport_transport_symm E Q.1
  map_rel_iff' := by
    intro P Q
    exact (Subcategory.transportOrderIso E).le_iff_le

@[simp]
theorem rightRejectiveTransportOrderIso_carrier
    (E : C ≌ D) (P : RightRejectiveSubcategory C) :
    (rightRejectiveTransportOrderIso E P).1.carrier =
      CategoricalRejective.imageProperty E P.1.carrier :=
  rfl

/-- Ambient equivalence transport is an order isomorphism on all
left-rejective additive subcategories. -/
def leftRejectiveTransportOrderIso (E : C ≌ D) :
    LeftRejectiveSubcategory C ≃o
      LeftRejectiveSubcategory D where
  toFun P :=
    ⟨P.1.transport E,
      (CategoricalRejective.Equivalence.isLeftRejective_iff_image
        E P.1.carrier).1 P.2⟩
  invFun Q :=
    ⟨Q.1.transport E.symm,
      (CategoricalRejective.Equivalence.isLeftRejective_iff_image
        E.symm Q.1.carrier).1 Q.2⟩
  left_inv P := by
    apply Subtype.ext
    exact Subcategory.transport_symm_transport E P.1
  right_inv Q := by
    apply Subtype.ext
    exact Subcategory.transport_transport_symm E Q.1
  map_rel_iff' := by
    intro P Q
    exact (Subcategory.transportOrderIso E).le_iff_le

@[simp]
theorem leftRejectiveTransportOrderIso_carrier
    (E : C ≌ D) (P : LeftRejectiveSubcategory C) :
    (leftRejectiveTransportOrderIso E P).1.carrier =
      CategoricalRejective.imageProperty E P.1.carrier :=
  rfl

end OpConjecture.CategoricalAdditiveSubcategory

namespace OpConjecture.CategoricalAdditiveSubcategory.ModuleBridge

universe uR w vD uD vι

variable {R : Type uR} [Ring R] [IsNoetherianRing R]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Forget that the generic additive-subcategory structure was first
defined specifically for finitely generated modules. -/
def ofFGModuleSubcategory
    (P :
      IndecomposableSkeleton.AdditiveRepleteSummandSubcategory.{uR, w}
        (R := R)) :
    Subcategory (FGModuleCat.{w} R) where
  carrier := P.carrier
  biproduct_mem := P.biproduct_mem
  retract_mem := P.retract_mem

/-- Recover the existing module-specific package from the generic
categorical package. -/
def toFGModuleSubcategory
    (P : Subcategory (FGModuleCat.{w} R)) :
    IndecomposableSkeleton.AdditiveRepleteSummandSubcategory.{uR, w}
      (R := R) where
  carrier := P.carrier
  biproduct_mem := P.biproduct_mem
  retract_mem := P.retract_mem

/-- The module-specific and generic additive-subcategory posets are
literally order-isomorphic. -/
def fgModuleSubcategoryOrderIso :
    IndecomposableSkeleton.AdditiveRepleteSummandSubcategory.{uR, w}
        (R := R) ≃o
      Subcategory (FGModuleCat.{w} R) where
  toFun := ofFGModuleSubcategory
  invFun := toFGModuleSubcategory
  left_inv P := by
    cases P
    rfl
  right_inv P := by
    cases P
    rfl
  map_rel_iff' := by
    intro P Q
    rfl

/-- The existing module-specific right-rejective poset is the generic
categorical right-rejective poset. -/
def fgModuleRightRejectiveOrderIso :
    IndecomposableSkeleton.RightRejectiveAdditiveSubcategory.{uR, w}
        (R := R) ≃o
      RightRejectiveSubcategory (FGModuleCat.{w} R) where
  toFun P :=
    ⟨ofFGModuleSubcategory P.1,
      (IndecomposableSkeleton.isRightRejective_iff_categorical
        P.1).1 P.2⟩
  invFun P :=
    ⟨toFGModuleSubcategory P.1,
      (IndecomposableSkeleton.isRightRejective_iff_categorical
        (toFGModuleSubcategory P.1)).2 P.2⟩
  left_inv P := by
    apply Subtype.ext
    exact fgModuleSubcategoryOrderIso.left_inv P.1
  right_inv P := by
    apply Subtype.ext
    exact fgModuleSubcategoryOrderIso.right_inv P.1
  map_rel_iff' := by
    intro P Q
    exact fgModuleSubcategoryOrderIso.le_iff_le

/-- The existing module-specific left-rejective poset is the generic
categorical left-rejective poset. -/
def fgModuleLeftRejectiveOrderIso :
    IndecomposableSkeleton.LeftRejectiveAdditiveSubcategory.{uR, w}
        (R := R) ≃o
      LeftRejectiveSubcategory (FGModuleCat.{w} R) where
  toFun P :=
    ⟨ofFGModuleSubcategory P.1,
      (IndecomposableSkeleton.isLeftRejective_iff_categorical
        P.1).1 P.2⟩
  invFun P :=
    ⟨toFGModuleSubcategory P.1,
      (IndecomposableSkeleton.isLeftRejective_iff_categorical
        (toFGModuleSubcategory P.1)).2 P.2⟩
  left_inv P := by
    apply Subtype.ext
    exact fgModuleSubcategoryOrderIso.left_inv P.1
  right_inv P := by
    apply Subtype.ext
    exact fgModuleSubcategoryOrderIso.right_inv P.1
  map_rel_iff' := by
    intro P Q
    exact fgModuleSubcategoryOrderIso.le_iff_le

variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasFiniteBiproducts D]

/-- Every module-side right-rejective additive subcategory, and every
right-rejective additive subcategory of an equivalent target, correspond
under a single order isomorphism. -/
def fgModuleRightRejectiveTransportOrderIso
    (E : FGModuleCat.{w} R ≌ D) :
    IndecomposableSkeleton.RightRejectiveAdditiveSubcategory.{uR, w}
        (R := R) ≃o
      RightRejectiveSubcategory D :=
  fgModuleRightRejectiveOrderIso.trans
    (rightRejectiveTransportOrderIso E)

/-- Dual all-target transport for left-rejective additive
subcategories. -/
def fgModuleLeftRejectiveTransportOrderIso
    (E : FGModuleCat.{w} R ≌ D) :
    IndecomposableSkeleton.LeftRejectiveAdditiveSubcategory.{uR, w}
        (R := R) ≃o
      LeftRejectiveSubcategory D :=
  fgModuleLeftRejectiveOrderIso.trans
    (leftRejectiveTransportOrderIso E)

omit [IsNoetherianRing R] in
@[simp]
theorem fgModuleRightRejectiveTransportOrderIso_carrier
    (E : FGModuleCat.{w} R ≌ D)
    (P :
      IndecomposableSkeleton.RightRejectiveAdditiveSubcategory.{uR, w}
        (R := R)) :
    (fgModuleRightRejectiveTransportOrderIso E P).1.carrier =
      CategoricalRejective.imageProperty E P.1.carrier :=
  rfl

omit [IsNoetherianRing R] in
@[simp]
theorem fgModuleLeftRejectiveTransportOrderIso_carrier
    (E : FGModuleCat.{w} R ≌ D)
    (P :
      IndecomposableSkeleton.LeftRejectiveAdditiveSubcategory.{uR, w}
        (R := R)) :
    (fgModuleLeftRejectiveTransportOrderIso E P).1.carrier =
      CategoricalRejective.imageProperty E P.1.carrier :=
  rfl

variable {ι : Type vι}
  (σ : IndecomposableSkeleton.{uR, vι, w} R ι)

/-- Quotient-closed literal module subcategories correspond to all
right-rejective additive subcategories of any equivalent preadditive
target. -/
def quotientClosedTargetRightRejectiveOrderIso
    (E : FGModuleCat.{w} R ≌ D) :
    IndecomposableSkeleton.QuotientClosedAdditiveSubcategory.{uR, w}
        (R := R) ≃o
      RightRejectiveSubcategory D :=
  (IndecomposableSkeleton.quotientClosedRightRejectiveOrderIso
    σ).trans
      (fgModuleRightRejectiveTransportOrderIso E)

/-- Support-poset form of the all-target quotient/rejective bridge. -/
def qClosedSupportTargetRightRejectiveOrderIso
    (E : FGModuleCat.{w} R ≌ D) :
    σ.qClosure.Closeds ≃o RightRejectiveSubcategory D :=
  (IndecomposableSkeleton.qClosedSupportRightRejectiveOrderIso
    σ).trans
      (fgModuleRightRejectiveTransportOrderIso E)

/-- Subobject-closed literal module subcategories correspond to all
left-rejective additive target subcategories. -/
def subobjectClosedTargetLeftRejectiveOrderIso
    (hfinite : ∀ X : FGModuleCat.{w} R,
      IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D) :
    IndecomposableSkeleton.SubobjectClosedAdditiveSubcategory.{uR, w}
        (R := R) ≃o
      LeftRejectiveSubcategory D :=
  (IndecomposableSkeleton.subobjectClosedLeftRejectiveOrderIso
    σ hfinite).trans
      (fgModuleLeftRejectiveTransportOrderIso E)

/-- Support-poset form of the all-target subobject/rejective bridge. -/
def sClosedSupportTargetLeftRejectiveOrderIso
    (hfinite : ∀ X : FGModuleCat.{w} R,
      IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D) :
    σ.sClosure.Closeds ≃o LeftRejectiveSubcategory D :=
  (IndecomposableSkeleton.sClosedSupportLeftRejectiveOrderIso
    σ hfinite).trans
      (fgModuleLeftRejectiveTransportOrderIso E)

/-! ## Finite-type Auslander target -/

/-- The finite-projective target of the Auslander equivalence attached
to a finite indecomposable skeleton. -/
abbrev FiniteTypeProjectiveTarget [Finite ι] :=
  (AuslanderEquivalence.finiteProjectiveModules
    (End
      (AuslanderEquivalence.FiniteTypeGenerator.additiveGenerator
        σ))ᵐᵒᵖ).FullSubcategory

/-- Literal quotient-closed subcategories correspond to all additive
right-rejective subcategories of the finite-projective Auslander
target. -/
def finiteTypeQuotientClosedProjectiveRightRejectiveOrderIso
    [Finite ι] :
    let E :=
      AuslanderEquivalence.FiniteTypeGenerator.auslanderEquivalence
        σ
    letI : HasFiniteBiproducts (FiniteTypeProjectiveTarget σ) :=
      hasFiniteBiproductsOfEquivalence E
    IndecomposableSkeleton.QuotientClosedAdditiveSubcategory.{uR, w}
        (R := R) ≃o
      RightRejectiveSubcategory (FiniteTypeProjectiveTarget σ) := by
  let E :=
    AuslanderEquivalence.FiniteTypeGenerator.auslanderEquivalence
      σ
  letI : HasFiniteBiproducts (FiniteTypeProjectiveTarget σ) :=
    hasFiniteBiproductsOfEquivalence E
  exact quotientClosedTargetRightRejectiveOrderIso σ E

/-- Support-poset form of the all-target finite-type quotient bridge. -/
def finiteTypeQClosedSupportProjectiveRightRejectiveOrderIso
    [Finite ι] :
    let E :=
      AuslanderEquivalence.FiniteTypeGenerator.auslanderEquivalence
        σ
    letI : HasFiniteBiproducts (FiniteTypeProjectiveTarget σ) :=
      hasFiniteBiproductsOfEquivalence E
    σ.qClosure.Closeds ≃o
      RightRejectiveSubcategory (FiniteTypeProjectiveTarget σ) := by
  let E :=
    AuslanderEquivalence.FiniteTypeGenerator.auslanderEquivalence
      σ
  letI : HasFiniteBiproducts (FiniteTypeProjectiveTarget σ) :=
    hasFiniteBiproductsOfEquivalence E
  exact qClosedSupportTargetRightRejectiveOrderIso σ E

/-- Literal subobject-closed subcategories correspond to all additive
left-rejective subcategories of the finite-projective Auslander target. -/
def finiteTypeSubobjectClosedProjectiveLeftRejectiveOrderIso
    [Finite ι]
    (hfinite : ∀ X : FGModuleCat.{w} R,
      IsFiniteLength R X) :
    let E :=
      AuslanderEquivalence.FiniteTypeGenerator.auslanderEquivalence
        σ
    letI : HasFiniteBiproducts (FiniteTypeProjectiveTarget σ) :=
      hasFiniteBiproductsOfEquivalence E
    IndecomposableSkeleton.SubobjectClosedAdditiveSubcategory.{uR, w}
        (R := R) ≃o
      LeftRejectiveSubcategory (FiniteTypeProjectiveTarget σ) := by
  let E :=
    AuslanderEquivalence.FiniteTypeGenerator.auslanderEquivalence
      σ
  letI : HasFiniteBiproducts (FiniteTypeProjectiveTarget σ) :=
    hasFiniteBiproductsOfEquivalence E
  exact
    subobjectClosedTargetLeftRejectiveOrderIso σ hfinite E

/-- Support-poset form of the all-target finite-type left bridge. -/
def finiteTypeSClosedSupportProjectiveLeftRejectiveOrderIso
    [Finite ι]
    (hfinite : ∀ X : FGModuleCat.{w} R,
      IsFiniteLength R X) :
    let E :=
      AuslanderEquivalence.FiniteTypeGenerator.auslanderEquivalence
        σ
    letI : HasFiniteBiproducts (FiniteTypeProjectiveTarget σ) :=
      hasFiniteBiproductsOfEquivalence E
    σ.sClosure.Closeds ≃o
      LeftRejectiveSubcategory (FiniteTypeProjectiveTarget σ) := by
  let E :=
    AuslanderEquivalence.FiniteTypeGenerator.auslanderEquivalence
      σ
  letI : HasFiniteBiproducts (FiniteTypeProjectiveTarget σ) :=
    hasFiniteBiproductsOfEquivalence E
  exact
    sClosedSupportTargetLeftRejectiveOrderIso σ hfinite E

/-! ## Canonical finite-dimensional right-module specialization -/

section CanonicalRightModules

universe uK uA

variable (K : Type uK) (A : Type uA)
  [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A]

/-- Exact paper-facing quotient/right-rejective order isomorphism.  The
target consists of all additive, replete, summand-closed right-rejective
subcategories of the finitely generated projective right modules over
`End(G)`. -/
def canonicalRightModuleQuotientClosedProjectiveRightRejectiveOrderIso
    (hrep : IsRightRepresentationFinite.{uK, uA, w} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite
        (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
      hrep
    let σ :=
      rightIndecomposableSkeleton.{uK, uA, w} K A
    let E :=
      AuslanderEquivalence.FiniteTypeGenerator.auslanderEquivalence σ
    letI : HasFiniteBiproducts (FiniteTypeProjectiveTarget σ) :=
      hasFiniteBiproductsOfEquivalence E
    IndecomposableSkeleton.QuotientClosedAdditiveSubcategory
        (R := Aᵐᵒᵖ) ≃o
      RightRejectiveSubcategory (FiniteTypeProjectiveTarget σ) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite
      (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
    hrep
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, w} K A
  exact finiteTypeQuotientClosedProjectiveRightRejectiveOrderIso σ

/-- Support-poset form of the canonical quotient/right-rejective bridge. -/
def canonicalRightModuleQClosedSupportProjectiveRightRejectiveOrderIso
    (hrep : IsRightRepresentationFinite.{uK, uA, w} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite
        (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
      hrep
    let σ :=
      rightIndecomposableSkeleton.{uK, uA, w} K A
    let E :=
      AuslanderEquivalence.FiniteTypeGenerator.auslanderEquivalence σ
    letI : HasFiniteBiproducts (FiniteTypeProjectiveTarget σ) :=
      hasFiniteBiproductsOfEquivalence E
    σ.qClosure.Closeds ≃o
      RightRejectiveSubcategory (FiniteTypeProjectiveTarget σ) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite
      (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
    hrep
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, w} K A
  exact finiteTypeQClosedSupportProjectiveRightRejectiveOrderIso σ

/-- Exact dual subobject/left-rejective order isomorphism. -/
def canonicalRightModuleSubobjectClosedProjectiveLeftRejectiveOrderIso
    (hrep : IsRightRepresentationFinite.{uK, uA, w} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite
        (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
      hrep
    let σ :=
      rightIndecomposableSkeleton.{uK, uA, w} K A
    let E :=
      AuslanderEquivalence.FiniteTypeGenerator.auslanderEquivalence σ
    letI : HasFiniteBiproducts (FiniteTypeProjectiveTarget σ) :=
      hasFiniteBiproductsOfEquivalence E
    IndecomposableSkeleton.SubobjectClosedAdditiveSubcategory
        (R := Aᵐᵒᵖ) ≃o
      LeftRejectiveSubcategory (FiniteTypeProjectiveTarget σ) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite
      (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
    hrep
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, w} K A
  exact
    finiteTypeSubobjectClosedProjectiveLeftRejectiveOrderIso σ
      (fun X ↦ isFiniteLength_rightFGModule K A X)

/-- Support-poset form of the canonical subobject/left-rejective bridge. -/
def canonicalRightModuleSClosedSupportProjectiveLeftRejectiveOrderIso
    (hrep : IsRightRepresentationFinite.{uK, uA, w} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite
        (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
      hrep
    let σ :=
      rightIndecomposableSkeleton.{uK, uA, w} K A
    let E :=
      AuslanderEquivalence.FiniteTypeGenerator.auslanderEquivalence σ
    letI : HasFiniteBiproducts (FiniteTypeProjectiveTarget σ) :=
      hasFiniteBiproductsOfEquivalence E
    σ.sClosure.Closeds ≃o
      LeftRejectiveSubcategory (FiniteTypeProjectiveTarget σ) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite
      (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
    hrep
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, w} K A
  exact
    finiteTypeSClosedSupportProjectiveLeftRejectiveOrderIso σ
      (fun X ↦ isFiniteLength_rightFGModule K A X)

end CanonicalRightModules

end OpConjecture.CategoricalAdditiveSubcategory.ModuleBridge
