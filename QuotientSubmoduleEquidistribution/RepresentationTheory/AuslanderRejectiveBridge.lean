import QuotientSubmoduleEquidistribution.RepresentationTheory.CanonicalAuslanderEquivalence
import Mathlib.Order.Hom.Set
import QuotientSubmoduleEquidistribution.RepresentationTheory.RejectiveEquivalenceTransport
import QuotientSubmoduleEquidistribution.RepresentationTheory.RejectiveLattice

/-!
# The finite-type Auslander--rejective bridge

This scratch file transports the production rejective-subcategory order
isomorphisms across the finite-type Auslander equivalence.  The target is
the category of finitely generated projective left modules over
`(End G)ᵐᵒᵖ`, equivalently finitely generated projective right modules over
`End G`.
-/

noncomputable section

open Set
open CategoryTheory

namespace QuotientSubmoduleEquidistribution.AuslanderEquivalence.RejectiveBridge

universe uR w vD uD vι

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {D : Type uD} [Category.{vD} D]

/-- Sending a module-side right-rejective literal subcategory to its
replete image under an equivalence is an order embedding into target object
properties. -/
def rightRejectiveImageOrderEmbedding
    (E : FGModuleCat.{w} R ≌ D) :
    IndecomposableSkeleton.RightRejectiveAdditiveSubcategory.{uR, w}
        (R := R) ↪o
      ObjectProperty D :=
  OrderEmbedding.ofMapLEIff
    (fun C ↦
      CategoricalRejective.imageProperty E C.1.carrier)
    (by
      intro C₁ C₂
      constructor
      · intro h X hX
        exact
          C₂.1.iso_mem (E.unitIso.app X).symm
            (h (E.functor.obj X)
              (C₁.1.iso_mem (E.unitIso.app X) hX))
      · intro h Y hY
        exact h (E.inverse.obj Y) hY)

/-- The dual order embedding for left-rejective literal subcategories. -/
def leftRejectiveImageOrderEmbedding
    (E : FGModuleCat.{w} R ≌ D) :
    IndecomposableSkeleton.LeftRejectiveAdditiveSubcategory.{uR, w}
        (R := R) ↪o
      ObjectProperty D :=
  OrderEmbedding.ofMapLEIff
    (fun C ↦
      CategoricalRejective.imageProperty E C.1.carrier)
    (by
      intro C₁ C₂
      constructor
      · intro h X hX
        exact
          C₂.1.iso_mem (E.unitIso.app X).symm
            (h (E.functor.obj X)
              (C₁.1.iso_mem (E.unitIso.app X) hX))
      · intro h Y hY
        exact h (E.inverse.obj Y) hY)

/-- Right-rejective additive subcategories of the target which arise by
transport from the module category.  Defining this as the range records the
exact target alignment and avoids asserting that arbitrary object
properties carry additive/summand-closed structure. -/
abbrev TransportedRightRejectiveAdditiveSubcategory
    (E : FGModuleCat.{w} R ≌ D) :=
  Set.range (rightRejectiveImageOrderEmbedding E)

/-- The transported left-rejective target poset. -/
abbrev TransportedLeftRejectiveAdditiveSubcategory
    (E : FGModuleCat.{w} R ≌ D) :=
  Set.range (leftRejectiveImageOrderEmbedding E)

omit [IsNoetherianRing R] in
/-- Every member of the transported right-hand target is categorically
right rejective in `D`. -/
theorem transportedRight_isRightRejective
    (E : FGModuleCat.{w} R ≌ D)
    (Q : TransportedRightRejectiveAdditiveSubcategory E) :
    CategoricalRejective.IsRightRejective (Q : ObjectProperty D) := by
  obtain ⟨C, hC⟩ := Q.property
  rw [← hC]
  exact
    (IndecomposableSkeleton.isRightRejective_iff_categorical_image
      E C.1).1 C.2

omit [IsNoetherianRing R] in
/-- Every member of the transported left-hand target is categorically left
rejective. -/
theorem transportedLeft_isLeftRejective
    (E : FGModuleCat.{w} R ≌ D)
    (Q : TransportedLeftRejectiveAdditiveSubcategory E) :
    CategoricalRejective.IsLeftRejective (Q : ObjectProperty D) := by
  obtain ⟨C, hC⟩ := Q.property
  rw [← hC]
  exact
    (IndecomposableSkeleton.isLeftRejective_iff_categorical_image
      E C.1).1 C.2

omit [IsNoetherianRing R] in
/-- Transported right-rejective target properties are replete. -/
theorem transportedRight_isClosedUnderIsomorphisms
    (E : FGModuleCat.{w} R ≌ D)
    (Q : TransportedRightRejectiveAdditiveSubcategory E) :
    (Q : ObjectProperty D).IsClosedUnderIsomorphisms := by
  obtain ⟨C, hC⟩ := Q.property
  rw [← hC]
  change
    (CategoricalRejective.imageProperty E C.1.carrier).IsClosedUnderIsomorphisms
  infer_instance

omit [IsNoetherianRing R] in
/-- Transported left-rejective target properties are replete. -/
theorem transportedLeft_isClosedUnderIsomorphisms
    (E : FGModuleCat.{w} R ≌ D)
    (Q : TransportedLeftRejectiveAdditiveSubcategory E) :
    (Q : ObjectProperty D).IsClosedUnderIsomorphisms := by
  obtain ⟨C, hC⟩ := Q.property
  rw [← hC]
  change
    (CategoricalRejective.imageProperty E C.1.carrier).IsClosedUnderIsomorphisms
  infer_instance

variable {ι : Type vι}
  (σ : IndecomposableSkeleton.{uR, vι, w} R ι)

/-- Literal quotient-closed additive subcategories of `mod R` are
order-isomorphic to their transported right-rejective images in any
equivalent target. -/
def quotientClosedTransportedRightRejectiveOrderIso
    (E : FGModuleCat.{w} R ≌ D) :
    IndecomposableSkeleton.QuotientClosedAdditiveSubcategory
        (R := R) ≃o
      TransportedRightRejectiveAdditiveSubcategory E :=
  (IndecomposableSkeleton.quotientClosedRightRejectiveOrderIso σ).trans
    (rightRejectiveImageOrderEmbedding E).orderIso

/-- Support-poset form of the quotient-side bridge. -/
def qClosedSupportTransportedRightRejectiveOrderIso
    (E : FGModuleCat.{w} R ≌ D) :
    σ.qClosure.Closeds ≃o
      TransportedRightRejectiveAdditiveSubcategory E :=
  (IndecomposableSkeleton.qClosedSupportRightRejectiveOrderIso σ).trans
    (rightRejectiveImageOrderEmbedding E).orderIso

/-- Literal subobject-closed additive subcategories transport to the
left-rejective image poset. -/
def subobjectClosedTransportedLeftRejectiveOrderIso
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D) :
    IndecomposableSkeleton.SubobjectClosedAdditiveSubcategory
        (R := R) ≃o
      TransportedLeftRejectiveAdditiveSubcategory E :=
  (IndecomposableSkeleton.subobjectClosedLeftRejectiveOrderIso
      σ hfinite).trans
    (leftRejectiveImageOrderEmbedding E).orderIso

/-- Support-poset form of the dual bridge. -/
def sClosedSupportTransportedLeftRejectiveOrderIso
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D) :
    σ.sClosure.Closeds ≃o
      TransportedLeftRejectiveAdditiveSubcategory E :=
  (IndecomposableSkeleton.sClosedSupportLeftRejectiveOrderIso
      σ hfinite).trans
    (leftRejectiveImageOrderEmbedding E).orderIso

/-! ## Finite-type projective targets -/

/-- For a finite indecomposable skeleton, literal quotient-closed
subcategories are order-isomorphic to the transported right-rejective
subcategories of the finite-projective Auslander target. -/
def finiteType_quotientClosedProjectiveRightRejectiveOrderIso
    [Finite ι] :
    let E := FiniteTypeGenerator.auslanderEquivalence σ
    IndecomposableSkeleton.QuotientClosedAdditiveSubcategory
        (R := R) ≃o
      TransportedRightRejectiveAdditiveSubcategory E := by
  let E := FiniteTypeGenerator.auslanderEquivalence σ
  exact quotientClosedTransportedRightRejectiveOrderIso σ E

/-- Support-poset form of the finite-type quotient-side bridge. -/
def finiteType_qClosedSupportProjectiveRightRejectiveOrderIso
    [Finite ι] :
    let E := FiniteTypeGenerator.auslanderEquivalence σ
    σ.qClosure.Closeds ≃o
      TransportedRightRejectiveAdditiveSubcategory E := by
  let E := FiniteTypeGenerator.auslanderEquivalence σ
  exact qClosedSupportTransportedRightRejectiveOrderIso σ E

/-- Dual literal order isomorphism for subobject-closed subcategories and
transported left-rejective subcategories of the finite-projective target. -/
def finiteType_subobjectClosedProjectiveLeftRejectiveOrderIso
    [Finite ι]
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X) :
    let E := FiniteTypeGenerator.auslanderEquivalence σ
    IndecomposableSkeleton.SubobjectClosedAdditiveSubcategory
        (R := R) ≃o
      TransportedLeftRejectiveAdditiveSubcategory E := by
  let E := FiniteTypeGenerator.auslanderEquivalence σ
  exact
    subobjectClosedTransportedLeftRejectiveOrderIso σ hfinite E

/-- Support-poset form of the finite-type left-rejective dual. -/
def finiteType_sClosedSupportProjectiveLeftRejectiveOrderIso
    [Finite ι]
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X) :
    let E := FiniteTypeGenerator.auslanderEquivalence σ
    σ.sClosure.Closeds ≃o
      TransportedLeftRejectiveAdditiveSubcategory E := by
  let E := FiniteTypeGenerator.auslanderEquivalence σ
  exact
    sClosedSupportTransportedLeftRejectiveOrderIso σ hfinite E

/-! ## Canonical right-module specialization

For a finite-dimensional algebra `A`, Mathlib's `ModuleCat Aᵐᵒᵖ`
is the category of right `A`-modules.  If
`G = ⨁ᵢ Mᵢ` is the additive generator, the Auslander functor has target
left modules over `(End G)ᵐᵒᵖ`, equivalently right modules over `End G`.
-/

section CanonicalRightModules

universe uK uA

variable (K : Type uK) (A : Type uA)
  [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A]

/-- Paper-facing literal quotient/right-rejective order isomorphism.  Its
target is the poset of right-rejective additive subcategories transported
to finitely generated projective right modules over `End(G)`. -/
def canonicalRightModule_quotientClosedProjectiveRightRejectiveOrderIso
    (hrep : IsRightRepresentationFinite.{uK, uA, w} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite
        (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
      hrep
    let E :=
      canonicalRightModuleAuslanderEquivalence K A hrep
    IndecomposableSkeleton.QuotientClosedAdditiveSubcategory
        (R := Aᵐᵒᵖ) ≃o
      TransportedRightRejectiveAdditiveSubcategory E := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite
      (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
    hrep
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, w} K A
  let E :=
    canonicalRightModuleAuslanderEquivalence K A hrep
  exact quotientClosedTransportedRightRejectiveOrderIso σ E

/-- Paper-facing support-poset form of the quotient/right-rejective
Auslander bridge. -/
def canonicalRightModule_qClosedSupportProjectiveRightRejectiveOrderIso
    (hrep : IsRightRepresentationFinite.{uK, uA, w} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite
        (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
      hrep
    let σ :=
      rightIndecomposableSkeleton.{uK, uA, w} K A
    let E :=
      canonicalRightModuleAuslanderEquivalence K A hrep
    σ.qClosure.Closeds ≃o
      TransportedRightRejectiveAdditiveSubcategory E := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite
      (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
    hrep
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, w} K A
  let E :=
    canonicalRightModuleAuslanderEquivalence K A hrep
  exact qClosedSupportTransportedRightRejectiveOrderIso σ E

/-- Dual paper-facing literal subobject/left-rejective order
isomorphism. -/
def canonicalRightModule_subobjectClosedProjectiveLeftRejectiveOrderIso
    (hrep : IsRightRepresentationFinite.{uK, uA, w} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite
        (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
      hrep
    let E :=
      canonicalRightModuleAuslanderEquivalence K A hrep
    IndecomposableSkeleton.SubobjectClosedAdditiveSubcategory
        (R := Aᵐᵒᵖ) ≃o
      TransportedLeftRejectiveAdditiveSubcategory E := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite
      (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
    hrep
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, w} K A
  let E :=
    canonicalRightModuleAuslanderEquivalence K A hrep
  exact
    subobjectClosedTransportedLeftRejectiveOrderIso σ
      (fun X ↦ isFiniteLength_rightFGModule K A X) E

/-- Support-poset form of the canonical left-rejective dual. -/
def canonicalRightModule_sClosedSupportProjectiveLeftRejectiveOrderIso
    (hrep : IsRightRepresentationFinite.{uK, uA, w} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite
        (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
      hrep
    let σ :=
      rightIndecomposableSkeleton.{uK, uA, w} K A
    let E :=
      canonicalRightModuleAuslanderEquivalence K A hrep
    σ.sClosure.Closeds ≃o
      TransportedLeftRejectiveAdditiveSubcategory E := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite
      (CanonicalIndecomposableIndex.{uA, w} Aᵐᵒᵖ) :=
    hrep
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, w} K A
  let E :=
    canonicalRightModuleAuslanderEquivalence K A hrep
  exact
    sClosedSupportTransportedLeftRejectiveOrderIso σ
      (fun X ↦ isFiniteLength_rightFGModule K A X) E

end CanonicalRightModules

end QuotientSubmoduleEquidistribution.AuslanderEquivalence.RejectiveBridge

