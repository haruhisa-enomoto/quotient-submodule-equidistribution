import QuotientSubmoduleEquidistribution.ConvexGeometry.Relabeling
import QuotientSubmoduleEquidistribution.RepresentationTheory.AdditiveSubcategory
import QuotientSubmoduleEquidistribution.RepresentationTheory.EquivalenceTransport

/-!
# Closure and polynomial consequences of an aligned equivalence
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence

universe uR uS vR vS wR wS

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {S : Type uS} [Ring S] [IsNoetherianRing S]
  {ι : Type vR} {κ : Type vS}
  (σ : IndecomposableSkeleton.{uR, vR, wR} R ι)
  (τ : IndecomposableSkeleton.{uS, vS, wS} S κ)
  (E : AlignedEquivalence σ τ)

/-- The quotient closures are the same closure system up to relabeling. -/
def qClosureRelabeling :
    SetClosure.RelabelingEquiv σ.qClosure τ.qClosure where
  equiv := E.labelEquiv
  map_closure := image_qClosure σ τ E

/-- The submodule closures are the same closure system up to relabeling. -/
def sClosureRelabeling :
    SetClosure.RelabelingEquiv σ.sClosure τ.sClosure where
  equiv := E.labelEquiv
  map_closure := image_sClosure σ τ E

/-- The quotient-closed support lattices are order-isomorphic. -/
def quotientClosedOrderIso :
    σ.qClosure.Closeds ≃o τ.qClosure.Closeds :=
  (qClosureRelabeling σ τ E).closedsOrderIso

/-- The submodule-closed support lattices are order-isomorphic. -/
def submoduleClosedOrderIso :
    σ.sClosure.Closeds ≃o τ.sClosure.Closeds :=
  (sClosureRelabeling σ τ E).closedsOrderIso

/-- The paper-facing order isomorphism between literal quotient-closed
additive subcategories. -/
def quotientClosedAdditiveSubcategoryOrderIso :
    QuotientClosedAdditiveSubcategory.{uR, wR} (R := R) ≃o
      QuotientClosedAdditiveSubcategory.{uS, wS} (R := S) :=
  σ.quotientClosedSupportOrderIso.trans <|
    (quotientClosedOrderIso σ τ E).trans
      τ.quotientClosedSupportOrderIso.symm

/-- The paper-facing order isomorphism between literal subobject-closed
additive subcategories. -/
def subobjectClosedAdditiveSubcategoryOrderIso :
    SubobjectClosedAdditiveSubcategory.{uR, wR} (R := R) ≃o
      SubobjectClosedAdditiveSubcategory.{uS, wS} (R := S) :=
  σ.subobjectClosedSupportOrderIso.trans <|
    (submoduleClosedOrderIso σ τ E).trans
      τ.subobjectClosedSupportOrderIso.symm

/-- The literal quotient-side order isomorphism preserves the number of
indecomposable isomorphism classes in every subcategory. -/
@[simp]
theorem ncard_support_quotientClosedAdditiveSubcategoryOrderIso
    (C : QuotientClosedAdditiveSubcategory.{uR, wR} (R := R)) :
    (τ.support
        ((quotientClosedAdditiveSubcategoryOrderIso σ τ E C).1)).ncard =
      (σ.support C.1).ncard := by
  simp only [quotientClosedAdditiveSubcategoryOrderIso,
    OrderIso.trans_apply]
  change
    (((τ.quotientClosedSupportOrderIso
        (τ.quotientClosedSupportOrderIso.symm
          ((quotientClosedOrderIso σ τ E)
            (σ.quotientClosedSupportOrderIso C)))) :
      τ.qClosure.Closeds) : Set κ).ncard =
      (σ.support C.1).ncard
  rw [τ.quotientClosedSupportOrderIso.apply_symm_apply]
  exact
    SetClosure.RelabelingEquiv.ncard_closedsOrderIso_apply
      (qClosureRelabeling σ τ E)
      (σ.quotientClosedSupportOrderIso C)

/-- The literal subobject-side order isomorphism preserves the number of
indecomposable isomorphism classes in every subcategory. -/
@[simp]
theorem ncard_support_subobjectClosedAdditiveSubcategoryOrderIso
    (C : SubobjectClosedAdditiveSubcategory.{uR, wR} (R := R)) :
    (τ.support
        ((subobjectClosedAdditiveSubcategoryOrderIso σ τ E C).1)).ncard =
      (σ.support C.1).ncard := by
  simp only [subobjectClosedAdditiveSubcategoryOrderIso,
    OrderIso.trans_apply]
  change
    (((τ.subobjectClosedSupportOrderIso
        (τ.subobjectClosedSupportOrderIso.symm
          ((submoduleClosedOrderIso σ τ E)
            (σ.subobjectClosedSupportOrderIso C)))) :
      τ.sClosure.Closeds) : Set κ).ncard =
      (σ.support C.1).ncard
  rw [τ.subobjectClosedSupportOrderIso.apply_symm_apply]
  exact
    SetClosure.RelabelingEquiv.ncard_closedsOrderIso_apply
      (sClosureRelabeling σ τ E)
      (σ.subobjectClosedSupportOrderIso C)

/-- In finite type, a Morita-style equivalence preserves the quotient
level-generating polynomial. -/
theorem quotientLevelPolynomial_eq
    (E : AlignedEquivalence σ τ) [Finite ι] [Finite κ] :
    σ.qClosure.levelPolynomial = τ.qClosure.levelPolynomial :=
  SetClosure.RelabelingEquiv.levelPolynomial_eq
    (qClosureRelabeling σ τ E)

/-- In finite type, a Morita-style equivalence preserves the submodule
level-generating polynomial. -/
theorem submoduleLevelPolynomial_eq
    (E : AlignedEquivalence σ τ) [Finite ι] [Finite κ] :
    σ.sClosure.levelPolynomial = τ.sClosure.levelPolynomial :=
  SetClosure.RelabelingEquiv.levelPolynomial_eq
    (sClosureRelabeling σ τ E)

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence
