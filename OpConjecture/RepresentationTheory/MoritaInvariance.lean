import OpConjecture.RepresentationTheory.SkeletonAlignment
import OpConjecture.RepresentationTheory.FiniteDimensionalAlgebra
import OpConjecture.RepresentationTheory.MoritaConsequences

/-!
# Paper-facing Morita invariance

This combines the restriction and skeleton-alignment adapters with the
existing closure transport consequences.  Since the project models right
`A`-modules as left `Aᵐᵒᵖ`-modules, the input here is a Mathlib Morita
equivalence between the opposite algebras.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture

universe uK uA uB

variable (K : Type uK) [Field K]
  (A : Type uA) [Ring A] [Algebra K A] [FiniteDimensional K A]
  (B : Type uB) [Ring B] [Algebra K B] [FiniteDimensional K B]

/-- A Morita equivalence of the opposite algebras aligns the canonical
indecomposable right-module skeletons. -/
def rightMoritaAlignedEquivalence
    (e : MoritaEquivalence K Aᵐᵒᵖ Bᵐᵒᵖ) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K B
    IndecomposableSkeleton.AlignedEquivalence
      (rightIndecomposableSkeleton.{uK, uA, max uA uB} K A)
      (rightIndecomposableSkeleton.{uK, uB, max uA uB} K B) := by
  letI : IsArtinianRing Aᵐᵒᵖ :=
    isArtinianRing_op_of_finiteDimensional K A
  letI : IsArtinianRing Bᵐᵒᵖ :=
    isArtinianRing_op_of_finiteDimensional K B
  letI : IsNoetherianRing Aᵐᵒᵖ := inferInstance
  letI : IsNoetherianRing Bᵐᵒᵖ := inferInstance
  exact
    MoritaEquivalence.alignedFgEquivalence e
      (rightIndecomposableSkeleton.{uK, uA, max uA uB} K A)
      (rightIndecomposableSkeleton.{uK, uB, max uA uB} K B)

/-- The literal lattice of quotient-closed additive subcategories of right
modules is Morita invariant. -/
def rightMoritaQuotientClosedOrderIso
    (e : MoritaEquivalence K Aᵐᵒᵖ Bᵐᵒᵖ) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K B
    IndecomposableSkeleton.QuotientClosedAdditiveSubcategory
        (R := Aᵐᵒᵖ) ≃o
      IndecomposableSkeleton.QuotientClosedAdditiveSubcategory
        (R := Bᵐᵒᵖ) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, max uA uB} K A
  let τ :=
    rightIndecomposableSkeleton.{uK, uB, max uA uB} K B
  exact
    IndecomposableSkeleton.AlignedEquivalence.quotientClosedAdditiveSubcategoryOrderIso
      σ τ (rightMoritaAlignedEquivalence K A B e)

/-- The literal lattice of subobject-closed additive subcategories of right
modules is Morita invariant. -/
def rightMoritaSubobjectClosedOrderIso
    (e : MoritaEquivalence K Aᵐᵒᵖ Bᵐᵒᵖ) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K B
    IndecomposableSkeleton.SubobjectClosedAdditiveSubcategory
        (R := Aᵐᵒᵖ) ≃o
      IndecomposableSkeleton.SubobjectClosedAdditiveSubcategory
        (R := Bᵐᵒᵖ) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, max uA uB} K A
  let τ :=
    rightIndecomposableSkeleton.{uK, uB, max uA uB} K B
  exact
    IndecomposableSkeleton.AlignedEquivalence.subobjectClosedAdditiveSubcategoryOrderIso
      σ τ (rightMoritaAlignedEquivalence K A B e)

/-- The quotient-side lattice isomorphism preserves the paper's size,
measured as the number of indecomposable isomorphism classes in the
subcategory. -/
theorem ncard_support_rightMoritaQuotientClosedOrderIso
    (e : MoritaEquivalence K Aᵐᵒᵖ Bᵐᵒᵖ) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K B
    let σ :=
      rightIndecomposableSkeleton.{uK, uA, max uA uB} K A
    let τ :=
      rightIndecomposableSkeleton.{uK, uB, max uA uB} K B
    ∀ C :
        IndecomposableSkeleton.QuotientClosedAdditiveSubcategory
          (R := Aᵐᵒᵖ),
      (τ.support
          (((rightMoritaQuotientClosedOrderIso K A B e) C).1)).ncard =
        (σ.support C.1).ncard := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, max uA uB} K A
  let τ :=
    rightIndecomposableSkeleton.{uK, uB, max uA uB} K B
  dsimp only
  intro C
  exact
    IndecomposableSkeleton.AlignedEquivalence.ncard_support_quotientClosedAdditiveSubcategoryOrderIso
      σ τ (rightMoritaAlignedEquivalence K A B e) C

/-- The subobject-side lattice isomorphism preserves the paper's size. -/
theorem ncard_support_rightMoritaSubobjectClosedOrderIso
    (e : MoritaEquivalence K Aᵐᵒᵖ Bᵐᵒᵖ) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K B
    let σ :=
      rightIndecomposableSkeleton.{uK, uA, max uA uB} K A
    let τ :=
      rightIndecomposableSkeleton.{uK, uB, max uA uB} K B
    ∀ C :
        IndecomposableSkeleton.SubobjectClosedAdditiveSubcategory
          (R := Aᵐᵒᵖ),
      (τ.support
          (((rightMoritaSubobjectClosedOrderIso K A B e) C).1)).ncard =
        (σ.support C.1).ncard := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, max uA uB} K A
  let τ :=
    rightIndecomposableSkeleton.{uK, uB, max uA uB} K B
  dsimp only
  intro C
  exact
    IndecomposableSkeleton.AlignedEquivalence.ncard_support_subobjectClosedAdditiveSubcategoryOrderIso
      σ τ (rightMoritaAlignedEquivalence K A B e) C

/-- Morita equivalence preserves and reflects representation-finiteness,
with both canonical skeletons placed in one common module universe. -/
theorem rightMorita_representationFinite_iff
    (e : MoritaEquivalence K Aᵐᵒᵖ Bᵐᵒᵖ) :
    IsRightRepresentationFinite.{uK, uA, max uA uB} K A ↔
      IsRightRepresentationFinite.{uK, uB, max uA uB} K B := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  change
    Finite
        (CanonicalIndecomposableIndex.{uA, max uA uB} Aᵐᵒᵖ) ↔
      Finite
        (CanonicalIndecomposableIndex.{uB, max uA uB} Bᵐᵒᵖ)
  exact
    (rightMoritaAlignedEquivalence K A B e).labelEquiv.finite_iff

/-- In representation-finite type, Morita equivalence preserves the
quotient level-generating polynomial. -/
theorem rightMorita_quotientLevelPolynomial_eq
    (e : MoritaEquivalence K Aᵐᵒᵖ Bᵐᵒᵖ)
    (hA : IsRightRepresentationFinite.{uK, uA, max uA uB} K A)
    (hB : IsRightRepresentationFinite.{uK, uB, max uA uB} K B) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K B
    letI : Finite
        (CanonicalIndecomposableIndex.{uA, max uA uB} Aᵐᵒᵖ) := hA
    letI : Finite
        (CanonicalIndecomposableIndex.{uB, max uA uB} Bᵐᵒᵖ) := hB
    let σ :=
      rightIndecomposableSkeleton.{uK, uA, max uA uB} K A
    let τ :=
      rightIndecomposableSkeleton.{uK, uB, max uA uB} K B
    σ.qClosure.levelPolynomial = τ.qClosure.levelPolynomial := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  letI : Finite
      (CanonicalIndecomposableIndex.{uA, max uA uB} Aᵐᵒᵖ) := hA
  letI : Finite
      (CanonicalIndecomposableIndex.{uB, max uA uB} Bᵐᵒᵖ) := hB
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, max uA uB} K A
  let τ :=
    rightIndecomposableSkeleton.{uK, uB, max uA uB} K B
  exact
    IndecomposableSkeleton.AlignedEquivalence.quotientLevelPolynomial_eq
      σ τ (rightMoritaAlignedEquivalence K A B e)

/-- In representation-finite type, Morita equivalence preserves the
submodule level-generating polynomial. -/
theorem rightMorita_submoduleLevelPolynomial_eq
    (e : MoritaEquivalence K Aᵐᵒᵖ Bᵐᵒᵖ)
    (hA : IsRightRepresentationFinite.{uK, uA, max uA uB} K A)
    (hB : IsRightRepresentationFinite.{uK, uB, max uA uB} K B) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K B
    letI : Finite
        (CanonicalIndecomposableIndex.{uA, max uA uB} Aᵐᵒᵖ) := hA
    letI : Finite
        (CanonicalIndecomposableIndex.{uB, max uA uB} Bᵐᵒᵖ) := hB
    let σ :=
      rightIndecomposableSkeleton.{uK, uA, max uA uB} K A
    let τ :=
      rightIndecomposableSkeleton.{uK, uB, max uA uB} K B
    σ.sClosure.levelPolynomial = τ.sClosure.levelPolynomial := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  letI : Finite
      (CanonicalIndecomposableIndex.{uA, max uA uB} Aᵐᵒᵖ) := hA
  letI : Finite
      (CanonicalIndecomposableIndex.{uB, max uA uB} Bᵐᵒᵖ) := hB
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, max uA uB} K A
  let τ :=
    rightIndecomposableSkeleton.{uK, uB, max uA uB} K B
  exact
    IndecomposableSkeleton.AlignedEquivalence.submoduleLevelPolynomial_eq
      σ τ (rightMoritaAlignedEquivalence K A B e)

/-- The strong quotient--submodule conjecture is invariant under Morita
equivalence. -/
theorem rightMorita_equidistribution_iff
    (e : MoritaEquivalence K Aᵐᵒᵖ Bᵐᵒᵖ)
    (hA : IsRightRepresentationFinite.{uK, uA, max uA uB} K A)
    (hB : IsRightRepresentationFinite.{uK, uB, max uA uB} K B) :
    RightQuotientSubmoduleEquidistribution K A hA ↔
      RightQuotientSubmoduleEquidistribution K B hB := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  letI : Finite
      (CanonicalIndecomposableIndex.{uA, max uA uB} Aᵐᵒᵖ) := hA
  letI : Finite
      (CanonicalIndecomposableIndex.{uB, max uA uB} Bᵐᵒᵖ) := hB
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, max uA uB} K A
  let τ :=
    rightIndecomposableSkeleton.{uK, uB, max uA uB} K B
  change
    σ.qClosure.levelPolynomial = σ.sClosure.levelPolynomial ↔
      τ.qClosure.levelPolynomial = τ.sClosure.levelPolynomial
  have hq :=
    rightMorita_quotientLevelPolynomial_eq K A B e hA hB
  have hs :=
    rightMorita_submoduleLevelPolynomial_eq K A B e hA hB
  constructor
  · intro h
    exact hq.symm.trans (h.trans hs)
  · intro h
    exact hq.trans (h.trans hs.symm)

/-- The weak counting conjecture is invariant under Morita equivalence. -/
theorem rightMorita_weakEquidistribution_iff
    (e : MoritaEquivalence K Aᵐᵒᵖ Bᵐᵒᵖ)
    (hA : IsRightRepresentationFinite.{uK, uA, max uA uB} K A)
    (hB : IsRightRepresentationFinite.{uK, uB, max uA uB} K B) :
    RightWeakQuotientSubmoduleEquidistribution K A hA ↔
      RightWeakQuotientSubmoduleEquidistribution K B hB := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  letI : Finite
      (CanonicalIndecomposableIndex.{uA, max uA uB} Aᵐᵒᵖ) := hA
  letI : Finite
      (CanonicalIndecomposableIndex.{uB, max uA uB} Bᵐᵒᵖ) := hB
  let σ :=
    rightIndecomposableSkeleton.{uK, uA, max uA uB} K A
  let τ :=
    rightIndecomposableSkeleton.{uK, uB, max uA uB} K B
  change
    Nat.card σ.qClosure.Closeds =
        Nat.card σ.sClosure.Closeds ↔
      Nat.card τ.qClosure.Closeds =
        Nat.card τ.sClosure.Closeds
  have hq :
      Nat.card σ.qClosure.Closeds =
        Nat.card τ.qClosure.Closeds :=
    Nat.card_congr
      (IndecomposableSkeleton.AlignedEquivalence.quotientClosedOrderIso
        σ τ (rightMoritaAlignedEquivalence K A B e)).toEquiv
  have hs :
      Nat.card σ.sClosure.Closeds =
        Nat.card τ.sClosure.Closeds :=
    Nat.card_congr
      (IndecomposableSkeleton.AlignedEquivalence.submoduleClosedOrderIso
        σ τ (rightMoritaAlignedEquivalence K A B e)).toEquiv
  constructor
  · intro h
    exact hq.symm.trans (h.trans hs)
  · intro h
    exact hq.trans (h.trans hs.symm)

end OpConjecture
