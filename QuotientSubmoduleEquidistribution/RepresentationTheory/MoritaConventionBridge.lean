import QuotientSubmoduleEquidistribution.RepresentationTheory.ContragredientDuality
import QuotientSubmoduleEquidistribution.RepresentationTheory.MoritaInvariance

/-!
# The left-Morita/right-module convention bridge

Mathlib's `MoritaEquivalence K A B` is phrased using categories of left
modules.  The manuscript uses finitely generated right modules.  Over
finite-dimensional algebras, contragredient duality conjugates the
restricted left-module equivalence to the required right-module
equivalence.

This file is scratch-only evidence.  It deliberately uses one universe,
matching the current concrete duality assembly.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.MoritaConventionBridge

universe u

variable (K A B : Type u)
  [Field K]
  [Ring A] [Algebra K A] [FiniteDimensional K A]
  [Ring B] [Algebra K B] [FiniteDimensional K B]

/-- Conjugate Mathlib's restricted left-module Morita equivalence by
finite-dimensional contragredient duality. -/
def rightFgEquivalence (e : MoritaEquivalence K A B) :
    FGModuleCat.{u} Aᵐᵒᵖ ≌ FGModuleCat.{u} Bᵐᵒᵖ :=
  (Contragredient.dualityEquivalence K A).symm |>.trans <|
    e.finiteDimensionalFgEquivalence.op |>.trans <|
      Contragredient.dualityEquivalence K B

/-- Therefore an ordinary Mathlib Morita equivalence aligns the canonical
indecomposable skeletons of finitely generated right modules. -/
def rightAlignedEquivalence
    (e : MoritaEquivalence K A B) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K B
    IndecomposableSkeleton.AlignedEquivalence
      (rightIndecomposableSkeleton.{u, u, u} K A)
      (rightIndecomposableSkeleton.{u, u, u} K B) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  exact
    IndecomposableSkeleton.Equivalence.alignedEquivalence
      (rightIndecomposableSkeleton.{u, u, u} K A)
      (rightIndecomposableSkeleton.{u, u, u} K B)
      (rightFgEquivalence K A B e)

/-- The quotient-closed additive-subcategory lattice of right modules is
invariant under Mathlib's ordinary (left-module) Morita equivalence. -/
def rightQuotientClosedOrderIso
    (e : MoritaEquivalence K A B) :
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
  let σ := rightIndecomposableSkeleton.{u, u, u} K A
  let τ := rightIndecomposableSkeleton.{u, u, u} K B
  exact
    IndecomposableSkeleton.AlignedEquivalence.quotientClosedAdditiveSubcategoryOrderIso
      σ τ (rightAlignedEquivalence K A B e)

/-- The subobject-closed additive-subcategory lattice has the same
invariance. -/
def rightSubobjectClosedOrderIso
    (e : MoritaEquivalence K A B) :
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
  let σ := rightIndecomposableSkeleton.{u, u, u} K A
  let τ := rightIndecomposableSkeleton.{u, u, u} K B
  exact
    IndecomposableSkeleton.AlignedEquivalence.subobjectClosedAdditiveSubcategoryOrderIso
      σ τ (rightAlignedEquivalence K A B e)

/-- The quotient-side lattice isomorphism preserves the paper's size,
namely the number of indecomposable isomorphism classes in a subcategory. -/
@[simp]
theorem ncard_support_rightQuotientClosedOrderIso
    (e : MoritaEquivalence K A B)
    (C : IndecomposableSkeleton.QuotientClosedAdditiveSubcategory
      (R := Aᵐᵒᵖ)) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K B
    let σ := rightIndecomposableSkeleton.{u, u, u} K A
    let τ := rightIndecomposableSkeleton.{u, u, u} K B
    (τ.support (((rightQuotientClosedOrderIso K A B e) C).1)).ncard =
      (σ.support C.1).ncard := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  let σ := rightIndecomposableSkeleton.{u, u, u} K A
  let τ := rightIndecomposableSkeleton.{u, u, u} K B
  dsimp only
  exact
    IndecomposableSkeleton.AlignedEquivalence.ncard_support_quotientClosedAdditiveSubcategoryOrderIso
      σ τ (rightAlignedEquivalence K A B e) C

/-- The subobject-side lattice isomorphism preserves the paper's size. -/
@[simp]
theorem ncard_support_rightSubobjectClosedOrderIso
    (e : MoritaEquivalence K A B)
    (C : IndecomposableSkeleton.SubobjectClosedAdditiveSubcategory
      (R := Aᵐᵒᵖ)) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K B
    let σ := rightIndecomposableSkeleton.{u, u, u} K A
    let τ := rightIndecomposableSkeleton.{u, u, u} K B
    (τ.support (((rightSubobjectClosedOrderIso K A B e) C).1)).ncard =
      (σ.support C.1).ncard := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  let σ := rightIndecomposableSkeleton.{u, u, u} K A
  let τ := rightIndecomposableSkeleton.{u, u, u} K B
  dsimp only
  exact
    IndecomposableSkeleton.AlignedEquivalence.ncard_support_subobjectClosedAdditiveSubcategoryOrderIso
      σ τ (rightAlignedEquivalence K A B e) C

/-- Ordinary Morita equivalence preserves and reflects right
representation-finiteness. -/
theorem rightRepresentationFinite_iff
    (e : MoritaEquivalence K A B) :
    IsRightRepresentationFinite.{u, u, u} K A ↔
      IsRightRepresentationFinite.{u, u, u} K B := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  change
    Finite (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) ↔
      Finite (CanonicalIndecomposableIndex.{u, u} Bᵐᵒᵖ)
  exact (rightAlignedEquivalence K A B e).labelEquiv.finite_iff

/-- The quotient level-generating polynomial is invariant. -/
theorem rightQuotientLevelPolynomial_eq
    (e : MoritaEquivalence K A B)
    (hA : IsRightRepresentationFinite.{u, u, u} K A)
    (hB : IsRightRepresentationFinite.{u, u, u} K B) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K B
    letI : Finite
        (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
    letI : Finite
        (CanonicalIndecomposableIndex.{u, u} Bᵐᵒᵖ) := hB
    let σ := rightIndecomposableSkeleton.{u, u, u} K A
    let τ := rightIndecomposableSkeleton.{u, u, u} K B
    σ.qClosure.levelPolynomial = τ.qClosure.levelPolynomial := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} Bᵐᵒᵖ) := hB
  let σ := rightIndecomposableSkeleton.{u, u, u} K A
  let τ := rightIndecomposableSkeleton.{u, u, u} K B
  exact
    IndecomposableSkeleton.AlignedEquivalence.quotientLevelPolynomial_eq
      σ τ (rightAlignedEquivalence K A B e)

/-- The submodule level-generating polynomial is invariant. -/
theorem rightSubmoduleLevelPolynomial_eq
    (e : MoritaEquivalence K A B)
    (hA : IsRightRepresentationFinite.{u, u, u} K A)
    (hB : IsRightRepresentationFinite.{u, u, u} K B) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K B
    letI : Finite
        (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
    letI : Finite
        (CanonicalIndecomposableIndex.{u, u} Bᵐᵒᵖ) := hB
    let σ := rightIndecomposableSkeleton.{u, u, u} K A
    let τ := rightIndecomposableSkeleton.{u, u, u} K B
    σ.sClosure.levelPolynomial = τ.sClosure.levelPolynomial := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} Bᵐᵒᵖ) := hB
  let σ := rightIndecomposableSkeleton.{u, u, u} K A
  let τ := rightIndecomposableSkeleton.{u, u, u} K B
  exact
    IndecomposableSkeleton.AlignedEquivalence.submoduleLevelPolynomial_eq
      σ τ (rightAlignedEquivalence K A B e)

/-- The strong quotient--submodule conjecture is invariant under
Mathlib's ordinary Morita equivalence. -/
theorem rightEquidistribution_iff
    (e : MoritaEquivalence K A B)
    (hA : IsRightRepresentationFinite.{u, u, u} K A)
    (hB : IsRightRepresentationFinite.{u, u, u} K B) :
    RightQuotientSubmoduleEquidistribution K A hA ↔
      RightQuotientSubmoduleEquidistribution K B hB := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} Bᵐᵒᵖ) := hB
  let σ := rightIndecomposableSkeleton.{u, u, u} K A
  let τ := rightIndecomposableSkeleton.{u, u, u} K B
  change
    σ.qClosure.levelPolynomial = σ.sClosure.levelPolynomial ↔
      τ.qClosure.levelPolynomial = τ.sClosure.levelPolynomial
  have hq := rightQuotientLevelPolynomial_eq K A B e hA hB
  have hs := rightSubmoduleLevelPolynomial_eq K A B e hA hB
  constructor
  · intro h
    exact hq.symm.trans (h.trans hs)
  · intro h
    exact hq.trans (h.trans hs.symm)

/-- The weak counting conjecture is invariant under Mathlib's ordinary
Morita equivalence. -/
theorem rightWeakEquidistribution_iff
    (e : MoritaEquivalence K A B)
    (hA : IsRightRepresentationFinite.{u, u, u} K A)
    (hB : IsRightRepresentationFinite.{u, u, u} K B) :
    RightWeakQuotientSubmoduleEquidistribution K A hA ↔
      RightWeakQuotientSubmoduleEquidistribution K B hB := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K B
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} Bᵐᵒᵖ) := hB
  let σ := rightIndecomposableSkeleton.{u, u, u} K A
  let τ := rightIndecomposableSkeleton.{u, u, u} K B
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
        σ τ (rightAlignedEquivalence K A B e)).toEquiv
  have hs :
      Nat.card σ.sClosure.Closeds =
        Nat.card τ.sClosure.Closeds :=
    Nat.card_congr
      (IndecomposableSkeleton.AlignedEquivalence.submoduleClosedOrderIso
        σ τ (rightAlignedEquivalence K A B e)).toEquiv
  constructor
  · intro h
    exact hq.symm.trans (h.trans hs)
  · intro h
    exact hq.trans (h.trans hs.symm)

end QuotientSubmoduleEquidistribution.MoritaConventionBridge
