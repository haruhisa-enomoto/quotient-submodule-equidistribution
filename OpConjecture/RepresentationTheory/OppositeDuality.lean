import OpConjecture.RepresentationTheory.ContragredientDuality
import OpConjecture.RepresentationTheory.MoritaConventionBridge

/-!
# Paper-facing opposite duality

For right modules, finite-dimensional vector-space duality exchanges
quotient closure over `A` with submodule closure over `Aᵐᵒᵖ`.  This file
instantiates the abstract aligned-biduality consequences on the canonical
indecomposable skeletons and proves the manuscript's Morita-self-opposite
consequence.
-/

noncomputable section

namespace OpConjecture

universe u

variable (K A : Type u)
  [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- Contragredient duality aligned with the canonical skeletons of right
`A`-modules and right `Aᵐᵒᵖ`-modules. -/
def rightOppositeAlignedBiduality :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
    IndecomposableSkeleton.AlignedBiduality
      (rightIndecomposableSkeleton.{u, u, u} K A)
      (rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  exact
    Contragredient.alignedBiduality K Aᵐᵒᵖ
      (rightIndecomposableSkeleton.{u, u, u} K A)
      (rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ)

/-- Vector-space duality gives the support-level order isomorphism
`LQ(A) ≃ LS(Aᵐᵒᵖ)`. -/
def rightQuotientToOppositeSubmoduleClosedOrderIso :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
    let σ := rightIndecomposableSkeleton.{u, u, u} K A
    let τ := rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
    σ.qClosure.Closeds ≃o τ.sClosure.Closeds := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  let σ := rightIndecomposableSkeleton.{u, u, u} K A
  let τ := rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
  exact
    IndecomposableSkeleton.AlignedBiduality.quotientToSubmoduleClosedOrderIso
      σ τ (rightOppositeAlignedBiduality K A)

/-- Literal additive-subcategory form of opposite duality. -/
def rightQuotientToOppositeSubobjectClosedOrderIso :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
    IndecomposableSkeleton.QuotientClosedAdditiveSubcategory
        (R := Aᵐᵒᵖ) ≃o
      IndecomposableSkeleton.SubobjectClosedAdditiveSubcategory
        (R := (Aᵐᵒᵖ)ᵐᵒᵖ) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  let σ := rightIndecomposableSkeleton.{u, u, u} K A
  let τ := rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
  exact
    IndecomposableSkeleton.AlignedBiduality.quotientToSubobjectClosedAdditiveSubcategoryOrderIso
      σ τ (rightOppositeAlignedBiduality K A)

/-- The literal opposite-duality isomorphism preserves the paper's size. -/
@[simp]
theorem ncard_support_rightQuotientToOppositeSubobjectClosedOrderIso
    (C : IndecomposableSkeleton.QuotientClosedAdditiveSubcategory
      (R := Aᵐᵒᵖ)) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
    let σ := rightIndecomposableSkeleton.{u, u, u} K A
    let τ := rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
    (τ.support
      (((rightQuotientToOppositeSubobjectClosedOrderIso K A) C).1)).ncard =
        (σ.support C.1).ncard := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  let σ := rightIndecomposableSkeleton.{u, u, u} K A
  let τ := rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
  dsimp only
  exact
    IndecomposableSkeleton.AlignedBiduality.ncard_support_quotientToSubobjectClosedAdditiveSubcategoryOrderIso
      σ τ (rightOppositeAlignedBiduality K A) C

/-- Opposite duality preserves and reflects right representation-finiteness. -/
theorem rightRepresentationFinite_op_iff :
    IsRightRepresentationFinite.{u, u, u} K A ↔
      IsRightRepresentationFinite.{u, u, u} K Aᵐᵒᵖ := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  change
    Finite (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) ↔
      Finite (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ)
  exact
    (rightOppositeAlignedBiduality K A).forward.labelEquiv.finite_iff

/-- In representation-finite type, vector-space duality identifies the
quotient polynomial of `A` with the submodule polynomial of `Aᵐᵒᵖ`. -/
theorem rightQuotient_oppositeSubmoduleLevelPolynomial_eq
    (hA : IsRightRepresentationFinite.{u, u, u} K A)
    (hAop : IsRightRepresentationFinite.{u, u, u} K Aᵐᵒᵖ) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
    letI : Finite
        (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
    letI : Finite
        (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
    let σ := rightIndecomposableSkeleton.{u, u, u} K A
    let τ := rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
    σ.qClosure.levelPolynomial = τ.sClosure.levelPolynomial := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
  let σ := rightIndecomposableSkeleton.{u, u, u} K A
  let τ := rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
  exact
    IndecomposableSkeleton.AlignedBiduality.quotientToSubmoduleLevelPolynomial_eq
      σ τ (rightOppositeAlignedBiduality K A)

/-- The manuscript's opposite-duality remark: if `A` is Morita equivalent
to `Aᵐᵒᵖ`, then the strong quotient--submodule conjecture holds for `A`. -/
theorem rightEquidistribution_of_moritaEquivalence_op
    (e : MoritaEquivalence K A Aᵐᵒᵖ)
    (hA : IsRightRepresentationFinite.{u, u, u} K A) :
    RightQuotientSubmoduleEquidistribution K A hA := by
  have hAop : IsRightRepresentationFinite.{u, u, u} K Aᵐᵒᵖ :=
    (MoritaConventionBridge.rightRepresentationFinite_iff
      K A Aᵐᵒᵖ e).mp hA
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
  let σ := rightIndecomposableSkeleton.{u, u, u} K A
  let τ := rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
  change σ.qClosure.levelPolynomial = σ.sClosure.levelPolynomial
  have hdual :=
    rightQuotient_oppositeSubmoduleLevelPolynomial_eq K A hA hAop
  have hmorita :=
    MoritaConventionBridge.rightSubmoduleLevelPolynomial_eq
      K A Aᵐᵒᵖ e hA hAop
  exact hdual.trans hmorita.symm

/-- The same hypothesis also proves the weak conjecture. -/
theorem rightWeakEquidistribution_of_moritaEquivalence_op
    (e : MoritaEquivalence K A Aᵐᵒᵖ)
    (hA : IsRightRepresentationFinite.{u, u, u} K A) :
    RightWeakQuotientSubmoduleEquidistribution K A hA :=
  rightQuotientSubmoduleEquidistribution_implies_weak K A hA
    (rightEquidistribution_of_moritaEquivalence_op K A e hA)

end OpConjecture
