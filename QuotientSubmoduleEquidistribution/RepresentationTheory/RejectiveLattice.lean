import QuotientSubmoduleEquidistribution.RepresentationTheory.LiteralTraceRejective
import QuotientSubmoduleEquidistribution.RepresentationTheory.ConvexStructure
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalAlgebra

/-!
# The module-side Auslander--rejective order isomorphism

This file isolates exactly what follows from the production
trace--rejective equivalences before constructing the Auslander functor
`Hom_A(G, -) : mod A ≌ proj (End_A(G))`.
-/

noncomputable section

open Set
open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

/-- Literal additive subcategories equipped propositionally with right
rejectivity in the ambient finitely generated module category. -/
abbrev RightRejectiveAdditiveSubcategory :=
  {C : AdditiveRepleteSummandSubcategory.{u, w} (R := R) //
    IsRightRejective C}

/-- Literal additive subcategories equipped propositionally with left
rejectivity in the ambient finitely generated module category. -/
abbrev LeftRejectiveAdditiveSubcategory :=
  {C : AdditiveRepleteSummandSubcategory.{u, w} (R := R) //
    IsLeftRejective C}

/-- Pointwise quotient closure versus right rejectivity upgrades directly
to an order isomorphism of the two literal-subcategory posets. -/
def quotientClosedRightRejectiveOrderIso :
    QuotientClosedAdditiveSubcategory.{u, w} (R := R) ≃o
      RightRejectiveAdditiveSubcategory.{u, w} (R := R) where
  toFun C :=
    ⟨C.1,
      (isClosedUnderQuotients_iff_rightRejective σ C.1).1 C.2⟩
  invFun C :=
    ⟨C.1,
      (isClosedUnderQuotients_iff_rightRejective σ C.1).2 C.2⟩
  left_inv C := by
    apply Subtype.ext
    rfl
  right_inv C := by
    apply Subtype.ext
    rfl
  map_rel_iff' := by
    intro C D
    rfl

/-- The left-rejective dual order isomorphism. -/
def subobjectClosedLeftRejectiveOrderIso
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X) :
    SubobjectClosedAdditiveSubcategory.{u, w} (R := R) ≃o
      LeftRejectiveAdditiveSubcategory.{u, w} (R := R) where
  toFun C :=
    ⟨C.1,
      (isClosedUnderSubobjects_iff_leftRejective
        σ hfinite C.1).1 C.2⟩
  invFun C :=
    ⟨C.1,
      (isClosedUnderSubobjects_iff_leftRejective
        σ hfinite C.1).2 C.2⟩
  left_inv C := by
    apply Subtype.ext
    rfl
  right_inv C := by
    apply Subtype.ext
    rfl
  map_rel_iff' := by
    intro C D
    rfl

/-- Exact support-poset form of the quotient half of
`cor:auslander-rejective`, still on `mod R`. -/
def qClosedSupportRightRejectiveOrderIso :
    σ.qClosure.Closeds ≃o
      RightRejectiveAdditiveSubcategory.{u, w} (R := R) :=
  σ.quotientClosedSupportOrderIso.symm.trans
    (quotientClosedRightRejectiveOrderIso σ)

/-- Exact support-poset form of the submodule half of
`cor:auslander-rejective`, still on `mod R`. -/
def sClosedSupportLeftRejectiveOrderIso
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X) :
    σ.sClosure.Closeds ≃o
      LeftRejectiveAdditiveSubcategory.{u, w} (R := R) :=
  σ.subobjectClosedSupportOrderIso.symm.trans
    (subobjectClosedLeftRejectiveOrderIso σ hfinite)

@[simp]
theorem qClosedSupportRightRejectiveOrderIso_val
    (C : σ.qClosure.Closeds) :
    (qClosedSupportRightRejectiveOrderIso σ C).1 =
      σ.generated (C : Set ι) :=
  rfl

@[simp]
theorem sClosedSupportLeftRejectiveOrderIso_val
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (C : σ.sClosure.Closeds) :
    (sClosedSupportLeftRejectiveOrderIso σ hfinite C).1 =
      σ.generated (C : Set ι) :=
  rfl

/-- The finite convex deletion theorem transports to ambient right
rejectivity: every nonzero right-rejective literal subcategory has a
one-indecomposable deletion which is again right rejective in `mod R`. -/
theorem rightRejective_exists_deletion
    [Finite ι]
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (C : RightRejectiveAdditiveSubcategory.{u, w} (R := R))
    (hne : (σ.support C.1).Nonempty) :
    ∃ x ∈ σ.support C.1,
      σ.IsRelativeSplitProjective (σ.support C.1) x ∧
        IsRightRejective
          (σ.generated (σ.support C.1 \ {x})) := by
  have hrr :
      IsRightRejective (σ.generated (σ.support C.1)) := by
    simpa only [generated_support σ C.1] using C.2
  have hclosed : σ.qClosure.IsClosed (σ.support C.1) :=
    (qClosed_iff_rightRejective σ (σ.support C.1)).2 hrr
  obtain ⟨x, hx, hxrel, hxclosed⟩ :=
    qClosed_exists_relativeSplitProjective_deletion
      (K := K) σ hclosed hne
  exact
    ⟨x, hx, hxrel,
      (qClosed_iff_rightRejective
        σ (σ.support C.1 \ {x})).1 hxclosed⟩

/-- Dual ambient left-rejective deletion statement. -/
theorem leftRejective_exists_deletion
    [Finite ι]
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (C : LeftRejectiveAdditiveSubcategory.{u, w} (R := R))
    (hne : (σ.support C.1).Nonempty) :
    ∃ x ∈ σ.support C.1,
      σ.IsRelativeSplitInjective (σ.support C.1) x ∧
        IsLeftRejective
          (σ.generated (σ.support C.1 \ {x})) := by
  have hlr :
      IsLeftRejective (σ.generated (σ.support C.1)) := by
    simpa only [generated_support σ C.1] using C.2
  have hclosed : σ.sClosure.IsClosed (σ.support C.1) :=
    (sClosed_iff_leftRejective
      σ hfinite (σ.support C.1)).2 hlr
  obtain ⟨x, hx, hxrel, hxclosed⟩ :=
    sClosed_exists_relativeSplitInjective_deletion
      (K := K) σ hclosed hne
  exact
    ⟨x, hx, hxrel,
      (sClosed_iff_leftRejective
        σ hfinite (σ.support C.1 \ {x})).1 hxclosed⟩

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton

namespace QuotientSubmoduleEquidistribution

universe uK uA w

/-- Canonical right-module specialization of the quotient-side order
isomorphism for a finite-dimensional algebra.  Representation-finiteness
is needed only to make the underlying support type finite, not for this
order equivalence itself. -/
noncomputable def rightModule_qClosedSupportRightRejectiveOrderIso
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
    σ.qClosure.Closeds ≃o
      IndecomposableSkeleton.RightRejectiveAdditiveSubcategory
        (R := Aᵐᵒᵖ) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
  exact
    IndecomposableSkeleton.qClosedSupportRightRejectiveOrderIso σ

/-- Canonical right-module specialization of the left-rejective dual. -/
noncomputable def rightModule_sClosedSupportLeftRejectiveOrderIso
    (K : Type uK) (A : Type uA)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
    σ.sClosure.Closeds ≃o
      IndecomposableSkeleton.LeftRejectiveAdditiveSubcategory
        (R := Aᵐᵒᵖ) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  let σ := rightIndecomposableSkeleton.{uK, uA, w} K A
  exact
    IndecomposableSkeleton.sClosedSupportLeftRejectiveOrderIso
      σ (fun X ↦ isFiniteLength_rightFGModule K A X)

end QuotientSubmoduleEquidistribution


