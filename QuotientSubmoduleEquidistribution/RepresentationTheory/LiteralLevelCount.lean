import QuotientSubmoduleEquidistribution.RepresentationTheory.CofiniteLevel
import QuotientSubmoduleEquidistribution.RepresentationTheory.LiteralLattice

/-!
# Literal additive-subcategory level counts

The support order isomorphisms transport the chosen-skeleton level counts
to literal quotient-closed and subobject-closed additive subcategories.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe uK uR v w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{uR, v, w} R ι)

/-- Number of literal quotient-closed additive subcategories whose
indecomposable support has cardinality `n`. -/
def literalQuotientLevelCount (n : ℕ) : ℕ :=
  {C : QuotientClosedAdditiveSubcategory.{uR, w} (R := R) |
    (σ.support C.1).ncard = n}.ncard

/-- Number of literal subobject-closed additive subcategories whose
indecomposable support has cardinality `n`. -/
def literalSubobjectLevelCount (n : ℕ) : ℕ :=
  {C : SubobjectClosedAdditiveSubcategory.{uR, w} (R := R) |
    (σ.support C.1).ncard = n}.ncard

/-- The support order isomorphism restricted to one quotient-closed
cardinality level. -/
def literalQuotientLevelEquiv (n : ℕ) :
    {C : QuotientClosedAdditiveSubcategory.{uR, w} (R := R) //
      (σ.support C.1).ncard = n} ≃
      {S : σ.qClosure.Closeds //
        (S : Set ι).ncard = n} where
  toFun C :=
    ⟨σ.quotientClosedSupportOrderIso C.1, C.2⟩
  invFun S := by
    let C :=
      σ.quotientClosedSupportOrderIso.symm S.1
    refine ⟨C, ?_⟩
    have hsupport :
        σ.support C.1 = (S.1 : Set ι) := by
      change
        ((σ.quotientClosedSupportOrderIso
          (σ.quotientClosedSupportOrderIso.symm S.1) :
            σ.qClosure.Closeds) : Set ι) =
          (S.1 : Set ι)
      rw [σ.quotientClosedSupportOrderIso.apply_symm_apply]
    rw [hsupport]
    exact S.2
  left_inv C := by
    apply Subtype.ext
    exact
      σ.quotientClosedSupportOrderIso.symm_apply_apply C.1
  right_inv S := by
    apply Subtype.ext
    exact
      σ.quotientClosedSupportOrderIso.apply_symm_apply S.1

/-- The support order isomorphism restricted to one subobject-closed
cardinality level. -/
def literalSubobjectLevelEquiv (n : ℕ) :
    {C : SubobjectClosedAdditiveSubcategory.{uR, w} (R := R) //
      (σ.support C.1).ncard = n} ≃
      {S : σ.sClosure.Closeds //
        (S : Set ι).ncard = n} where
  toFun C :=
    ⟨σ.subobjectClosedSupportOrderIso C.1, C.2⟩
  invFun S := by
    let C :=
      σ.subobjectClosedSupportOrderIso.symm S.1
    refine ⟨C, ?_⟩
    have hsupport :
        σ.support C.1 = (S.1 : Set ι) := by
      change
        ((σ.subobjectClosedSupportOrderIso
          (σ.subobjectClosedSupportOrderIso.symm S.1) :
            σ.sClosure.Closeds) : Set ι) =
          (S.1 : Set ι)
      rw [σ.subobjectClosedSupportOrderIso.apply_symm_apply]
    rw [hsupport]
    exact S.2
  left_inv C := by
    apply Subtype.ext
    exact
      σ.subobjectClosedSupportOrderIso.symm_apply_apply C.1
  right_inv S := by
    apply Subtype.ext
    exact
      σ.subobjectClosedSupportOrderIso.apply_symm_apply S.1

omit [DecidableEq ι] in
/-- Literal quotient-closed support levels have the same count as the
chosen-skeleton closure levels. -/
theorem literalQuotientLevelCount_eq_levelCount (n : ℕ) :
    σ.literalQuotientLevelCount n =
      σ.qClosure.levelCount n := by
  unfold literalQuotientLevelCount SetClosure.levelCount
  calc
    {C : QuotientClosedAdditiveSubcategory.{uR, w} (R := R) |
        (σ.support C.1).ncard = n}.ncard =
        Nat.card
          {C : QuotientClosedAdditiveSubcategory.{uR, w} (R := R) //
            (σ.support C.1).ncard = n} :=
      (Nat.card_coe_set_eq _).symm
    _ = Nat.card
          {S : σ.qClosure.Closeds //
            (S : Set ι).ncard = n} :=
      Nat.card_congr (literalQuotientLevelEquiv σ n)
    _ = {S : σ.qClosure.Closeds |
          (S : Set ι).ncard = n}.ncard :=
      Nat.card_coe_set_eq _

omit [DecidableEq ι] in
/-- Literal subobject-closed support levels have the same count as the
chosen-skeleton closure levels. -/
theorem literalSubobjectLevelCount_eq_levelCount (n : ℕ) :
    σ.literalSubobjectLevelCount n =
      σ.sClosure.levelCount n := by
  unfold literalSubobjectLevelCount SetClosure.levelCount
  calc
    {C : SubobjectClosedAdditiveSubcategory.{uR, w} (R := R) |
        (σ.support C.1).ncard = n}.ncard =
        Nat.card
          {C : SubobjectClosedAdditiveSubcategory.{uR, w} (R := R) //
            (σ.support C.1).ncard = n} :=
      (Nat.card_coe_set_eq _).symm
    _ = Nat.card
          {S : σ.sClosure.Closeds //
            (S : Set ι).ncard = n} :=
      Nat.card_congr (literalSubobjectLevelEquiv σ n)
    _ = {S : σ.sClosure.Closeds |
          (S : Set ι).ncard = n}.ncard :=
      Nat.card_coe_set_eq _

/-- The quotient cofinite-two count is the literal `(N - 2)` support
level count. -/
theorem qCofiniteTwoCount_eq_literalQuotientLevelCount_card_sub_two
    (hcard : 2 ≤ Nat.card ι) :
    σ.qClosure.cofiniteTwoCount =
      σ.literalQuotientLevelCount (Nat.card ι - 2) := by
  rw [qCofiniteTwoCount_eq_levelCount_card_sub_two σ hcard,
    literalQuotientLevelCount_eq_levelCount]

/-- The submodule cofinite-two count is the literal `(N - 2)` support
level count. -/
theorem sCofiniteTwoCount_eq_literalSubobjectLevelCount_card_sub_two
    (hcard : 2 ≤ Nat.card ι) :
    σ.sClosure.cofiniteTwoCount =
      σ.literalSubobjectLevelCount (Nat.card ι - 2) := by
  rw [sCofiniteTwoCount_eq_levelCount_card_sub_two σ hcard,
    literalSubobjectLevelCount_eq_levelCount]

variable {K : Type uK}
  [Field K] [Algebra K R]
  [∀ i : ι, Module K (σ.obj i)]
  [∀ i : ι, IsScalarTower K R (σ.obj i)]
  [∀ i : ι, FiniteDimensional K (σ.obj i)]

include K in
/-- Quotient-side cofinite-two formula at the literal additive-subcategory
level. -/
theorem literalQuotientLevelCount_card_sub_two_eq_choose_add_mixedBoundaryCount
    (hcard : 2 ≤ Nat.card ι) :
    σ.literalQuotientLevelCount (Nat.card ι - 2) =
      Nat.choose σ.topSplitProjectiveIndices.card 2 +
        σ.qClosure.mixedBoundaryCount := by
  rw [literalQuotientLevelCount_eq_levelCount]
  exact
    qLevelCount_card_sub_two_eq_choose_add_mixedBoundaryCount
      (K := K) σ hcard

include K in
/-- Submodule-side cofinite-two formula at the literal
additive-subcategory level. -/
theorem literalSubobjectLevelCount_card_sub_two_eq_choose_add_mixedBoundaryCount
    (hcard : 2 ≤ Nat.card ι) :
    σ.literalSubobjectLevelCount (Nat.card ι - 2) =
      Nat.choose σ.topSplitInjectiveIndices.card 2 +
        σ.sClosure.mixedBoundaryCount := by
  rw [literalSubobjectLevelCount_eq_levelCount]
  exact
    sLevelCount_card_sub_two_eq_choose_add_mixedBoundaryCount
      (K := K) σ hcard

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton

