import OpConjecture.RepresentationTheory.RejectiveChains
import OpConjecture.RepresentationTheory.SplitInjective

/-!
# Maximal subobject flags and total left rejective chains

This is the exact dual chain-level bridge for the subobject-closed lattice.
The one-point cosemisimplicity argument is not postulated: the range of a
nonunit endomorphism is a selected subobject, has smaller finite length, and
therefore factors through the additive subcategory after deleting the
surviving indecomposable.

As on the quotient/right side, the separate algebraic equivalence with
left-strong heredity chains is not asserted here.
-/

noncomputable section

open Set

namespace OpConjecture.IndecomposableSkeleton

open CategoryTheory
open CategoryTheory.Limits

universe uR uι w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι} [Fintype ι]
  (σ : IndecomposableSkeleton.{uR, uι, w} R ι)

/-- A saturated endpoint chain whose literal additive terms are ambient
left rejective. -/
structure SaturatedAmbientLeftRejectiveChain
    extends
      OpConjecture.SetClosure.SaturatedSupportDeletionChain ι where
  term_leftRejective :
    ∀ i, IsLeftRejective (σ.generated (support i))

/-- A saturated total left rejective chain on arbitrary supports: ambient
left rejectivity together with cosemisimplicity of every one-point factor. -/
structure SaturatedTotalLeftRejectiveChain
    extends SaturatedAmbientLeftRejectiveChain σ where
  step_cosemisimple :
    ∀ i, σ.OnePointFactorIsCosemisimple
      (support i.castSucc) (removed i)

/-- Total left rejectivity on a legal subobject-closed deletion chain. -/
structure IsTotalLeftRejectiveChain
    (d : OpConjecture.SetClosure.LegalDeletionChain
      σ.sClosure) : Prop where
  term_leftRejective :
    ∀ i, IsLeftRejective (σ.generated (d.support i))
  step_cosemisimple :
    ∀ i, σ.OnePointFactorIsCosemisimple
      (d.support i.castSucc) (d.removed i)

namespace LegalSubobjectDeletionChain

abbrev Chain :=
  OpConjecture.SetClosure.LegalDeletionChain σ.sClosure

/-- A term of a legal subobject-deletion chain as an actual element of
the subobject-closed support lattice. -/
def closedSupportAt
    (d : Chain σ)
    (i : Fin (Fintype.card ι + 1)) :
    σ.sClosure.Closeds :=
  ⟨d.support i, d.closed i⟩

@[simp]
theorem coe_closedSupportAt
    (d : Chain σ)
    (i : Fin (Fintype.card ι + 1)) :
    (closedSupportAt σ d i : Set ι) = d.support i :=
  rfl

/-- Each top-to-bottom support step is a cover in the subobject-closed
support lattice. -/
theorem closedSupportAt_succ_covBy
    (d : Chain σ)
    (i : Fin (Fintype.card ι)) :
    closedSupportAt σ d i.succ ⋖
      closedSupportAt σ d i.castSucc := by
  simpa only [closedSupportAt,
    OpConjecture.SetClosure.LegalDeletionChain.ascending,
    Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev] using
      d.ascending_covBy i.rev

/-- Ambient left rejectivity implies subobject closedness term by term,
so an arbitrary saturated ambient-left-rejective support chain is legal. -/
def ofSaturatedAmbientLeftRejective
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (d : SaturatedAmbientLeftRejectiveChain σ) :
    Chain σ :=
  d.toSaturatedSupportDeletionChain.toLegal
    (fun i ↦
      (sClosed_iff_leftRejective
        σ hfinite (d.support i)).2
          (d.term_leftRejective i))

@[simp]
theorem ofSaturatedAmbientLeftRejective_support
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (d : SaturatedAmbientLeftRejectiveChain σ)
    (i : Fin (Fintype.card ι + 1)) :
    (ofSaturatedAmbientLeftRejective σ hfinite d).support i =
      d.support i :=
  rfl

/-- Every saturated endpoint chain of ambient left-rejective terms gives a
genuine maximal subobject-closed flag. -/
def closedFlagOfSaturatedAmbientLeftRejective
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (d : SaturatedAmbientLeftRejectiveChain σ) :
    OpConjecture.SetClosure.ClosedFlag σ.sClosure :=
  (ofSaturatedAmbientLeftRejective σ hfinite d).toClosedFlag
    (sClosure_isClosed_empty σ)

/-- Forgetting cosemisimplicity, a saturated total chain has the same legal
subobject-deletion presentation. -/
def ofSaturatedTotalLeftRejective
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (d : SaturatedTotalLeftRejectiveChain σ) :
    Chain σ :=
  ofSaturatedAmbientLeftRejective σ hfinite
    d.toSaturatedAmbientLeftRejectiveChain

/-- The arbitrary-support presentation satisfies the exact total-left
property on its derived legal deletion chain. -/
theorem ofSaturatedTotalLeftRejective_isTotal
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (d : SaturatedTotalLeftRejectiveChain σ) :
    IsTotalLeftRejectiveChain σ
      (ofSaturatedTotalLeftRejective σ hfinite d) where
  term_leftRejective :=
    d.term_leftRejective
  step_cosemisimple :=
    d.step_cosemisimple

/-- Every saturated total left rejective support chain determines a maximal
subobject-closed flag. -/
def closedFlagOfSaturatedTotalLeftRejective
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (d : SaturatedTotalLeftRejectiveChain σ) :
    OpConjecture.SetClosure.ClosedFlag σ.sClosure :=
  (ofSaturatedTotalLeftRejective σ hfinite d).toClosedFlag
    (sClosure_isClosed_empty σ)

section TargetTransport

open
  OpConjecture.CategoricalAdditiveSubcategory
  OpConjecture.CategoricalAdditiveSubcategory.ModuleBridge

universe vD uD

variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasFiniteBiproducts D]
  (E : FGModuleCat.{w} R ≌ D)

/-- Transport a legal subobject-chain term to the corresponding ambient
left-rejective additive subcategory of an equivalent target category. -/
def targetLeftRejectiveTerm
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (d : Chain σ)
    (i : Fin (Fintype.card ι + 1)) :
    LeftRejectiveSubcategory D :=
  sClosedSupportTargetLeftRejectiveOrderIso σ hfinite E
    (closedSupportAt σ d i)

/-- Saturation is preserved by the target left-rejective order
equivalence. -/
theorem targetLeftRejectiveTerm_succ_covBy
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (d : Chain σ)
    (i : Fin (Fintype.card ι)) :
    targetLeftRejectiveTerm σ E hfinite d i.succ ⋖
      targetLeftRejectiveTerm σ E hfinite d i.castSucc := by
  rw [targetLeftRejectiveTerm,
    targetLeftRejectiveTerm,
    apply_covBy_apply_iff]
  exact closedSupportAt_succ_covBy σ d i

end TargetTransport

/-- The canonical saturated legal deletion presentation of a maximal
subobject-closed flag. -/
def ofClosedFlag
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (s :
      OpConjecture.SetClosure.ClosedFlag
        σ.sClosure) :
    Chain σ :=
  s.toLegalDeletionChain
    (sClosure_isAntiExchange_of_finiteDimensional
      (K := K) σ)
    (sClosure_isClosed_empty σ)

theorem ofClosedFlag_reconstructs
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (s :
      OpConjecture.SetClosure.ClosedFlag
        σ.sClosure) :
    (ofClosedFlag (K := K) σ s).toClosedFlag
        (sClosure_isClosed_empty σ) =
      s :=
  OpConjecture.SetClosure.ClosedFlag.toClosedFlag_toLegalDeletionChain
      (sClosure_isAntiExchange_of_finiteDimensional
        (K := K) σ)
      (sClosure_isClosed_empty σ) s

/-- A legal subobject-closed one-point deletion removes a relative split
injective. -/
theorem removed_isRelativeSplitInjective
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (d : Chain σ)
    (i : Fin (Fintype.card ι)) :
    σ.IsRelativeSplitInjective
      (d.support i.castSucc) (d.removed i) := by
  letI : ∀ j : ι,
      IsArtinianRing (Module.End R (σ.obj j)) :=
    fun j ↦
      OpConjecture.isArtinianRing_moduleEnd_of_finiteDimensional
        (K := K) (B := R) (M := σ.obj j)
  have hlower :
      σ.sClosure.IsClosed
        (d.support i.castSucc \ {d.removed i}) := by
    rw [← d.step i]
    exact d.closed i.succ
  have hnot :
      d.removed i ∉
        σ.sClosure
          (d.support i.castSucc \ {d.removed i}) := by
    rw [hlower.closure_eq]
    simp
  exact
    (not_mem_sClosure_diff_iff_relativeSplitInjective
      σ (d.support i.castSucc) (d.removed i)).1 hnot

/-- Every saturated legal subobject-side deletion chain is a total left
rejective chain.  The factor category is the literal ideal quotient and its
zero radical is proved from subobject closedness. -/
theorem isTotalLeftRejectiveChain
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (d : Chain σ) :
    IsTotalLeftRejectiveChain σ d where
  term_leftRejective i :=
    (sClosed_iff_leftRejective
      σ hfinite (d.support i)).1 (d.closed i)
  step_cosemisimple i := by
    exact
      quotientCategory_hasZeroRadical_of_sClosed
        σ (d.closed i.castSucc) (d.removed_mem i)

/-- Maximal subobject-closed flags therefore give saturated total left
rejective chains, before invoking a quasi-hereditary theorem. -/
theorem ofClosedFlag_isTotalLeftRejectiveChain
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (s :
      OpConjecture.SetClosure.ClosedFlag
        σ.sClosure) :
    IsTotalLeftRejectiveChain σ
      (ofClosedFlag (K := K) σ s) :=
  isTotalLeftRejectiveChain
    σ hfinite (ofClosedFlag (K := K) σ s)

end LegalSubobjectDeletionChain

end OpConjecture.IndecomposableSkeleton
