import QuotientSubmoduleEquidistribution.ConvexGeometry.MaximalChains
import QuotientSubmoduleEquidistribution.RepresentationTheory.OnePointIdealQuotient
import QuotientSubmoduleEquidistribution.RepresentationTheory.GenericAdditiveRejective

/-!
# Maximal quotient flags and total right rejective chains

This file proves the chain-level part of the manuscript’s quasi-hereditary
bridge.  It constructs saturated total right rejective chains from maximal
quotient-closed flags and recovers maximal flags from arbitrary saturated
endpoint chains whose terms are ambient right rejective.

The algebraic equivalence with right-strong heredity chains and the resulting
right-strongly quasi-hereditary structure are the separate Tsukamoto input;
they are not asserted here.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

open CategoryTheory
open CategoryTheory.Limits

universe uR uι w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι} [Fintype ι]
  (σ : IndecomposableSkeleton.{uR, uι, w} R ι)

/-- The literal statement that the one-point ideal factor at `x` in
`add S` is cosemisimple (has zero categorical radical). -/
def OnePointFactorIsCosemisimple
    (S : Set ι) (x : ι) : Prop :=
  let I := σ.factorThroughAddIdeal S (S \ {x})
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  letI : HasFiniteBiproducts
      (CategoryTheory.Quotient I.rel) :=
    σ.factorQuotientHasFiniteBiproducts S (S \ {x})
  QuotientSubmoduleEquidistribution.CategoricalRadical.HasZeroRadical
    (CategoryTheory.Quotient I.rel)

/-- A saturated endpoint chain of arbitrary supports whose associated
literal additive subcategories are ambient right rejective.

This is deliberately weaker than a total right rejective chain: no
cosemisimplicity is assumed.  It is exactly the data needed for the
non-tautological converse from rejective subcategories to a maximal
quotient-closed flag. -/
structure SaturatedAmbientRightRejectiveChain
    extends
      QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain ι where
  term_rightRejective :
    ∀ i, IsRightRejective (σ.generated (support i))

/-- A saturated total right rejective chain presented on arbitrary
supports: ambient right rejectivity plus cosemisimplicity of every
successive one-point factor. -/
structure SaturatedTotalRightRejectiveChain
    extends SaturatedAmbientRightRejectiveChain σ where
  step_cosemisimple :
    ∀ i, σ.OnePointFactorIsCosemisimple
      (support i.castSucc) (removed i)

/-- The support-side form of a total right rejective chain used in the
paper: every term is right rejective in the ambient module category,
and every successive one-point ideal factor is cosemisimple.

Saturation and the endpoint conditions are already carried by
`LegalDeletionChain`.  Right rejectivity of the lower subcategory
*inside* the preceding term, although discussed in the manuscript
proof, is intentionally not a field: it is not part of the paper's
stated definition of a total right rejective chain. -/
structure IsTotalRightRejectiveChain
    (d : QuotientSubmoduleEquidistribution.SetClosure.LegalDeletionChain
      σ.qClosure) : Prop where
  term_rightRejective :
    ∀ i, IsRightRejective (σ.generated (d.support i))
  step_cosemisimple :
    ∀ i, σ.OnePointFactorIsCosemisimple
      (d.support i.castSucc) (d.removed i)

namespace LegalQuotientDeletionChain

abbrev Chain :=
  QuotientSubmoduleEquidistribution.SetClosure.LegalDeletionChain σ.qClosure

/-- A term of a legal quotient deletion chain as an actual element of
the quotient-closed support lattice. -/
def closedSupportAt
    (d : Chain σ)
    (i : Fin (Fintype.card ι + 1)) :
    σ.qClosure.Closeds :=
  ⟨d.support i, d.closed i⟩

@[simp]
theorem coe_closedSupportAt
    (d : Chain σ)
    (i : Fin (Fintype.card ι + 1)) :
    (closedSupportAt σ d i : Set ι) = d.support i :=
  rfl

/-- Each top-to-bottom support step is a cover in the quotient-closed
support lattice. -/
theorem closedSupportAt_succ_covBy
    (d : Chain σ)
    (i : Fin (Fintype.card ι)) :
    closedSupportAt σ d i.succ ⋖
      closedSupportAt σ d i.castSucc := by
  simpa only [closedSupportAt,
    QuotientSubmoduleEquidistribution.SetClosure.LegalDeletionChain.ascending,
    Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev] using
      d.ascending_covBy i.rev

/-- Ambient right rejectivity implies quotient closedness term by term,
so an arbitrary saturated ambient-right-rejective support chain is a
legal quotient-side deletion chain. -/
def ofSaturatedAmbientRightRejective
    (d : SaturatedAmbientRightRejectiveChain σ) :
    Chain σ :=
  d.toSaturatedSupportDeletionChain.toLegal
    (fun i ↦
      (qClosed_iff_rightRejective
        σ (d.support i)).2
          (d.term_rightRejective i))

@[simp]
theorem ofSaturatedAmbientRightRejective_support
    (d : SaturatedAmbientRightRejectiveChain σ)
    (i : Fin (Fintype.card ι + 1)) :
    (ofSaturatedAmbientRightRejective σ d).support i =
      d.support i :=
  rfl

/-- Consequently every saturated endpoint chain of ambient
right-rejective subcategories has a genuine maximal closed-set flag.
No cosemisimplicity hypothesis is needed for this converse
combinatorial step. -/
def closedFlagOfSaturatedAmbientRightRejective
    (d : SaturatedAmbientRightRejectiveChain σ) :
    QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure :=
  (ofSaturatedAmbientRightRejective σ d).toClosedFlag
    (qClosure_isClosed_empty σ)

/-- Forgetting cosemisimplicity, a saturated total chain gives the same
legal quotient-deletion presentation. -/
def ofSaturatedTotalRightRejective
    (d : SaturatedTotalRightRejectiveChain σ) :
    Chain σ :=
  ofSaturatedAmbientRightRejective σ
    d.toSaturatedAmbientRightRejectiveChain

/-- The arbitrary-support total-chain presentation becomes the exact
total-right-rejective property on its derived legal deletion chain. -/
theorem ofSaturatedTotalRightRejective_isTotal
    (d : SaturatedTotalRightRejectiveChain σ) :
    IsTotalRightRejectiveChain σ
      (ofSaturatedTotalRightRejective σ d) where
  term_rightRejective :=
    d.term_rightRejective
  step_cosemisimple :=
    d.step_cosemisimple

/-- Hence every saturated total right rejective support chain
determines a maximal quotient-closed flag. -/
def closedFlagOfSaturatedTotalRightRejective
    (d : SaturatedTotalRightRejectiveChain σ) :
    QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure :=
  (ofSaturatedTotalRightRejective σ d).toClosedFlag
    (qClosure_isClosed_empty σ)

section TargetTransport

open
  QuotientSubmoduleEquidistribution.CategoricalAdditiveSubcategory
  QuotientSubmoduleEquidistribution.CategoricalAdditiveSubcategory.ModuleBridge

universe vD uD

variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasFiniteBiproducts D]
  (E : FGModuleCat.{w} R ≌ D)

/-- Transport a legal quotient-chain term to the corresponding ambient
right-rejective additive subcategory of an equivalent target category
(in the paper, the finite-projective Auslander target). -/
def targetRightRejectiveTerm
    (d : Chain σ)
    (i : Fin (Fintype.card ι + 1)) :
    RightRejectiveSubcategory D :=
  qClosedSupportTargetRightRejectiveOrderIso σ E
    (closedSupportAt σ d i)

/-- Saturation is preserved by the Auslander/order equivalence: each
successive target right-rejective term is a cover of the next one in
the full poset of ambient right-rejective additive subcategories. -/
theorem targetRightRejectiveTerm_succ_covBy
    (d : Chain σ)
    (i : Fin (Fintype.card ι)) :
    targetRightRejectiveTerm σ E d i.succ ⋖
      targetRightRejectiveTerm σ E d i.castSucc := by
  rw [targetRightRejectiveTerm,
    targetRightRejectiveTerm,
    apply_covBy_apply_iff]
  exact closedSupportAt_succ_covBy σ d i

end TargetTransport

/-- The canonical saturated legal deletion presentation of a maximal
quotient-closed flag. -/
def ofClosedFlag
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (s :
      QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag
        σ.qClosure) :
    Chain σ :=
  s.toLegalDeletionChain
    (qClosure_isAntiExchange_of_finiteDimensional
      (K := K) σ)
    (qClosure_isClosed_empty σ)

theorem ofClosedFlag_reconstructs
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (s :
      QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag
        σ.qClosure) :
    (ofClosedFlag (K := K) σ s).toClosedFlag
        (qClosure_isClosed_empty σ) =
      s :=
  QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag.toClosedFlag_toLegalDeletionChain
      (qClosure_isAntiExchange_of_finiteDimensional
        (K := K) σ)
      (qClosure_isClosed_empty σ) s

/-- A legal quotient-closed one-point deletion removes a relative split
projective. -/
theorem removed_isRelativeSplitProjective
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (d : Chain σ)
    (i : Fin (Fintype.card ι)) :
    σ.IsRelativeSplitProjective
      (d.support i.castSucc) (d.removed i) := by
  letI : ∀ j : ι,
      IsArtinianRing (Module.End R (σ.obj j)) :=
    fun j ↦
      QuotientSubmoduleEquidistribution.isArtinianRing_moduleEnd_of_finiteDimensional
        (K := K) (B := R) (M := σ.obj j)
  have hlower :
      σ.qClosure.IsClosed
        (d.support i.castSucc \ {d.removed i}) := by
    rw [← d.step i]
    exact d.closed i.succ
  have hnot :
      d.removed i ∉
        σ.qClosure
          (d.support i.castSucc \ {d.removed i}) := by
    rw [hlower.closure_eq]
    simp
  exact
    σ.isRelativeSplitProjective_of_not_mem_qClosure_sdiff
      (d.support i.castSucc) (d.removed i) hnot

/-- Every saturated legal quotient-side deletion chain is a total right
rejective chain in the precise support-side sense above.  The
cosemisimplicity clause is the literal categorical ideal quotient proved
in `OnePointIdealQuotient`. -/
theorem isTotalRightRejectiveChain
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (d : Chain σ) :
    IsTotalRightRejectiveChain σ d where
  term_rightRejective i :=
    (qClosed_iff_rightRejective
      σ (d.support i)).1 (d.closed i)
  step_cosemisimple i := by
    exact
      (relativeSplitProjective_deletion_quotientCategory_hasZeroRadical
        σ (d.closed i.castSucc) (d.removed_mem i)
        (removed_isRelativeSplitProjective
          (K := K) σ d i)).2

/-- Maximal quotient-closed flags therefore give saturated total right
rejective chains, before invoking any quasi-hereditary theorem. -/
theorem ofClosedFlag_isTotalRightRejectiveChain
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (s :
      QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag
        σ.qClosure) :
    IsTotalRightRejectiveChain σ
      (ofClosedFlag (K := K) σ s) :=
  isTotalRightRejectiveChain
    (K := K) σ (ofClosedFlag (K := K) σ s)

end LegalQuotientDeletionChain

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
