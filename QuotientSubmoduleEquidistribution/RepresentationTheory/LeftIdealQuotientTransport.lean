import QuotientSubmoduleEquidistribution.RepresentationTheory.IdealQuotientTransport
import QuotientSubmoduleEquidistribution.RepresentationTheory.LeftRejectiveChains

/-!
# Transporting total left rejective chains

The generic ideal-quotient equivalence is independent of handedness.  This
file applies it to legal subobject-closed chains, completing the target-side
left-rejective analogue: ambient left rejectivity, saturated covers, and
zero-radical successive factors all survive the Auslander equivalence.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe uR uι w vD uD

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι} [Fintype ι]
  (σ : IndecomposableSkeleton.{uR, uι, w} R ι)
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasFiniteBiproducts D]

open
  QuotientSubmoduleEquidistribution.CategoricalAdditiveSubcategory.ModuleBridge

namespace LegalSubobjectDeletionChain

/-- An arbitrary saturated endpoint chain in the full target poset of
ambient left-rejective additive subcategories. -/
abbrev SaturatedTargetLeftRejectiveChain
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D) :=
  QuotientSubmoduleEquidistribution.SetClosure.SaturatedOrderDeletionChain
    (sClosedSupportTargetLeftRejectiveOrderIso
      σ hfinite E)

/-- An arbitrary saturated total left-rejective target chain. -/
structure SaturatedTotalTargetLeftRejectiveChain
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D)
    extends SaturatedTargetLeftRejectiveChain
      σ hfinite E where
  step_cosemisimple :
    ∀ i : Fin (Fintype.card ι),
      QuotientSubmoduleEquidistribution.CategoricalAdditiveSubcategory.Subcategory.FactorIsCosemisimple
        (term i.castSucc).1
        (term i.succ).1

/-- Every arbitrary saturated target left-rejective endpoint chain pulls
back to a genuine maximal subobject-closed flag. -/
def closedFlagOfSaturatedTargetLeftRejective
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D)
    (d : SaturatedTargetLeftRejectiveChain
      σ hfinite E) :
    QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.sClosure :=
  d.toClosedFlag

/-- Consequently every arbitrary saturated total left-rejective target
chain arises from a maximal subobject-closed flag after pullback. -/
def closedFlagOfSaturatedTotalTargetLeftRejective
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D)
    (d : SaturatedTotalTargetLeftRejectiveChain
      σ hfinite E) :
    QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.sClosure :=
  closedFlagOfSaturatedTargetLeftRejective
    σ hfinite E d.toSaturatedOrderDeletionChain

/-- The target left-rejective term has exactly the transported generated
subcategory as its underlying additive subcategory. -/
theorem targetLeftRejectiveTerm_subcategory
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D)
    (d : Chain σ)
    (i : Fin (Fintype.card ι + 1)) :
    (targetLeftRejectiveTerm σ E hfinite d i).1 =
      σ.transportedGeneratedSubcategory E (d.support i) :=
  rfl

/-- Every cosemisimple source step transports to a cosemisimple factor of
the corresponding target left-rejective terms. -/
theorem targetLeftRejectiveTerm_step_cosemisimple
    (E : FGModuleCat.{w} R ≌ D)
    (d : Chain σ)
    (hd : IsTotalLeftRejectiveChain σ d)
    (i : Fin (Fintype.card ι)) :
    σ.TransportedFactorIsCosemisimple E
      (d.support i.castSucc)
      (d.support i.castSucc \ {d.removed i}) :=
  (σ.onePointFactorIsCosemisimple_iff_transported
    E (d.support i.castSucc) (d.removed i)).1
      (hd.step_cosemisimple i)

/-- Package the transported terms of a source total left chain as an
arbitrary target total left chain. -/
def saturatedTotalTargetLeftRejectiveChain
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D)
    (d : Chain σ)
    (hd : IsTotalLeftRejectiveChain σ d) :
    SaturatedTotalTargetLeftRejectiveChain
      σ hfinite E where
  term i := targetLeftRejectiveTerm σ E hfinite d i
  top := by
    apply congrArg
      (sClosedSupportTargetLeftRejectiveOrderIso
        σ hfinite E)
    apply Subtype.ext
    exact d.top
  bottom := by
    apply congrArg
      (sClosedSupportTargetLeftRejectiveOrderIso
        σ hfinite E)
    apply Subtype.ext
    simpa only [closedSupportAt,
      QuotientSubmoduleEquidistribution.SetClosure.coe_bot,
      (sClosure_isClosed_empty σ).closure_eq] using
        d.bottom
  step_covBy i :=
    targetLeftRejectiveTerm_succ_covBy
      σ E hfinite d i
  step_cosemisimple i := by
    rw [targetLeftRejectiveTerm_subcategory
        σ hfinite E d i.castSucc,
      targetLeftRejectiveTerm_subcategory
        σ hfinite E d i.succ]
    change
      σ.TransportedFactorIsCosemisimple E
        (d.support i.castSucc) (d.support i.succ)
    rw [d.step i]
    exact
      targetLeftRejectiveTerm_step_cosemisimple
        σ E d hd i

/-- The arbitrary target-total-left presentation attached directly to a
maximal subobject-closed flag. -/
def saturatedTotalTargetLeftRejectiveChainOfClosedFlag
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D)
    (s :
      QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag
        σ.sClosure) :
    SaturatedTotalTargetLeftRejectiveChain
      σ hfinite E :=
  saturatedTotalTargetLeftRejectiveChain
    σ hfinite E (ofClosedFlag (K := K) σ s)
      (ofClosedFlag_isTotalLeftRejectiveChain
        (K := K) σ hfinite s)

/-- Pulling back a transported target left chain recovers the increasing
closed-support enumeration of its source legal chain. -/
theorem saturatedTotalTargetLeftRejectiveChain_ascending
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D)
    (d : Chain σ)
    (hd : IsTotalLeftRejectiveChain σ d)
    (i : Fin (Fintype.card ι + 1)) :
    (saturatedTotalTargetLeftRejectiveChain
        σ hfinite E d hd).toSaturatedOrderDeletionChain.ascending i =
      d.ascending i := by
  apply Subtype.ext
  simp [QuotientSubmoduleEquidistribution.SetClosure.SaturatedOrderDeletionChain.ascending,
    saturatedTotalTargetLeftRejectiveChain,
    targetLeftRejectiveTerm, closedSupportAt,
    QuotientSubmoduleEquidistribution.SetClosure.LegalDeletionChain.ascending]

/-- Pulling the target total-left chain attached to a maximal flag back
along the rejective order isomorphism recovers that flag. -/
theorem closedFlagOfSaturatedTotalTargetLeftRejective_ofClosedFlag
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D)
    (s :
      QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag
        σ.sClosure) :
    closedFlagOfSaturatedTotalTargetLeftRejective
        σ hfinite E
        (saturatedTotalTargetLeftRejectiveChainOfClosedFlag
          (K := K) σ hfinite E s) =
      s := by
  let d := ofClosedFlag (K := K) σ s
  let hd : IsTotalLeftRejectiveChain σ d :=
    ofClosedFlag_isTotalLeftRejectiveChain
      (K := K) σ hfinite s
  change
    (saturatedTotalTargetLeftRejectiveChain
        σ hfinite E d hd).toSaturatedOrderDeletionChain.toClosedFlag =
      s
  calc
    _ = d.toClosedFlag (sClosure_isClosed_empty σ) := by
      apply
        QuotientSubmoduleEquidistribution.SetClosure.SaturatedOrderDeletionChain.toClosedFlag_eq_legalToClosedFlag
      exact fun i ↦
        saturatedTotalTargetLeftRejectiveChain_ascending
          σ hfinite E d hd i
    _ = s :=
      ofClosedFlag_reconstructs (K := K) σ s

/-- The complete target-side total-left package. -/
structure IsTransportedTotalLeftRejectiveChain
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D)
    (d : Chain σ) : Prop where
  term_leftRejective :
    ∀ i : Fin (Fintype.card ι + 1),
      CategoricalRejective.IsLeftRejective
        (targetLeftRejectiveTerm σ E hfinite d i).1.carrier
  step_covBy :
    ∀ i : Fin (Fintype.card ι),
      targetLeftRejectiveTerm σ E hfinite d i.succ ⋖
        targetLeftRejectiveTerm σ E hfinite d i.castSucc
  step_cosemisimple :
    ∀ i : Fin (Fintype.card ι),
      σ.TransportedFactorIsCosemisimple E
        (d.support i.castSucc)
        (d.support i.castSucc \ {d.removed i})

/-- Transporting a legal total left-rejective source chain gives the full
target-side package step by step. -/
theorem isTransportedTotalLeftRejectiveChain
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D)
    (d : Chain σ)
    (hd : IsTotalLeftRejectiveChain σ d) :
    IsTransportedTotalLeftRejectiveChain σ hfinite E d where
  term_leftRejective i :=
    (targetLeftRejectiveTerm σ E hfinite d i).2
  step_covBy i :=
    targetLeftRejectiveTerm_succ_covBy
      σ E hfinite d i
  step_cosemisimple i :=
    targetLeftRejectiveTerm_step_cosemisimple
      σ E d hd i

/-- A maximal subobject-closed flag gives the full saturated total
left-rejective chain in the equivalent target category. -/
theorem ofClosedFlag_isTransportedTotalLeftRejectiveChain
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (hfinite :
      ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (E : FGModuleCat.{w} R ≌ D)
    (s :
      QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag
        σ.sClosure) :
    IsTransportedTotalLeftRejectiveChain σ hfinite E
      (ofClosedFlag (K := K) σ s) :=
  isTransportedTotalLeftRejectiveChain
    σ hfinite E (ofClosedFlag (K := K) σ s)
      (ofClosedFlag_isTotalLeftRejectiveChain
        (K := K) σ hfinite s)

end LegalSubobjectDeletionChain

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
