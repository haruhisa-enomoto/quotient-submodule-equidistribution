import QuotientSubmoduleEquidistribution.RepresentationTheory.MaximalFlagAuslanderPackage
import QuotientSubmoduleEquidistribution.RepresentationTheory.LeftIdealQuotientTransport
import QuotientSubmoduleEquidistribution.RepresentationTheory.TsukamotoLeftRejectiveBridge

/-!
# A maximal subobject-closed flag on both sides of the Auslander equivalence

This is the left-hand companion to `MaximalFlagAuslanderPackage`.  It
combines the arbitrary saturated total target left-rejective chain with the
coordinate idempotent-ideal chain, proves the literal termwise
identification with `add(eᵢ Γ)`, and applies the left-handed Tsukamoto
bridge to obtain left-projectivity of every nonfinal coordinate ideal.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution
namespace IndecomposableSkeleton
namespace LegalSubobjectDeletionChain

open AuslanderEquivalence
open AuslanderEquivalence.CoordinateIdempotent

universe uA uR uι wR uK

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι}
  (σ : IndecomposableSkeleton.{uR, uι, wR} R ι)
  [Fintype ι]
  {K : Type uK} [Field K] [Algebra K R]
  [∀ i : ι, Module K (σ.obj i)]
  [∀ i : ι, IsScalarTower K R (σ.obj i)]
  [∀ i : ι, FiniteDimensional K (σ.obj i)]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

local instance leftFlagSkeletonProjectiveTarget_hasFiniteBiproducts :
    HasFiniteBiproducts (skeletonProjectiveTarget σ) :=
  CategoricalAdditiveSubcategory.hasFiniteBiproductsOfEquivalence
    (skeletonAuslanderEquivalence σ)

/-- The legal subobject-deletion chain reconstructed from an `s`-closed
maximal flag. -/
abbrev LeftFlagSourceChain
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.sClosure) :=
  ofClosedFlag (K := K) σ s

/-- The saturated total left-rejective chain in the finite-projective
Auslander target associated to the flag. -/
abbrev leftFlagTargetChain
    (hfinite :
      ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.sClosure) :
    SaturatedTotalTargetLeftRejectiveChain σ hfinite
      (skeletonAuslanderEquivalence σ) :=
  saturatedTotalTargetLeftRejectiveChainOfClosedFlag
    (K := K) σ hfinite (skeletonAuslanderEquivalence σ) s

/-- The coordinate principal-ideal chain attached to the support deletion
chain underlying the same `s`-closed flag. -/
abbrev leftFlagIdealChain
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.sClosure) :
    Tsukamoto.IdempotentIdealChain
      (skeletonAuslanderAlgebra σ) (Fintype.card ι) :=
  idempotentIdealChainOfSaturatedSupportDeletion σ
    (LeftFlagSourceChain (K := K) σ s).toSaturatedSupport

/-- Explicit coordinate idempotents presenting every term of the left
flag's ideal chain. -/
def leftFlagIdempotentPresentation
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.sClosure) :
    (leftFlagIdealChain (K := K) σ s).IdempotentPresentation :=
  idempotentPresentationOfSupportChain σ
    (LeftFlagSourceChain (K := K) σ s).support
    (saturatedSupportDeletionChain_strictAnti
      (LeftFlagSourceChain (K := K) σ s).toSaturatedSupport)
    (LeftFlagSourceChain (K := K) σ s).top
    (LeftFlagSourceChain (K := K) σ s).bottom

/-- Literal termwise compatibility between the transported target
left-rejective chain and the coordinate principal modules `eᵢ Γ`. -/
def LeftFlagTermPrincipalAlignment
    (hfinite :
      ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.sClosure) : Prop :=
  ∀ i : Fin (Fintype.card ι + 1),
    (targetLeftRejectiveTerm σ
        (skeletonAuslanderEquivalence σ) hfinite
        (LeftFlagSourceChain (K := K) σ s) i).1.carrier =
      (fun X : skeletonProjectiveTarget σ ↦
        Tsukamoto.addPrincipalRightModule
          (skeletonCoordinateProjector σ
            ((LeftFlagSourceChain (K := K) σ s).support i))
          X.obj)

/-- The left target terms are automatically the literal
`add(eᵢ Γ)`-subcategories.  This uses the handedness-independent
finite-additive alignment proved for the Auslander equivalence. -/
theorem leftFlagTermPrincipalAlignment
    (hfinite :
      ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.sClosure) :
    LeftFlagTermPrincipalAlignment (K := K) σ hfinite s := by
  intro i
  funext X
  apply propext
  rw [targetLeftRejectiveTerm_subcategory]
  exact
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.LegalQuotientDeletionChain.transportedGenerated_carrier_iff_addPrincipal
      σ ((LeftFlagSourceChain (K := K) σ s).support i) X

/-- Literal public shape of the left-handed Tsukamoto bridge. -/
def LiteralLeftTsukamotoBridge
    (A : Type uA) [Ring A] : Prop :=
  ∀ (e : A), IsIdempotentElem e →
    CategoricalRejective.IsLeftRejective
      (fun X :
        (AuslanderEquivalence.finiteProjectiveModules
          Aᵐᵒᵖ).FullSubcategory ↦
        Tsukamoto.addPrincipalRightModule e X.obj) →
    Tsukamoto.IsLeftProjectiveIdeal
      (Tsukamoto.principalTwoSidedIdeal e)

/-- The literal left Tsukamoto bridge, discharged without Artinian or
finite-dimensional assumptions. -/
theorem literalLeftTsukamotoBridge
    (A : Type uA) [Ring A] :
    LiteralLeftTsukamotoBridge A := by
  intro e he hlr
  exact
    Tsukamoto.LeftBridge.principalTwoSidedIdeal_leftProjective_of_literal_leftRejective
        he hlr

/-- Conditional form retained for downstream uses which supply an
alternative realization of the left Tsukamoto bridge. -/
theorem leftFlagIdealChain_leftProjective_of_bridge
    (hfinite :
      ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (bridge :
      LiteralLeftTsukamotoBridge
        (skeletonAuslanderAlgebra σ))
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.sClosure) :
    ∀ i : Fin (Fintype.card ι),
      Tsukamoto.IsLeftProjectiveIdeal
        ((leftFlagIdealChain (K := K) σ s).ideal i.castSucc) := by
  intro i
  let d := LeftFlagSourceChain (K := K) σ s
  let e :=
    skeletonCoordinateProjector σ (d.support i.castSucc)
  have hlr :
      CategoricalRejective.IsLeftRejective
        (fun X : skeletonProjectiveTarget σ ↦
          Tsukamoto.addPrincipalRightModule e X.obj) := by
    rw [← leftFlagTermPrincipalAlignment
      (K := K) σ hfinite s i.castSucc]
    exact
      (targetLeftRejectiveTerm σ
        (skeletonAuslanderEquivalence σ) hfinite
        d i.castSucc).2
  exact
    bridge e
      (coordinateProjector_isIdempotent σ.obj
        (d.support i.castSucc))
      hlr

/-- Every nonfinal coordinate ideal attached to a maximal subobject-closed
flag is projective as a left module. -/
theorem leftFlagIdealChain_leftProjective
    (hfinite :
      ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.sClosure) :
    ∀ i : Fin (Fintype.card ι),
      Tsukamoto.IsLeftProjectiveIdeal
        ((leftFlagIdealChain (K := K) σ s).ideal i.castSucc) :=
  leftFlagIdealChain_leftProjective_of_bridge
    (K := K) σ hfinite
      (literalLeftTsukamotoBridge
        (skeletonAuslanderAlgebra σ)) s

/-- Compact left-hand package, including both literal principal-term
alignment and left-projectivity of the associated coordinate ideals. -/
structure MaximalLeftFlagAuslanderPackage
    (hfinite :
      ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.sClosure) where
  targetChain :
    SaturatedTotalTargetLeftRejectiveChain σ hfinite
      (skeletonAuslanderEquivalence σ)
  idealChain :
    Tsukamoto.IdempotentIdealChain
      (skeletonAuslanderAlgebra σ) (Fintype.card ι)
  presentation : idealChain.IdempotentPresentation
  term_principal :
    LeftFlagTermPrincipalAlignment (K := K) σ hfinite s
  ideal_leftProjective :
    ∀ i : Fin (Fintype.card ι),
      Tsukamoto.IsLeftProjectiveIdeal
        (idealChain.ideal i.castSucc)

/-- Canonical combined package attached to a maximal `s`-closed flag. -/
def maximalLeftFlagAuslanderPackage
    (hfinite :
      ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.sClosure) :
    MaximalLeftFlagAuslanderPackage (K := K) σ hfinite s where
  targetChain := leftFlagTargetChain (K := K) σ hfinite s
  idealChain := leftFlagIdealChain (K := K) σ s
  presentation := leftFlagIdempotentPresentation (K := K) σ s
  term_principal :=
    leftFlagTermPrincipalAlignment (K := K) σ hfinite s
  ideal_leftProjective :=
    leftFlagIdealChain_leftProjective
      (K := K) σ hfinite s

end LegalSubobjectDeletionChain
end IndecomposableSkeleton
end QuotientSubmoduleEquidistribution
