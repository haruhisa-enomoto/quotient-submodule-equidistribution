import QuotientSubmoduleEquidistribution.RepresentationTheory.MaximalFlagAuslanderPackage
import QuotientSubmoduleEquidistribution.RepresentationTheory.TsukamotoRadicalSandwichBridge
import QuotientSubmoduleEquidistribution.RepresentationTheory.AuslanderEndArtinian

/-!
# From maximal quotient-closed flags to right-strong heredity chains

This file combines the coordinate-ideal projectivity theorem with the
right-handed radical-sandwich direction of Tsukamoto's Lemma 3.18.  The
only ring-theoretic input left explicit is Artinianity of the successive
coordinate quotients.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution
namespace IndecomposableSkeleton
namespace LegalQuotientDeletionChain

open AuslanderEquivalence
open AuslanderEquivalence.CoordinateIdempotent

universe uR uι wR uK

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
  FintypeCat.fintype

local instance strongHereditySkeletonProjectiveTarget_hasFiniteBiproducts :
    HasFiniteBiproducts (skeletonProjectiveTarget σ) :=
  CategoricalAdditiveSubcategory.hasFiniteBiproductsOfEquivalence
    (skeletonAuslanderEquivalence σ)

/-- Cosemisimplicity of every target factor gives the radical-sandwich
condition for the associated coordinate ideals, provided the corresponding
ring quotients are Artinian. -/
theorem flagIdealChain_radicalSandwich_of_artinianQuotients
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure)
    (hartinian :
      ∀ i : Fin (Fintype.card ι),
        IsArtinianRing
          (skeletonAuslanderAlgebra σ ⧸
            ((flagIdealChain (K := K) σ s).ideal i.succ).asIdeal)) :
    ∀ i : Fin (Fintype.card ι),
      Tsukamoto.RadicalSandwichZero
        ((flagIdealChain (K := K) σ s).ideal i.castSucc)
        ((flagIdealChain (K := K) σ s).ideal i.succ) := by
  intro i
  let d := FlagSourceChain (K := K) σ s
  let e :=
    skeletonCoordinateProjector σ (d.support i.castSucc)
  let f :=
    skeletonCoordinateProjector σ (d.support i.succ)
  have he : IsIdempotentElem e :=
    coordinateProjector_isIdempotent
      σ.obj (d.support i.castSucc)
  have hf : IsIdempotentElem f :=
    coordinateProjector_isIdempotent
      σ.obj (d.support i.succ)
  have hartinian' := hartinian i
  change
    IsArtinianRing
      (skeletonAuslanderAlgebra σ ⧸
        (Tsukamoto.principalTwoSidedIdeal f).asIdeal)
    at hartinian'
  letI :
      IsArtinianRing
        (skeletonAuslanderAlgebra σ ⧸
          (Tsukamoto.principalTwoSidedIdeal f).asIdeal) :=
    hartinian'
  have hUpper :
      ((flagTargetChain (K := K) σ s).term
          i.castSucc).1.carrier =
        fun X : skeletonProjectiveTarget σ ↦
          Tsukamoto.addPrincipalRightModule e X.obj := by
    exact flagTermPrincipalAlignment
      (K := K) σ s i.castSucc
  have hLower :
      ((flagTargetChain (K := K) σ s).term
          i.succ).1.carrier =
        fun X : skeletonProjectiveTarget σ ↦
          Tsukamoto.addPrincipalRightModule f X.obj := by
    exact flagTermPrincipalAlignment
      (K := K) σ s i.succ
  change
    Tsukamoto.RadicalSandwichZero
      (Tsukamoto.principalTwoSidedIdeal e)
      (Tsukamoto.principalTwoSidedIdeal f)
  exact
    TsukamotoRadicalSandwichBridge.radicalSandwichZero_of_aligned_factorIsCosemisimple
        he hf
        ((flagTargetChain (K := K) σ s).term
          i.castSucc).1
        ((flagTargetChain (K := K) σ s).term
          i.succ).1
        hUpper hLower
        ((flagTargetChain (K := K) σ s).step_cosemisimple i)

/-- Under Artinianity of the successive quotients, the coordinate chain of
a maximal quotient-closed flag is a right-strong heredity chain. -/
theorem flagIdealChain_isRightStrongHeredity_of_artinianQuotients
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure)
    (hartinian :
      ∀ i : Fin (Fintype.card ι),
        IsArtinianRing
          (skeletonAuslanderAlgebra σ ⧸
            ((flagIdealChain (K := K) σ s).ideal i.succ).asIdeal)) :
    (flagIdealChain (K := K) σ s).IsRightStrongHeredity :=
  ⟨flagIdealChain_rightProjective (K := K) σ s,
    flagIdealChain_radicalSandwich_of_artinianQuotients
      (K := K) σ s hartinian⟩

/-- Existential right-strong-heredity-chain package obtained from a maximal
quotient-closed flag and Artinianity of its successive coordinate
quotients. -/
theorem hasRightStrongHeredityChain_of_closedFlag_of_artinianQuotients
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure)
    (hartinian :
      ∀ i : Fin (Fintype.card ι),
        IsArtinianRing
          (skeletonAuslanderAlgebra σ ⧸
            ((flagIdealChain (K := K) σ s).ideal i.succ).asIdeal)) :
    Tsukamoto.HasRightStrongHeredityChain
      (skeletonAuslanderAlgebra σ) :=
  ⟨Fintype.card ι, flagIdealChain (K := K) σ s,
    flagIdealChain_isRightStrongHeredity_of_artinianQuotients
      (K := K) σ s hartinian⟩

/-- Under the standing finite-dimensional-skeleton hypotheses, Artinianity
of all successive quotients is automatic. -/
theorem flagIdealChain_isRightStrongHeredity
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure) :
    (flagIdealChain (K := K) σ s).IsRightStrongHeredity := by
  letI : IsArtinianRing (skeletonAuslanderAlgebra σ) :=
    isArtinianRing_skeletonAuslanderAlgebra (K := K) σ
  exact
    flagIdealChain_isRightStrongHeredity_of_artinianQuotients
      (K := K) σ s (fun _ ↦ inferInstance)

include K

/-- A maximal quotient-closed flag on a finite-dimensional skeleton
canonically yields a right-strong heredity chain in its Auslander
endomorphism ring. -/
theorem hasRightStrongHeredityChain_of_closedFlag
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure) :
    Tsukamoto.HasRightStrongHeredityChain
      (skeletonAuslanderAlgebra σ) :=
  ⟨Fintype.card ι, flagIdealChain (K := K) σ s,
    flagIdealChain_isRightStrongHeredity
      (K := K) σ s⟩

end LegalQuotientDeletionChain
end IndecomposableSkeleton
end QuotientSubmoduleEquidistribution
