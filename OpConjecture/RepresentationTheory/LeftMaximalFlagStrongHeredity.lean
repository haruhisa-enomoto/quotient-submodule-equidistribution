import OpConjecture.RepresentationTheory.LeftMaximalFlagAuslanderPackage
import OpConjecture.RepresentationTheory.TsukamotoRadicalSandwichBridge
import OpConjecture.RepresentationTheory.AuslanderEndArtinian

/-!
# From maximal subobject-closed flags to left-strong heredity chains

This is the left-handed companion to `MaximalFlagStrongHeredity`.  It
combines the left projectivity bridge with the same categorical-radical
calculation; the only remaining ring-theoretic input is Artinianity of the
successive coordinate quotients.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace OpConjecture
namespace IndecomposableSkeleton
namespace LegalSubobjectDeletionChain

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

local instance leftStrongHereditySkeletonProjectiveTarget_hasFiniteBiproducts :
    HasFiniteBiproducts (skeletonProjectiveTarget σ) :=
  CategoricalAdditiveSubcategory.hasFiniteBiproductsOfEquivalence
    (skeletonAuslanderEquivalence σ)

/-- Cosemisimplicity of every left-target factor gives the
radical-sandwich condition for the associated coordinate ideals, provided
the corresponding ring quotients are Artinian. -/
theorem leftFlagIdealChain_radicalSandwich_of_artinianQuotients
    (hfinite :
      ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (s : OpConjecture.SetClosure.ClosedFlag σ.sClosure)
    (hartinian :
      ∀ i : Fin (Fintype.card ι),
        IsArtinianRing
          (skeletonAuslanderAlgebra σ ⧸
            ((leftFlagIdealChain (K := K) σ s).ideal
              i.succ).asIdeal)) :
    ∀ i : Fin (Fintype.card ι),
      Tsukamoto.RadicalSandwichZero
        ((leftFlagIdealChain (K := K) σ s).ideal i.castSucc)
        ((leftFlagIdealChain (K := K) σ s).ideal i.succ) := by
  intro i
  let d := LeftFlagSourceChain (K := K) σ s
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
      ((leftFlagTargetChain (K := K) σ hfinite s).term
          i.castSucc).1.carrier =
        fun X : skeletonProjectiveTarget σ ↦
          Tsukamoto.addPrincipalRightModule e X.obj := by
    exact leftFlagTermPrincipalAlignment
      (K := K) σ hfinite s i.castSucc
  have hLower :
      ((leftFlagTargetChain (K := K) σ hfinite s).term
          i.succ).1.carrier =
        fun X : skeletonProjectiveTarget σ ↦
          Tsukamoto.addPrincipalRightModule f X.obj := by
    exact leftFlagTermPrincipalAlignment
      (K := K) σ hfinite s i.succ
  change
    Tsukamoto.RadicalSandwichZero
      (Tsukamoto.principalTwoSidedIdeal e)
      (Tsukamoto.principalTwoSidedIdeal f)
  exact
    TsukamotoRadicalSandwichBridge.radicalSandwichZero_of_aligned_factorIsCosemisimple
      he hf
      ((leftFlagTargetChain (K := K) σ hfinite s).term
        i.castSucc).1
      ((leftFlagTargetChain (K := K) σ hfinite s).term
        i.succ).1
      hUpper hLower
      ((leftFlagTargetChain (K := K) σ hfinite s).step_cosemisimple i)

/-- Under Artinianity of the successive quotients, the coordinate chain of
a maximal subobject-closed flag is a left-strong heredity chain. -/
theorem leftFlagIdealChain_isLeftStrongHeredity_of_artinianQuotients
    (hfinite :
      ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (s : OpConjecture.SetClosure.ClosedFlag σ.sClosure)
    (hartinian :
      ∀ i : Fin (Fintype.card ι),
        IsArtinianRing
          (skeletonAuslanderAlgebra σ ⧸
            ((leftFlagIdealChain (K := K) σ s).ideal
              i.succ).asIdeal)) :
    (leftFlagIdealChain (K := K) σ s).IsLeftStrongHeredity :=
  ⟨leftFlagIdealChain_leftProjective (K := K) σ hfinite s,
    leftFlagIdealChain_radicalSandwich_of_artinianQuotients
      (K := K) σ hfinite s hartinian⟩

/-- Existential left-strong-heredity-chain package obtained from a maximal
subobject-closed flag and Artinianity of its successive coordinate
quotients. -/
theorem hasLeftStrongHeredityChain_of_closedFlag_of_artinianQuotients
    (hfinite :
      ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (s : OpConjecture.SetClosure.ClosedFlag σ.sClosure)
    (hartinian :
      ∀ i : Fin (Fintype.card ι),
        IsArtinianRing
          (skeletonAuslanderAlgebra σ ⧸
            ((leftFlagIdealChain (K := K) σ s).ideal
              i.succ).asIdeal)) :
    Tsukamoto.HasLeftStrongHeredityChain
      (skeletonAuslanderAlgebra σ) :=
  ⟨Fintype.card ι, leftFlagIdealChain (K := K) σ s,
    leftFlagIdealChain_isLeftStrongHeredity_of_artinianQuotients
      (K := K) σ hfinite s hartinian⟩

/-- Under the standing finite-dimensional-skeleton hypotheses, Artinianity
of all successive quotients is automatic. -/
theorem leftFlagIdealChain_isLeftStrongHeredity
    (hfinite :
      ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (s : OpConjecture.SetClosure.ClosedFlag σ.sClosure) :
    (leftFlagIdealChain (K := K) σ s).IsLeftStrongHeredity := by
  letI : IsArtinianRing (skeletonAuslanderAlgebra σ) :=
    LegalQuotientDeletionChain.isArtinianRing_skeletonAuslanderAlgebra
      (K := K) σ
  exact
    leftFlagIdealChain_isLeftStrongHeredity_of_artinianQuotients
      (K := K) σ hfinite s (fun _ ↦ inferInstance)

include K

/-- A maximal subobject-closed flag on a finite-dimensional skeleton
canonically yields a left-strong heredity chain in its Auslander
endomorphism ring. -/
theorem hasLeftStrongHeredityChain_of_closedFlag
    (hfinite :
      ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (s : OpConjecture.SetClosure.ClosedFlag σ.sClosure) :
    Tsukamoto.HasLeftStrongHeredityChain
      (skeletonAuslanderAlgebra σ) :=
  ⟨Fintype.card ι, leftFlagIdealChain (K := K) σ s,
    leftFlagIdealChain_isLeftStrongHeredity
      (K := K) σ hfinite s⟩

end LegalSubobjectDeletionChain
end IndecomposableSkeleton
end OpConjecture
