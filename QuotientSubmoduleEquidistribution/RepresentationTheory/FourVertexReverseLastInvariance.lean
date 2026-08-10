import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexReverseLastCrossing
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexOuterMirrorPackaging

/-!
# Reversal invariance of the reverse-last correction

Chaining the status characterization, the fan decomposition, the
collapse at the projective-source boundary, the per-hub fan balance and
the crossed fan equivalence shows that the reverse-last correction
families of the two skeletons are equinumerous.  Combined with the wall
permutation and the deep-anchor mirror invariance this closes the
colevel-four crossed balance, and with it the paper-facing colevel-four
equality.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

section SingleSkeleton

namespace FiniteARTranslationData

variable {K R : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (AR : σ.FiniteARTranslationData)

omit [DecidableEq ι] in
include K in
/-- The reverse-last correction family counts the strict-source fan
cells over all translation-fixed hubs. -/
theorem reverseLast_card_eq_strictSource_sigma :
    Nat.card (AR.BoundaryM6ReverseLastPair σ) =
      Nat.card ((s : AR.FixedHubLabel σ) ×
        {x : (AR.arMeshRotationData σ).InteriorArrow σ //
          ((AR.arMeshRotationData σ).arrowOrbitData σ).InteriorSource
              x ∧
            ¬ ((AR.arMeshRotationData σ).arrowOrbitData
              σ).InteriorTarget x ∧
            AR.FanAttached σ s.1.1 x}) := by
  refine Nat.card_congr
    (((boundaryM6ReverseLastPairEquivFixedMiddle (K := K) σ
      AR).trans (fixedMiddleEquivSigmaFan σ AR)).trans
      (Equiv.sigmaCongrRight fun s ↦
        Equiv.subtypeEquivRight fun x ↦ ?_))
  exact and_congr_right fun hP ↦ and_congr_right fun _ ↦
    (fanAttached_iff_target_of_interior_source (K := K) σ AR
      s.1.1 s.1.2 s.2 x hP).symm

omit [DecidableEq ι] in
/-- The fan balance summed over all translation-fixed hubs. -/
theorem sigma_fan_balance :
    Nat.card ((s : AR.FixedHubLabel σ) ×
        {x : (AR.arMeshRotationData σ).InteriorArrow σ //
          ((AR.arMeshRotationData σ).arrowOrbitData σ).InteriorSource
              x ∧
            ¬ ((AR.arMeshRotationData σ).arrowOrbitData
              σ).InteriorTarget x ∧
            AR.FanAttached σ s.1.1 x}) =
      Nat.card ((s : AR.FixedHubLabel σ) ×
        {x : (AR.arMeshRotationData σ).InteriorArrow σ //
          ((AR.arMeshRotationData σ).arrowOrbitData σ).InteriorTarget
              x ∧
            ¬ ((AR.arMeshRotationData σ).arrowOrbitData
              σ).InteriorSource x ∧
            AR.FanAttached σ s.1.1 x}) := by
  haveI : Finite (AR.FixedHubLabel σ) :=
    Finite.of_injective (fun s ↦ s.1.1)
      fun a b h ↦ Subtype.ext (Subtype.ext h)
  haveI : Fintype (AR.FixedHubLabel σ) := Fintype.ofFinite _
  rw [Nat.card_sigma, Nat.card_sigma]
  exact Finset.sum_congr rfl fun s _ ↦
    fan_strict_source_card_eq_strict_target_card σ AR
      s.1.1 s.1.2 s.2

end FiniteARTranslationData

end SingleSkeleton

variable {K R S : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [Ring S] [Algebra K S] [FiniteDimensional K S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace AlignedBiduality

omit [DecidableEq ι] [DecidableEq κ] in
include K in
/-- The reverse-last correction families of the two skeletons are
equinumerous. -/
theorem reverseLast_card_reversal_invariant
    (D : AlignedBiduality σ τ)
    (ARsigma : σ.FiniteARTranslationData)
    (ARtau : τ.FiniteARTranslationData) :
    Fintype.card (ARtau.BoundaryM6ReverseLastPair τ) =
      Fintype.card (ARsigma.BoundaryM6ReverseLastPair σ) := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    FiniteARTranslationData.reverseLast_card_eq_strictSource_sigma
      (K := K) τ ARtau,
    FiniteARTranslationData.reverseLast_card_eq_strictSource_sigma
      (K := K) σ ARsigma,
    FiniteARTranslationData.sigma_fan_balance σ ARsigma]
  exact Nat.card_congr (D.reverseLastSigmaCrossEquiv σ τ ARsigma ARtau)

/-- The colevel-four crossed balance holds unconditionally. -/
theorem intrinsicOuterLocalStrataReversalBalance_holds
    (D : AlignedBiduality σ τ) :
    IntrinsicOuterLocalStrataReversalBalance
      (k := K) (R := R) (S := S) σ τ := by
  apply D.intrinsicOuterLocalStrataReversalBalance_of_wallInvariance
    (K := K) σ τ
  have hw := D.wall_sum_reversal_invariant (K := K) σ τ
    (σ.finiteDimensionalARTranslationData K R)
    (τ.finiteDimensionalARTranslationData K S)
  have hr := D.reverseLast_card_reversal_invariant (K := K) σ τ
    (σ.finiteDimensionalARTranslationData K R)
    (τ.finiteDimensionalARTranslationData K S)
  omega

end AlignedBiduality

include K in
/-- Paper-facing colevel-four equality, now unconditional. -/
theorem levelCount_card_sub_four_eq_of_alignedBiduality
    [IsAlgClosed K]
    (D : AlignedBiduality σ τ) (hfour : 4 ≤ Nat.card ι) :
    σ.qClosure.levelCount (Nat.card ι - 4) =
      σ.sClosure.levelCount (Nat.card ι - 4) :=
  levelCount_card_sub_four_eq_of_intrinsicOuterLocalStrata
    (k := K) σ τ D hfour
    (D.intrinsicOuterLocalStrataReversalBalance_holds σ τ)

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
