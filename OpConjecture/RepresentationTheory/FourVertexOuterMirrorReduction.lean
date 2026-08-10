import OpConjecture.RepresentationTheory.FourVertexOuterDeepMirrorTransport
import OpConjecture.RepresentationTheory.FourVertexSignedStripReduction

/-!
# Mirror reduction of the surviving outer corner

The deep-anchor outer `M6` family is identified with the deep-image
subtype of its intrinsic stratum, and hence — through the aligned
mirror transport — with the mirror residual cell of the opposite
skeleton.  Substituting both directions into the surviving-outer-corner
balance turns the remaining crossed obligation into aligned invariance
of one same-side quantity: mirror cell + unused `M2` + unused `M3` +
reverse-last.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {K R S : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [Ring S] [Algebra K S] [FiniteDimensional K S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

/-- Deep-anchor outer `M6` terms are exactly the deep-image subtype of
the deep intrinsic stratum. -/
def hookM6DeepAnchorEquivDeepStratumSubtype :
    HookM6Channel.InjectiveFourthDeepAnchor σ AR ≃
      {p : AR.FirstPISecondInteriorNotTwoSourceOuterPair σ //
        p.outer ∈ AR.FirstPIDeepM6Image σ} :=
  (hookM6DeepAnchorEquivFirstPIImage σ AR).trans
    { toFun := fun x ↦
        ⟨{ outer := x.1
           second_nonprojective :=
             FirstPIDeepM6Image.second_nonprojective σ AR x
           second_noninjective :=
             FirstPIDeepM6Image.second_noninjective σ AR x
           second_not_twoSource :=
             FirstPIDeepM6Image.second_not_twoSource σ AR x }, x.2⟩
      invFun := fun s ↦ ⟨s.1.outer, s.2⟩
      left_inv := fun x ↦ Subtype.ext rfl
      right_inv := fun s ↦ by
        apply Subtype.ext
        apply FirstPISecondInteriorNotTwoSourceOuterPair.ext
        rfl }

end FiniteARTranslationData

section MirrorFintype

universe w'

noncomputable instance mirrorResidualCellFintype
    {S' : Type u} [Ring S'] [IsNoetherianRing S']
    {κ' : Type w'} [Fintype κ'] [DecidableEq κ']
    (ρ : IndecomposableSkeleton.{u, w', u} S' κ')
    (AR : ρ.FiniteARTranslationData) :
    Fintype (MirrorResidualCell ρ AR) :=
  Fintype.ofFinite _

end MirrorFintype

namespace AlignedBiduality

omit [Algebra K S] [FiniteDimensional K S] in
include K in
/-- Cardinal form of the unit-one identification: the deep-anchor outer
`M6` family has the size of the opposite mirror residual cell. -/
theorem deepAnchor_card_eq_mirror
    (D : AlignedBiduality σ τ)
    (ARsigma : σ.FiniteARTranslationData)
    (ARtau : τ.FiniteARTranslationData) :
    Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthDeepAnchor
          σ ARsigma) =
      Fintype.card (MirrorResidualCell τ ARtau) :=
  Fintype.card_congr
    ((FiniteARTranslationData.hookM6DeepAnchorEquivDeepStratumSubtype
      σ ARsigma).trans
      (D.deepResidualEquivMirror (K := K) σ τ ARsigma ARtau))

/-- The surviving-outer-corner balance is aligned invariance of one
same-side quantity: mirror residual cell + unused `M2` + unused `M3` +
reverse-last. -/
theorem intrinsicSurvivingOuterCornerReversalBalance_iff_mirrorInvariance
    (D : AlignedBiduality σ τ) :
    IntrinsicSurvivingOuterCornerReversalBalance
        (k := K) (R := R) (S := S) σ τ ↔
      Fintype.card
            (MirrorResidualCell τ
              (τ.finiteDimensionalARTranslationData K S)) +
          Fintype.card
            (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
              (K := K) τ (τ.finiteDimensionalARTranslationData K S)) +
          Fintype.card
            (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
              (K := K) τ (τ.finiteDimensionalARTranslationData K S)) +
          Fintype.card
            ((τ.finiteDimensionalARTranslationData K S).BoundaryM6ReverseLastPair
              τ) =
        Fintype.card
              (MirrorResidualCell σ
                (σ.finiteDimensionalARTranslationData K R)) +
            Fintype.card
              (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
                (K := K) σ (σ.finiteDimensionalARTranslationData K R)) +
            Fintype.card
              (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
                (K := K) σ (σ.finiteDimensionalARTranslationData K R)) +
            Fintype.card
              ((σ.finiteDimensionalARTranslationData K R).BoundaryM6ReverseLastPair
                σ) := by
  unfold IntrinsicSurvivingOuterCornerReversalBalance
  dsimp only []
  rw [D.deepAnchor_card_eq_mirror (K := K) σ τ
      (σ.finiteDimensionalARTranslationData K R)
      (τ.finiteDimensionalARTranslationData K S),
    (D.swap σ τ).deepAnchor_card_eq_mirror (K := K) τ σ
      (τ.finiteDimensionalARTranslationData K S)
      (σ.finiteDimensionalARTranslationData K R)]

/-- Conditional closure of the paper's colevel-four balance: aligned
invariance of the same-side mirror quantity discharges the terminal
crossed obligation. -/
theorem intrinsicOuterLocalStrataReversalBalance_of_mirrorInvariance
    (D : AlignedBiduality σ τ)
    (h : Fintype.card
            (MirrorResidualCell τ
              (τ.finiteDimensionalARTranslationData K S)) +
          Fintype.card
            (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
              (K := K) τ (τ.finiteDimensionalARTranslationData K S)) +
          Fintype.card
            (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
              (K := K) τ (τ.finiteDimensionalARTranslationData K S)) +
          Fintype.card
            ((τ.finiteDimensionalARTranslationData K S).BoundaryM6ReverseLastPair
              τ) =
        Fintype.card
              (MirrorResidualCell σ
                (σ.finiteDimensionalARTranslationData K R)) +
            Fintype.card
              (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
                (K := K) σ (σ.finiteDimensionalARTranslationData K R)) +
            Fintype.card
              (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
                (K := K) σ (σ.finiteDimensionalARTranslationData K R)) +
            Fintype.card
              ((σ.finiteDimensionalARTranslationData K R).BoundaryM6ReverseLastPair
                σ)) :
    IntrinsicOuterLocalStrataReversalBalance
      (k := K) (R := R) (S := S) σ τ := by
  rw [← intrinsicOuterLocalIndexRemainderReversalBalance_iff_localStrata
      σ τ D,
    ← intrinsicOuterStatusRemainderReversalBalance_iff_localIndexRemainder
      σ τ D,
    ← intrinsicOuterTransportRemainderReversalBalance_iff_statusRemainder
      σ τ,
    ← intrinsicSurvivingOuterCornerReversalBalance_iff_outerTransportRemainder
      σ τ D,
    D.intrinsicSurvivingOuterCornerReversalBalance_iff_mirrorInvariance
      (K := K) σ τ]
  exact h

end AlignedBiduality

end OpConjecture.IndecomposableSkeleton
