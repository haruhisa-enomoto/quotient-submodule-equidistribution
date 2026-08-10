import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexStripReversal
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexFixedStripParametrization
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexReversePacketTransport
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexDiagonalCandidateReversal
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexFixedReturnReversal
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexChannelTrimComplements
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexOuterEndpointTwoSourceTransport
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexOuterLocalBoundaryIndex
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexDiagonalM4DualCuts

/-!
# Exact reduction of the signed four-vertex strip

The hook-channel decompositions and the wall-term reversal reduce the
remaining strip identity to one subtraction-free equality among the four
signed channels and the row-`T`/double-hook corrections.  This file records
that exact interface and feeds it, together with the completed fixed-strip
equality, into the actual colevel-four packet balance.
-/

set_option autoImplicit false
noncomputable section

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {k R S : Type u} [Field k] [IsAlgClosed k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

/-- The raw signed strip identity before return arrows are removed from
the positive `M5` channel.  This is the direct numerical output expected
from the remaining trimmed-boundary image/complement classification. -/
def PreliminaryHookChannelReversalBalance : Prop :=
  Fintype.card
        ((σ.finiteDimensionalARTranslationData k R).HookM5Preliminary σ) +
      Fintype.card
        ((σ.finiteDimensionalARTranslationData k R).HookM6Channel σ) +
    Fintype.card
        ((τ.finiteDimensionalARTranslationData k S).HookWallBadU τ) +
      Fintype.card
        ((τ.finiteDimensionalARTranslationData k S).HookWallBadBUnrestricted
          τ) =
  Fintype.card
        ((τ.finiteDimensionalARTranslationData k S).HookM5Preliminary τ) +
      Fintype.card
        ((τ.finiteDimensionalARTranslationData k S).HookM6Channel τ) +
    Fintype.card
        ((σ.finiteDimensionalARTranslationData k R).HookWallBadU σ) +
      Fintype.card
        ((σ.finiteDimensionalARTranslationData k R).HookWallBadBUnrestricted
          σ)

/-- The terms discarded by trimming the four preliminary hook channels
satisfy the same crossed reversal balance as the retained terms. -/
def ChannelTrimComplementReversalBalance : Prop :=
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.NonInteriorChannel
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.NonInteriorChannel
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.NonInteriorChannel τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.NonInteriorChannel
          τ ARtau) =
    Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.NonInteriorChannel
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.NonInteriorChannel τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.NonInteriorChannel
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.NonInteriorChannel
          σ ARsigma)

/-- Endpoint-normalized form of the four discarded-channel equation. -/
def ChannelOuterEndpointReversalBalance : Prop :=
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.InjectiveMiddleEndpoint
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.InjectiveFourthEndpoint
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.InjectiveEndpoint
          τ ARtau) =
    Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.InjectiveMiddleEndpoint
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.InjectiveFourthEndpoint
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.InjectiveEndpoint
          σ ARsigma)

/-- The exact endpoint remainder left by the global square-shift proof.
The terminal/reverse-last defect of the trimmed boundary and the discarded
outer-channel defect are kept in one equation, as in the manuscript. -/
def EndpointRemainderReversalBalance : Prop :=
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  Fintype.card
        (ARsigma.InteriorTerminalFirstNotSourceCommonTargetPair σ) +
      Fintype.card (ARtau.BoundaryM6ReverseLastPair τ) +
      Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.InjectiveMiddleEndpoint
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.InjectiveFourthEndpoint
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.InjectiveEndpoint
          τ ARtau) =
    Fintype.card
        (ARtau.InteriorTerminalFirstNotSourceCommonTargetPair τ) +
      Fintype.card (ARsigma.BoundaryM6ReverseLastPair σ) +
      Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.InjectiveMiddleEndpoint
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.InjectiveFourthEndpoint
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.InjectiveEndpoint
          σ ARsigma)

/-- Endpoint remainder after cancelling the exact projective-first
outer-`M5`/noninjective-first outer-`M3` overlap. -/
def ReducedEndpointRemainderReversalBalance : Prop :=
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  Fintype.card
        (ARsigma.InteriorTerminalFirstNotSourceCommonTargetPair σ) +
      Fintype.card (ARtau.BoundaryM6ReverseLastPair τ) +
      Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.InjectiveMiddleNoProjectiveFirst
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.InjectiveFourthEndpoint
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.InjectiveEndpointFirstInjective
          τ ARtau) =
    Fintype.card
        (ARtau.InteriorTerminalFirstNotSourceCommonTargetPair τ) +
      Fintype.card (ARsigma.BoundaryM6ReverseLastPair σ) +
      Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.InjectiveMiddleNoProjectiveFirst
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.InjectiveFourthEndpoint
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.InjectiveEndpointFirstInjective
          σ ARsigma)

/-- Endpoint remainder after also cancelling the two exact outer `M6`
overlap images.  The only surviving `M6` terms have deep anchors, while
the negative wall terms are the unused `M2` and injective-first `M3`
occurrence complements. -/
def CornerReducedEndpointRemainderReversalBalance : Prop :=
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  Fintype.card
        (ARsigma.InteriorTerminalFirstNotSourceCommonTargetPair σ) +
      Fintype.card (ARtau.BoundaryM6ReverseLastPair τ) +
      Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.InjectiveMiddleNoProjectiveFirst
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthDeepAnchor
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
          (K := k) τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
          (K := k) τ ARtau) =
    Fintype.card
        (ARtau.InteriorTerminalFirstNotSourceCommonTargetPair τ) +
      Fintype.card (ARsigma.BoundaryM6ReverseLastPair σ) +
      Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.InjectiveMiddleNoProjectiveFirst
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthDeepAnchor
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
          (K := k) σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
          (K := k) σ ARsigma)

/-- Endpoint remainder after the same-chain diagonal image is cancelled.
The reverse-last terms have disappeared; the opposite residual term is the
literal different-chain part of the noninjective first source boundary. -/
def DiagonalComplementEndpointRemainderReversalBalance : Prop :=
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  Fintype.card
        (ARsigma.InteriorTerminalFirstNotSourceCommonTargetPair σ) +
      Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.InjectiveMiddleNoProjectiveFirst
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InteriorChannel σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthDeepAnchor
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
          (K := k) τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
          (K := k) τ ARtau) +
      Fintype.card
        (ARtau.LongArrowChainFirstDiagonalFirstBoundaryComplement τ) =
    Fintype.card
        (ARtau.InteriorTerminalFirstNotSourceCommonTargetPair τ) +
      Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.InjectiveMiddleNoProjectiveFirst
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InteriorChannel τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthDeepAnchor
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
          (K := k) σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
          (K := k) σ ARsigma) +
      Fintype.card
        (ARsigma.LongArrowChainFirstDiagonalFirstBoundaryComplement σ)

/-- Endpoint remainder after the diagonal complement has been split into
its intrinsic different-orbit part and the aligned length-three same-orbit
part has been cancelled.  This is the exact interface to the manuscript's
two-different-chain square shift. -/
def IntrinsicDifferentOrbitEndpointRemainderReversalBalance : Prop :=
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  Fintype.card
        (ARsigma.InteriorTerminalFirstNotSourceCommonTargetPair σ) +
      Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.InjectiveMiddleNoProjectiveFirst
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InteriorChannel σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthDeepAnchor
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
          (K := k) τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
          (K := k) τ ARtau) +
      Fintype.card
        (ARtau.DifferentOrbitFirstSourceNoninjectiveTargetPair τ) =
    Fintype.card
        (ARtau.InteriorTerminalFirstNotSourceCommonTargetPair τ) +
      Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.InjectiveMiddleNoProjectiveFirst
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InteriorChannel τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthDeepAnchor
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
          (K := k) σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
          (K := k) σ ARsigma) +
      Fintype.card
        (ARsigma.DifferentOrbitFirstSourceNoninjectiveTargetPair σ)

/-- Final corner form of the two-different-chain endpoint transport.  The
terminal/outer-`M5` pair and the same-chain diagonal channel have already
cancelled; only deep outer `M6`, the unused outer `M2`/`M3` complements,
and the reverse-last exception remain. -/
def IntrinsicSurvivingOuterCornerReversalBalance : Prop :=
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthDeepAnchor
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
          (K := k) τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
          (K := k) τ ARtau) +
      Fintype.card (ARtau.BoundaryM6ReverseLastPair τ) =
    Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthDeepAnchor
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
          (K := k) σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
          (K := k) σ ARsigma) +
      Fintype.card (ARsigma.BoundaryM6ReverseLastPair σ)

/-- The final outer corner after cancelling the injective-common-target
part of outer `M2` against the translated-projective injective-second
outer `M3` stratum on the opposite skeleton.  The unused `M2` term and
that `M3` subcorner no longer occur. -/
def IntrinsicOuterTransportRemainderReversalBalance : Prop :=
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthDeepAnchor
          σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthProjectiveAnchor
          σ ARsigma) +
      Fintype.card
        (ARtau.FirstPISecondInteriorM6Complement (K := k) τ) +
      Fintype.card
        (ARtau.FirstPISecondProjectiveNoninjectiveTargetNoninjectiveOuterPair
          τ) +
      Fintype.card (ARtau.BoundaryM6ReverseLastPair τ) =
    Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthDeepAnchor
          τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthProjectiveAnchor
          τ ARtau) +
      Fintype.card
        (ARsigma.FirstPISecondInteriorM6Complement (K := k) σ) +
      Fintype.card
        (ARsigma.FirstPISecondProjectiveNoninjectiveTargetNoninjectiveOuterPair
          σ) +
      Fintype.card (ARsigma.BoundaryM6ReverseLastPair σ)

/-- The same final corner after restoring the exact common
second-boundary `M6` image on both sides.  Projective-anchor and deep `M6`
recombine into the full outer `M6` endpoint, while the interior `M3`
complement recombines into the full intrinsic two-source stratum. -/
def IntrinsicOuterStatusRemainderReversalBalance : Prop :=
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
          σ ARsigma) +
      Fintype.card
        (ARtau.FirstPISecondInteriorTwoSourceOuterPair τ) +
      Fintype.card
        (ARtau.FirstPISecondProjectiveNoninjectiveTargetNoninjectiveOuterPair
          τ) +
      Fintype.card (ARtau.BoundaryM6ReverseLastPair τ) =
    Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
          τ ARtau) +
      Fintype.card
        (ARsigma.FirstPISecondInteriorTwoSourceOuterPair σ) +
      Fintype.card
        (ARsigma.FirstPISecondProjectiveNoninjectiveTargetNoninjectiveOuterPair
          σ) +
      Fintype.card (ARsigma.BoundaryM6ReverseLastPair σ)

/-- Endpoint-coordinate form of the full-status remainder.  Aligned outer
transport replaces the opposite two-source stratum by the local
nonprojective/noninjective-second stratum with injective common target. -/
def IntrinsicOuterLocalIndexRemainderReversalBalance : Prop :=
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
          σ ARsigma) +
      Fintype.card
        (ARsigma.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
          σ) +
      Fintype.card
        (ARtau.FirstPISecondProjectiveNoninjectiveTargetNoninjectiveOuterPair
          τ) +
      Fintype.card (ARtau.BoundaryM6ReverseLastPair τ) =
    Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
          τ ARtau) +
      Fintype.card
        (ARtau.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
          τ) +
      Fintype.card
        (ARsigma.FirstPISecondProjectiveNoninjectiveTargetNoninjectiveOuterPair
          σ) +
      Fintype.card (ARsigma.BoundaryM6ReverseLastPair σ)

/-- Fully local intrinsic-stratum form of the outer endpoint index.  The
noninjective-target outer `M2` residue has also been transported to the
local injective-second/translated-target-nonprojective stratum, leaving
only the reverse-last exceptions on the crossed sides. -/
def IntrinsicOuterLocalStrataReversalBalance : Prop :=
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
          σ ARsigma) +
      Fintype.card
        (ARsigma.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
          σ) +
      Fintype.card
        (ARsigma.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair
          σ) +
      Fintype.card (ARtau.BoundaryM6ReverseLastPair τ) =
    Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
          τ ARtau) +
      Fintype.card
        (ARtau.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
          τ) +
      Fintype.card
        (ARtau.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair
          τ) +
      Fintype.card (ARsigma.BoundaryM6ReverseLastPair σ)

omit [IsAlgClosed k] in
include k in
/-- Exact full-boundary-complement coordinate form of the final crossed
outer balance. -/
theorem intrinsicOuterLocalStrataReversalBalance_iff_crossedBoundaryFamilies
    (D : AlignedBiduality σ τ) :
    IntrinsicOuterLocalStrataReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      let ARsigma := σ.finiteDimensionalARTranslationData k R
      let ARtau := τ.finiteDimensionalARTranslationData k S
      Fintype.card (ARsigma.OuterLocalStrataFamily σ) +
          Fintype.card
            (ARtau.TargetBoundaryComplementReverseLastFamily τ) =
        Fintype.card (ARtau.OuterLocalStrataFamily τ) +
          Fintype.card
            (ARsigma.TargetBoundaryComplementReverseLastFamily σ) := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have h := D.outerLocalStrata_crossedReverseLast_iff_crossedBoundaryFamilies
    (K := k) σ τ ARsigma ARtau
  unfold IntrinsicOuterLocalStrataReversalBalance
  dsimp only [ARsigma, ARtau] at h ⊢
  exact h

omit [IsAlgClosed k] in
include k in
/-- Exact literal-source-boundary coordinate form of the final crossed
outer balance.  In this form the raw complement and reverse-last exception
belong to one common boundary coordinate. -/
theorem intrinsicOuterLocalStrataReversalBalance_iff_crossedSourceBoundaryFamilies
    (D : AlignedBiduality σ τ) :
    IntrinsicOuterLocalStrataReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      let ARsigma := σ.finiteDimensionalARTranslationData k R
      let ARtau := τ.finiteDimensionalARTranslationData k S
      Fintype.card (ARsigma.OuterLocalStrataFamily σ) +
          Fintype.card
            (ARtau.SourceBoundaryComplementReverseLastFamily τ) =
        Fintype.card (ARtau.OuterLocalStrataFamily τ) +
          Fintype.card
            (ARsigma.SourceBoundaryComplementReverseLastFamily σ) := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have h :=
    D.outerLocalStrata_crossedReverseLast_iff_crossedSourceBoundaryFamilies
      (K := k) σ τ ARsigma ARtau
  unfold IntrinsicOuterLocalStrataReversalBalance
  dsimp only [ARsigma, ARtau] at h ⊢
  exact h

omit [IsAlgClosed k] in
include k in
/-- Exact expanded source-endpoint form of the final crossed outer balance.
The boundary side is now the tagged sum of projective-target occurrences,
trimmed literal-source occurrences, and reverse-last exceptions. -/
theorem intrinsicOuterLocalStrataReversalBalance_iff_crossedSourceEndpointFamilies
    (D : AlignedBiduality σ τ) :
    IntrinsicOuterLocalStrataReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      let ARsigma := σ.finiteDimensionalARTranslationData k R
      let ARtau := τ.finiteDimensionalARTranslationData k S
      Fintype.card (ARsigma.OuterLocalStrataFamily σ) +
          Fintype.card
            (ARtau.SourceBoundaryEndpointReverseLastFamily τ) =
        Fintype.card (ARtau.OuterLocalStrataFamily τ) +
          Fintype.card
            (ARsigma.SourceBoundaryEndpointReverseLastFamily σ) := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have h :=
    D.outerLocalStrata_crossedReverseLast_iff_crossedSourceEndpointFamilies
      (K := k) σ τ ARsigma ARtau
  unfold IntrinsicOuterLocalStrataReversalBalance
  dsimp only [ARsigma, ARtau] at h ⊢
  exact h

omit [IsAlgClosed k] in
include k in
/-- The remaining crossed outer balance follows from the exact local
full-boundary classification on the two skeletons. -/
theorem intrinsicOuterLocalStrataReversalBalance_of_localBoundaryIndices
    (D : AlignedBiduality σ τ)
    (hσ :
      (σ.finiteDimensionalARTranslationData k R).OuterLocalBoundaryIndex σ)
    (hτ :
      (τ.finiteDimensionalARTranslationData k S).OuterLocalBoundaryIndex τ) :
    IntrinsicOuterLocalStrataReversalBalance
      (k := k) (R := R) (S := S) σ τ := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have h := D.outerLocalStrata_add_crossedReverseLast_card_eq
    (K := k) σ τ ARsigma ARtau hσ hτ
  unfold IntrinsicOuterLocalStrataReversalBalance
  dsimp only [ARsigma, ARtau] at h ⊢
  exact h

omit [IsAlgClosed k] in
include k in
/-- The surviving-outer corner is equivalent to the smaller remainder
obtained from the exact aligned outer-endpoint transport. -/
theorem intrinsicSurvivingOuterCornerReversalBalance_iff_outerTransportRemainder
    (D : AlignedBiduality σ τ) :
    IntrinsicSurvivingOuterCornerReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      IntrinsicOuterTransportRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have hm3Sigma :=
    ARsigma.hookWallBadBM6SecondBoundaryComplement_card_eq_intrinsic
      (K := k) σ
  have hm3Tau :=
    ARtau.hookWallBadBM6SecondBoundaryComplement_card_eq_intrinsic
      (K := k) τ
  have hcrossSigma :=
    D.hookM6ProjectiveAnchor_add_unusedM2_card_eq_crossedM3_add_remainder
      (K := k) σ τ ARsigma ARtau
  have hcrossTau :=
    D.swap.hookM6ProjectiveAnchor_add_unusedM2_card_eq_crossedM3_add_remainder
      (K := k) τ σ ARtau ARsigma
  unfold IntrinsicSurvivingOuterCornerReversalBalance
  unfold IntrinsicOuterTransportRemainderReversalBalance
  dsimp only [ARsigma, ARtau] at *
  constructor <;> intro h <;> omega

omit [IsAlgClosed k] in
include k in
/-- Restoring the shared second-boundary overlap on both sides turns the
outer-transport remainder into the cleaner full-status equation. -/
theorem intrinsicOuterTransportRemainderReversalBalance_iff_statusRemainder :
    IntrinsicOuterTransportRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      IntrinsicOuterStatusRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have hM6Sigma := Fintype.card_congr
    (FiniteARTranslationData.hookM6InjectiveFourthEquivProjectiveSumNonprojectiveAnchor
      σ ARsigma)
  have hM6Tau := Fintype.card_congr
    (FiniteARTranslationData.hookM6InjectiveFourthEquivProjectiveSumNonprojectiveAnchor
      τ ARtau)
  have hNonprojectiveSigma := Fintype.card_congr
    (FiniteARTranslationData.hookM6NonprojectiveAnchorEquivSecondBoundarySumDeep
      σ ARsigma)
  have hNonprojectiveTau := Fintype.card_congr
    (FiniteARTranslationData.hookM6NonprojectiveAnchorEquivSecondBoundarySumDeep
      τ ARtau)
  have hTwoSourceSigma :=
    ARsigma.firstPISecondInteriorTwoSource_card_eq_m6SecondBoundary_add_complement
      (K := k) σ
  have hTwoSourceTau :=
    ARtau.firstPISecondInteriorTwoSource_card_eq_m6SecondBoundary_add_complement
      (K := k) τ
  simp only [Fintype.card_sum] at hM6Sigma hM6Tau hNonprojectiveSigma hNonprojectiveTau
  unfold IntrinsicOuterTransportRemainderReversalBalance
  unfold IntrinsicOuterStatusRemainderReversalBalance
  dsimp only [ARsigma, ARtau] at *
  constructor <;> intro h <;> omega

omit [IsAlgClosed k] in
/-- The full-status remainder is exactly its local endpoint-index form
under the pointwise aligned outer transport. -/
theorem intrinsicOuterStatusRemainderReversalBalance_iff_localIndexRemainder
    (D : AlignedBiduality σ τ) :
    IntrinsicOuterStatusRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      IntrinsicOuterLocalIndexRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have hSigma := Fintype.card_congr
    (D.firstPISecondInteriorTwoSourceEquivTargetInjective
      σ τ ARsigma ARtau)
  have hTau := Fintype.card_congr
    (D.swap.firstPISecondInteriorTwoSourceEquivTargetInjective
      τ σ ARtau ARsigma)
  unfold IntrinsicOuterStatusRemainderReversalBalance
  unfold IntrinsicOuterLocalIndexRemainderReversalBalance
  dsimp only [ARsigma, ARtau] at *
  constructor <;> intro h <;> omega

omit [IsAlgClosed k] in
/-- Transporting the last noninjective-target outer `M2` residue makes all
non-exceptional outer strata local to their own skeleton. -/
theorem intrinsicOuterLocalIndexRemainderReversalBalance_iff_localStrata
    (D : AlignedBiduality σ τ) :
    IntrinsicOuterLocalIndexRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      IntrinsicOuterLocalStrataReversalBalance
        (k := k) (R := R) (S := S) σ τ := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have hSigma := Fintype.card_congr
    (D.firstPISecondProjectiveNoninjectiveTargetNoninjectiveEquivTranslatedTargetNonprojective
      σ τ ARsigma ARtau)
  have hTau := Fintype.card_congr
    (D.swap.firstPISecondProjectiveNoninjectiveTargetNoninjectiveEquivTranslatedTargetNonprojective
      τ σ ARtau ARsigma)
  unfold IntrinsicOuterLocalIndexRemainderReversalBalance
  unfold IntrinsicOuterLocalStrataReversalBalance
  dsimp only [ARsigma, ARtau] at *
  constructor <;> intro h <;> omega

omit [IsAlgClosed k] in
include k in
/-- The intrinsic endpoint remainder is exactly equivalent to its final
surviving-outer corner.  The proof uses the pointwise crossed
terminal/`M5` equivalence and the already compiled crossed diagonal-channel
balance, so no independent endpoint term remains hidden. -/
theorem intrinsicDifferentOrbitEndpointRemainderReversalBalance_iff_survivingOuterCorner
    (D : AlignedBiduality σ τ) :
    IntrinsicDifferentOrbitEndpointRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      IntrinsicSurvivingOuterCornerReversalBalance
        (k := k) (R := R) (S := S) σ τ := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have hterminalSigma :=
    D.terminalFirstNotSource_card_eq_m5Image
      (K := k) σ τ ARsigma ARtau
  have hterminalTau :=
    D.swap.terminalFirstNotSource_card_eq_m5Image
      (K := k) τ σ ARtau ARsigma
  have hm5Sigma :=
    ARsigma.hookM5NoProjectiveFirst_card_eq_differentOrbitImage
      (K := k) σ
  have hm5Tau :=
    ARtau.hookM5NoProjectiveFirst_card_eq_differentOrbitImage
      (K := k) τ
  have hdiagonal :=
    FiniteARTranslationData.longArrowChainFirstDiagonalChannel_crossedDifferentOrbitFirstBoundary_card_eq
      (K := k) σ τ ARsigma ARtau D
  unfold IntrinsicDifferentOrbitEndpointRemainderReversalBalance
  unfold IntrinsicSurvivingOuterCornerReversalBalance
  dsimp only [ARsigma, ARtau] at *
  constructor <;> intro h <;> omega

omit [IsAlgClosed k] in
include k in
/-- Cancelling the occurrence-preserving outer `M5`/`M3` overlap is exact:
the original combined endpoint remainder is equivalent to its reduced
four-family form. -/
theorem endpointRemainderReversalBalance_iff_reduced :
    EndpointRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      ReducedEndpointRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have hsigma :=
    ARsigma.hookM5Outer_add_hookWallBadBFirstInjective_card_eq
      (K := k) σ
  have htau :=
    ARtau.hookM5Outer_add_hookWallBadBFirstInjective_card_eq
      (K := k) τ
  unfold EndpointRemainderReversalBalance
  unfold ReducedEndpointRemainderReversalBalance
  dsimp only [ARsigma, ARtau] at *
  omega

omit [IsAlgClosed k] in
include k in
/-- Cancelling the occurrence-preserving `M6`/`M2` and `M6`/`M3`
overlaps is exact: the four-family endpoint equation is equivalent to the
corner-reduced deep-anchor/complement equation. -/
theorem reducedEndpointRemainderReversalBalance_iff_cornerReduced :
    ReducedEndpointRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      CornerReducedEndpointRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have hsigma := ARsigma.hookM6_add_outer_overlap_complements_card_eq
    (K := k) σ
  have htau := ARtau.hookM6_add_outer_overlap_complements_card_eq
    (K := k) τ
  unfold ReducedEndpointRemainderReversalBalance
  unfold CornerReducedEndpointRemainderReversalBalance
  dsimp only [ARsigma, ARtau] at *
  omega

omit [IsAlgClosed k] in
include k in
/-- Cancelling the aligned same-chain diagonal image is exact: the
corner-reduced six-family equation is equivalent to the endpoint equation
in literal different-chain boundary coordinates. -/
theorem cornerReducedEndpointRemainderReversalBalance_iff_diagonalComplement
    (D : AlignedBiduality σ τ) :
    CornerReducedEndpointRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      DiagonalComplementEndpointRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have hdiagonal :=
    FiniteARTranslationData.longArrowChainFirstDiagonalChannel_crossedFirstBoundaryComplement_card_eq
      (K := k) σ τ ARsigma ARtau D
  unfold CornerReducedEndpointRemainderReversalBalance
  unfold DiagonalComplementEndpointRemainderReversalBalance
  dsimp only [ARsigma, ARtau] at *
  constructor <;> intro h <;> omega

omit [IsAlgClosed k] in
include k in
/-- Cancelling the exact aligned length-three same-orbit remainder turns
the diagonal-complement equation into its intrinsic different-orbit form. -/
theorem diagonalComplementEndpointRemainderReversalBalance_iff_intrinsicDifferentOrbit
    (D : AlignedBiduality σ τ) :
    DiagonalComplementEndpointRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      IntrinsicDifferentOrbitEndpointRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have hsplitσ :=
    ARsigma.longArrowChainFirstDiagonalFirstBoundaryComplement_card_eq_differentOrbit_add_sameOrbit
      σ
  have hsplitτ :=
    ARtau.longArrowChainFirstDiagonalFirstBoundaryComplement_card_eq_differentOrbit_add_sameOrbit
      τ
  have hshort :=
    FiniteARTranslationData.longArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder_card_eq
      σ τ ARsigma ARtau D
  unfold DiagonalComplementEndpointRemainderReversalBalance
  unfold IntrinsicDifferentOrbitEndpointRemainderReversalBalance
  dsimp only [ARsigma, ARtau] at *
  constructor <;> intro h <;> omega

omit [IsAlgClosed k] in
/-- The endpoint descriptions of the four discarded families are exact,
so their normalized reversal equation proves the trimming-complement
equation. -/
theorem channelTrimComplementReversalBalance_of_outerEndpoint
    (h : ChannelOuterEndpointReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    ChannelTrimComplementReversalBalance
      (k := k) (R := R) (S := S) σ τ := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have h5sigma := Fintype.card_congr
    (ARsigma.hookM5PreliminaryNonInteriorEquivInjectiveMiddleEndpoint σ)
  have h5tau := Fintype.card_congr
    (ARtau.hookM5PreliminaryNonInteriorEquivInjectiveMiddleEndpoint τ)
  have h6sigma := Fintype.card_congr
    (ARsigma.hookM6NonInteriorEquivInjectiveFourthEndpoint σ)
  have h6tau := Fintype.card_congr
    (ARtau.hookM6NonInteriorEquivInjectiveFourthEndpoint τ)
  have h2sigma := Fintype.card_congr
    (ARsigma.hookWallBadUNonInteriorEquivInjectiveFourthEndpoint σ)
  have h2tau := Fintype.card_congr
    (ARtau.hookWallBadUNonInteriorEquivInjectiveFourthEndpoint τ)
  have h3sigma := Fintype.card_congr
    (ARsigma.hookWallBadBUnrestrictedNonInteriorEquivInjectiveEndpoint σ)
  have h3tau := Fintype.card_congr
    (ARtau.hookWallBadBUnrestrictedNonInteriorEquivInjectiveEndpoint τ)
  unfold ChannelOuterEndpointReversalBalance at h
  unfold ChannelTrimComplementReversalBalance
  dsimp only [ARsigma, ARtau] at *
  omega

omit [IsAlgClosed k] in
/-- The trimmed channel identity and the identity for exactly its four
discarded complements reassemble the full preliminary channel balance. -/
theorem preliminaryHookChannelReversalBalance_of_trimmed_and_complements
    (htrim : TrimmedPreliminaryHookChannelReversalBalance
      (k := k) (R := R) (S := S) σ τ)
    (hcomp : ChannelTrimComplementReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    PreliminaryHookChannelReversalBalance
      (k := k) (R := R) (S := S) σ τ := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have hm5sigma :=
    ARsigma.hookM5Preliminary_card_eq_interior_add_nonInterior σ
  have hm5tau :=
    ARtau.hookM5Preliminary_card_eq_interior_add_nonInterior τ
  have hm6sigma :=
    ARsigma.hookM6Channel_card_eq_interior_add_nonInterior σ
  have hm6tau :=
    ARtau.hookM6Channel_card_eq_interior_add_nonInterior τ
  have hwallsigma :=
    ARsigma.hookWallFull_card_eq_interior_add_nonInterior σ
  have hwalltau :=
    ARtau.hookWallFull_card_eq_interior_add_nonInterior τ
  unfold TrimmedPreliminaryHookChannelReversalBalance at htrim
  unfold ChannelTrimComplementReversalBalance at hcomp
  unfold PreliminaryHookChannelReversalBalance
  dsimp only [ARsigma, ARtau] at *
  simp only [Fintype.card_sum] at htrim
  omega

omit [IsAlgClosed k] in
include k in
/-- The manuscript's single combined endpoint remainder is sufficient for
the full preliminary hook-channel balance.  No separate invariance of its
trimmed and outer summands is required. -/
theorem preliminaryHookChannelReversalBalance_of_endpointRemainder
    (D : AlignedBiduality σ τ)
    (h : EndpointRemainderReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    PreliminaryHookChannelReversalBalance
      (k := k) (R := R) (S := S) σ τ := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have hterminalSigma :=
    ARsigma.interiorLiteralSourceTerminalCommonTarget_card_eq_injective_add_firstNotSource
      σ
  have hterminalTau :=
    ARtau.interiorLiteralSourceTerminalCommonTarget_card_eq_injective_add_firstNotSource
      τ
  have hliteral :=
    interiorLiteralSourceCommonSource_card_eq_secondOnly_add_dualTerminal
      (k := k) σ τ D
  have hprojective := FiniteARTranslationData.projectiveStrip_card_eq
    (K := k) σ τ ARsigma ARtau D
  have hlocalSigma :=
    ARsigma.interiorSourceBoundary_clean_local_channel_card_identity
      (k := k) σ
  have hlocalTau :=
    ARtau.interiorSourceBoundary_clean_local_channel_card_identity
      (k := k) τ
  have hincidence :=
    ARsigma.interiorSourceBoundary_target_add_literalSource_card_eq σ
  have hduality :=
    D.interiorSourceBoundaryCommonTarget_card_eq_sourceBoundaryCommonSource
      σ τ ARsigma ARtau
  have hm5Sigma :=
    ARsigma.hookM5Preliminary_card_eq_interior_add_nonInterior σ
  have hm5Tau :=
    ARtau.hookM5Preliminary_card_eq_interior_add_nonInterior τ
  have hm6Sigma :=
    ARsigma.hookM6Channel_card_eq_interior_add_nonInterior σ
  have hm6Tau :=
    ARtau.hookM6Channel_card_eq_interior_add_nonInterior τ
  have hwallSigma :=
    ARsigma.hookWallFull_card_eq_interior_add_nonInterior σ
  have hwallTau :=
    ARtau.hookWallFull_card_eq_interior_add_nonInterior τ
  have h5Sigma := Fintype.card_congr
    (ARsigma.hookM5PreliminaryNonInteriorEquivInjectiveMiddleEndpoint σ)
  have h5Tau := Fintype.card_congr
    (ARtau.hookM5PreliminaryNonInteriorEquivInjectiveMiddleEndpoint τ)
  have h6Sigma := Fintype.card_congr
    (ARsigma.hookM6NonInteriorEquivInjectiveFourthEndpoint σ)
  have h6Tau := Fintype.card_congr
    (ARtau.hookM6NonInteriorEquivInjectiveFourthEndpoint τ)
  have h2Sigma := Fintype.card_congr
    (ARsigma.hookWallBadUNonInteriorEquivInjectiveFourthEndpoint σ)
  have h2Tau := Fintype.card_congr
    (ARtau.hookWallBadUNonInteriorEquivInjectiveFourthEndpoint τ)
  have h3Sigma := Fintype.card_congr
    (ARsigma.hookWallBadBUnrestrictedNonInteriorEquivInjectiveEndpoint σ)
  have h3Tau := Fintype.card_congr
    (ARtau.hookWallBadBUnrestrictedNonInteriorEquivInjectiveEndpoint τ)
  unfold EndpointRemainderReversalBalance at h
  unfold PreliminaryHookChannelReversalBalance
  dsimp only [ARsigma, ARtau] at *
  simp only [Fintype.card_sum] at *
  omega

omit [IsAlgClosed k] in
include k in
/-- Conversely, after all already-compiled local classifications and
duality transports, the preliminary balance forces the combined endpoint
remainder. -/
theorem endpointRemainderReversalBalance_of_preliminaryHookChannel
    (D : AlignedBiduality σ τ)
    (h : PreliminaryHookChannelReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    EndpointRemainderReversalBalance
      (k := k) (R := R) (S := S) σ τ := by
  let ARsigma := σ.finiteDimensionalARTranslationData k R
  let ARtau := τ.finiteDimensionalARTranslationData k S
  have hterminalSigma :=
    ARsigma.interiorLiteralSourceTerminalCommonTarget_card_eq_injective_add_firstNotSource
      σ
  have hterminalTau :=
    ARtau.interiorLiteralSourceTerminalCommonTarget_card_eq_injective_add_firstNotSource
      τ
  have hliteral :=
    interiorLiteralSourceCommonSource_card_eq_secondOnly_add_dualTerminal
      (k := k) σ τ D
  have hprojective := FiniteARTranslationData.projectiveStrip_card_eq
    (K := k) σ τ ARsigma ARtau D
  have hlocalSigma :=
    ARsigma.interiorSourceBoundary_clean_local_channel_card_identity
      (k := k) σ
  have hlocalTau :=
    ARtau.interiorSourceBoundary_clean_local_channel_card_identity
      (k := k) τ
  have hincidence :=
    ARsigma.interiorSourceBoundary_target_add_literalSource_card_eq σ
  have hduality :=
    D.interiorSourceBoundaryCommonTarget_card_eq_sourceBoundaryCommonSource
      σ τ ARsigma ARtau
  have hm5Sigma :=
    ARsigma.hookM5Preliminary_card_eq_interior_add_nonInterior σ
  have hm5Tau :=
    ARtau.hookM5Preliminary_card_eq_interior_add_nonInterior τ
  have hm6Sigma :=
    ARsigma.hookM6Channel_card_eq_interior_add_nonInterior σ
  have hm6Tau :=
    ARtau.hookM6Channel_card_eq_interior_add_nonInterior τ
  have hwallSigma :=
    ARsigma.hookWallFull_card_eq_interior_add_nonInterior σ
  have hwallTau :=
    ARtau.hookWallFull_card_eq_interior_add_nonInterior τ
  have h5Sigma := Fintype.card_congr
    (ARsigma.hookM5PreliminaryNonInteriorEquivInjectiveMiddleEndpoint σ)
  have h5Tau := Fintype.card_congr
    (ARtau.hookM5PreliminaryNonInteriorEquivInjectiveMiddleEndpoint τ)
  have h6Sigma := Fintype.card_congr
    (ARsigma.hookM6NonInteriorEquivInjectiveFourthEndpoint σ)
  have h6Tau := Fintype.card_congr
    (ARtau.hookM6NonInteriorEquivInjectiveFourthEndpoint τ)
  have h2Sigma := Fintype.card_congr
    (ARsigma.hookWallBadUNonInteriorEquivInjectiveFourthEndpoint σ)
  have h2Tau := Fintype.card_congr
    (ARtau.hookWallBadUNonInteriorEquivInjectiveFourthEndpoint τ)
  have h3Sigma := Fintype.card_congr
    (ARsigma.hookWallBadBUnrestrictedNonInteriorEquivInjectiveEndpoint σ)
  have h3Tau := Fintype.card_congr
    (ARtau.hookWallBadBUnrestrictedNonInteriorEquivInjectiveEndpoint τ)
  unfold PreliminaryHookChannelReversalBalance at h
  unfold EndpointRemainderReversalBalance
  dsimp only [ARsigma, ARtau] at *
  simp only [Fintype.card_sum] at *
  omega

omit [IsAlgClosed k] in
include k in
/-- The full preliminary signed-channel balance is exactly equivalent to
the one combined endpoint remainder. -/
theorem preliminaryHookChannelReversalBalance_iff_endpointRemainder
    (D : AlignedBiduality σ τ) :
    PreliminaryHookChannelReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      EndpointRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ :=
  ⟨endpointRemainderReversalBalance_of_preliminaryHookChannel
      (k := k) σ τ D,
    preliminaryHookChannelReversalBalance_of_endpointRemainder
      (k := k) σ τ D⟩

omit [IsAlgClosed k] in
include k in
/-- The full preliminary signed-channel balance is exactly equivalent to
the reduced endpoint remainder after the outer `M5`/`M3` overlap has been
cancelled. -/
theorem preliminaryHookChannelReversalBalance_iff_reducedEndpointRemainder
    (D : AlignedBiduality σ τ) :
    PreliminaryHookChannelReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      ReducedEndpointRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ :=
  (preliminaryHookChannelReversalBalance_iff_endpointRemainder
    (k := k) σ τ D).trans
      (endpointRemainderReversalBalance_iff_reduced
        (k := k) σ τ)

omit [IsAlgClosed k] in
include k in
/-- The full preliminary signed-channel balance is equivalently the
manuscript-organized endpoint equation after both outer-overlap and
same-chain diagonal cancellation. -/
theorem preliminaryHookChannelReversalBalance_iff_diagonalComplementRemainder
    (D : AlignedBiduality σ τ) :
    PreliminaryHookChannelReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      DiagonalComplementEndpointRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ :=
  (preliminaryHookChannelReversalBalance_iff_reducedEndpointRemainder
    (k := k) σ τ D).trans <|
      (reducedEndpointRemainderReversalBalance_iff_cornerReduced
        (k := k) (R := R) (S := S) σ τ).trans
        (cornerReducedEndpointRemainderReversalBalance_iff_diagonalComplement
          (k := k) σ τ D)

omit [IsAlgClosed k] in
include k in
/-- The preliminary signed-channel balance is exactly equivalent to the
endpoint equation whose boundary term is the intrinsic different-orbit
subtype and whose length-three same-orbit part has already cancelled. -/
theorem preliminaryHookChannelReversalBalance_iff_intrinsicDifferentOrbitRemainder
    (D : AlignedBiduality σ τ) :
    PreliminaryHookChannelReversalBalance
        (k := k) (R := R) (S := S) σ τ ↔
      IntrinsicDifferentOrbitEndpointRemainderReversalBalance
        (k := k) (R := R) (S := S) σ τ :=
  (preliminaryHookChannelReversalBalance_iff_diagonalComplementRemainder
    (k := k) σ τ D).trans
      (diagonalComplementEndpointRemainderReversalBalance_iff_intrinsicDifferentOrbit
        (k := k) σ τ D)

omit [IsAlgClosed k] in
include k in
/-- The stronger split endpoint hypotheses imply the exact combined
endpoint remainder. -/
theorem endpointRemainderReversalBalance_of_terminal_and_outer
    (hterminal : TrimmedTerminalReverseExceptionBalance
      (k := k) (R := R) (S := S) σ τ)
    (houter : ChannelOuterEndpointReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    EndpointRemainderReversalBalance
      (k := k) (R := R) (S := S) σ τ := by
  unfold TrimmedTerminalReverseExceptionBalance at hterminal
  unfold ChannelOuterEndpointReversalBalance at houter
  unfold EndpointRemainderReversalBalance
  omega

omit [IsAlgClosed k] in
include k in
/-- Separately balancing the trimmed-terminal and outer-channel endpoint
families gives a convenient stronger input for the full preliminary
hook-channel balance. -/
theorem preliminaryHookChannelReversalBalance_of_endpointBalances
    (D : AlignedBiduality σ τ)
    (hterminal : TrimmedTerminalReverseExceptionBalance
      (k := k) (R := R) (S := S) σ τ)
    (houter : ChannelOuterEndpointReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    PreliminaryHookChannelReversalBalance
      (k := k) (R := R) (S := S) σ τ := by
  apply preliminaryHookChannelReversalBalance_of_endpointRemainder
    (k := k) σ τ D
  exact endpointRemainderReversalBalance_of_terminal_and_outer
    (k := k) σ τ hterminal houter

/-- The sole remaining numerical content of signed strip reversal after
the raw hook-channel decompositions and wall equality have been removed.

The positive terms are `M₅,M₆`; the negative terms `M₂,M₃` cross to
the opposite side.  Row `T` and the double-hook correction have the signs
forced by `W-B+T`. -/
def SignedHookChannelReversalBalance : Prop :=
  Fintype.card
        ((σ.finiteDimensionalARTranslationData k R).HookM5Channel σ) +
          Fintype.card
            ((σ.finiteDimensionalARTranslationData k R).HookM6Channel σ) +
        Fintype.card
          ((τ.finiteDimensionalARTranslationData k S).HookWallBadU τ) +
      Fintype.card
        ((τ.finiteDimensionalARTranslationData k S).HookWallBadBUnrestricted τ) +
    Fintype.card (QuotientTrianglePacketFour (k := k) (R := R) σ) +
    Fintype.card (SubmoduleDoubleHookFour (k := k) (S := S) τ) =
  Fintype.card
        ((τ.finiteDimensionalARTranslationData k S).HookM5Channel τ) +
          Fintype.card
            ((τ.finiteDimensionalARTranslationData k S).HookM6Channel τ) +
        Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookWallBadU σ) +
      Fintype.card
        ((σ.finiteDimensionalARTranslationData k R).HookWallBadBUnrestricted σ) +
    Fintype.card (SubmoduleTrianglePacketFour (k := k) (S := S) τ) +
    Fintype.card (QuotientDoubleHookFour (k := k) (R := R) σ)

omit [IsAlgClosed k] in
/-- The two completed return-reversal theorems give the exact conversion
between preliminary and genuine `M5` counts.  Fixed returns cancel
directly; diagonal returns cancel after adjoining the double-hook term;
row-`T` returns are the triangle-packet term. -/
theorem hookM5Preliminary_reversal_correction
    (D : AlignedBiduality σ τ) :
    Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookM5Preliminary σ) +
        Fintype.card
          ((τ.finiteDimensionalARTranslationData k S).HookM5Channel τ) +
      Fintype.card (QuotientTrianglePacketFour (k := k) (R := S) τ) +
        Fintype.card (QuotientDoubleHookFour (k := k) (R := R) σ) =
    Fintype.card
          ((τ.finiteDimensionalARTranslationData k S).HookM5Preliminary τ) +
        Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookM5Channel σ) +
      Fintype.card (QuotientTrianglePacketFour (k := k) (R := R) σ) +
        Fintype.card (QuotientDoubleHookFour (k := k) (R := S) τ) := by
  let ARσ := σ.finiteDimensionalARTranslationData k R
  let ARτ := τ.finiteDimensionalARTranslationData k S
  have hpσ := FiniteARTranslationData.hookM5Preliminary_card_eq_channel_add_rejected
    σ ARσ
  have hpτ := FiniteARTranslationData.hookM5Preliminary_card_eq_channel_add_rejected
    τ ARτ
  have hrσ :=
    FiniteARTranslationData.hookM5Rejected_card_eq_fixedReturn_add_diagonalReturn_add_trianglePacket
      (k := k) (R := R) σ
  have hrτ :=
    FiniteARTranslationData.hookM5Rejected_card_eq_fixedReturn_add_diagonalReturn_add_trianglePacket
      (k := k) (R := S) τ
  have hfixed := FiniteARTranslationData.hookM5FixedReturn_card_eq
    (k := k) σ τ ARσ ARτ D
  have hdiagonal :=
    FiniteARTranslationData.diagonalReturn_add_doubleHook_card_eq
      (k := k) σ τ D
  dsimp only [ARσ, ARτ] at hpσ hpτ hfixed
  omega

omit [IsAlgClosed k] in
include k in
/-- Once the raw preliminary boundary balance is known, all return
corrections assemble automatically into the signed-channel identity. -/
theorem signedHookChannelReversalBalance_of_preliminary
    (D : AlignedBiduality σ τ)
    (h : PreliminaryHookChannelReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    SignedHookChannelReversalBalance
      (k := k) (R := R) (S := S) σ τ := by
  have hcorrection := hookM5Preliminary_reversal_correction
    (k := k) (R := R) (S := S) σ τ D
  unfold PreliminaryHookChannelReversalBalance at h
  unfold SignedHookChannelReversalBalance
  dsimp only [SubmoduleDoubleHookFour, SubmoduleTrianglePacketFour]
  omega

omit [IsAlgClosed k] in
include k in
/-- The combined endpoint remainder feeds through all compiled return
corrections to the genuine signed hook-channel balance. -/
theorem signedHookChannelReversalBalance_of_endpointRemainder
    (D : AlignedBiduality σ τ)
    (h : EndpointRemainderReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    SignedHookChannelReversalBalance
      (k := k) (R := R) (S := S) σ τ := by
  apply signedHookChannelReversalBalance_of_preliminary
    (k := k) σ τ D
  exact preliminaryHookChannelReversalBalance_of_endpointRemainder
    (k := k) σ τ D h

omit [IsAlgClosed k] in
include k in
/-- The reduced endpoint remainder feeds through all compiled return
corrections to the genuine signed hook-channel balance. -/
theorem signedHookChannelReversalBalance_of_reducedEndpointRemainder
    (D : AlignedBiduality σ τ)
    (h : ReducedEndpointRemainderReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    SignedHookChannelReversalBalance
      (k := k) (R := R) (S := S) σ τ := by
  apply signedHookChannelReversalBalance_of_endpointRemainder
    (k := k) σ τ D
  exact (endpointRemainderReversalBalance_iff_reduced
    (k := k) σ τ).2 h

omit [IsAlgClosed k] in
include k in
/-- The stronger pair of separately balanced endpoint equations also feeds
through all compiled return corrections. -/
theorem signedHookChannelReversalBalance_of_endpointBalances
    (D : AlignedBiduality σ τ)
    (hterminal : TrimmedTerminalReverseExceptionBalance
      (k := k) (R := R) (S := S) σ τ)
    (houter : ChannelOuterEndpointReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    SignedHookChannelReversalBalance
      (k := k) (R := R) (S := S) σ τ := by
  apply signedHookChannelReversalBalance_of_preliminary
    (k := k) σ τ D
  exact preliminaryHookChannelReversalBalance_of_endpointBalances
    (k := k) σ τ D hterminal houter

omit [IsAlgClosed k] in
include k in
/-- The exact signed-channel equality implies the strip field of the actual
four-packet reversal balance. -/
theorem actualFourVertex_strip_of_signedHookChannelReversalBalance
    (D : AlignedBiduality σ τ)
    (h : SignedHookChannelReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    Fintype.card (QuotientHookOccurrenceFour (k := k) (R := R) σ) +
          Fintype.card (QuotientTrianglePacketFour (k := k) (R := R) σ) +
        Fintype.card (SubmoduleDoubleHookFour (k := k) (S := S) τ) =
      Fintype.card (SubmoduleHookOccurrenceFour (k := k) (S := S) τ) +
          Fintype.card (SubmoduleTrianglePacketFour (k := k) (S := S) τ) +
        Fintype.card (QuotientDoubleHookFour (k := k) (R := R) σ) := by
  have hq := FiniteARTranslationData.quotientHookOccurrenceFour_channel_card_identity_unrestricted
    (k := k) (R := R) σ
  have hs := FiniteARTranslationData.quotientHookOccurrenceFour_channel_card_identity_unrestricted
    (k := k) (R := S) τ
  have hwall := FiniteARTranslationData.hookWallChoice_card_eq
    (K := k) σ τ
      (σ.finiteDimensionalARTranslationData k R)
      (τ.finiteDimensionalARTranslationData k S) D
  unfold SignedHookChannelReversalBalance at h
  dsimp only [SubmoduleHookOccurrenceFour, SubmoduleDoubleHookFour,
    SubmoduleTrianglePacketFour] at h ⊢
  omega

omit [IsAlgClosed k] in
/-- Signed channel reversal and the already completed fixed strip assemble
the concrete reversal balance required by the colevel-four theorem. -/
theorem actualFourVertexReversalBalanceOfSignedHookChannels
    (D : AlignedBiduality σ τ)
    (h : SignedHookChannelReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    ActualFourVertexReversalBalance
      (k := k) (R := R) (S := S) σ τ where
  strip := actualFourVertex_strip_of_signedHookChannelReversalBalance
    (k := k) (R := R) (S := S) σ τ D h
  fixed := fixedPacketFour_card_eq
    (k := k) (R := R) (S := S) σ τ D

/-- Paper-facing colevel-four equality reduced to the one exact signed
channel equation left by the strip proof. -/
theorem levelCount_card_sub_four_eq_of_signedHookChannelReversalBalance
    (D : AlignedBiduality σ τ) (hfour : 4 ≤ Nat.card ι)
    (h : SignedHookChannelReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    σ.qClosure.levelCount (Nat.card ι - 4) =
      σ.sClosure.levelCount (Nat.card ι - 4) := by
  exact levelCount_card_sub_four_eq_of_actualReversalBalance
    (k := k) (R := R) (S := S) σ τ D hfour
      (actualFourVertexReversalBalanceOfSignedHookChannels
        (k := k) (R := R) (S := S) σ τ D h)

/-- Paper-facing colevel-four equality from the exact combined endpoint
remainder of the arrow-chain argument. -/
theorem levelCount_card_sub_four_eq_of_endpointRemainder
    (D : AlignedBiduality σ τ) (hfour : 4 ≤ Nat.card ι)
    (h : EndpointRemainderReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    σ.qClosure.levelCount (Nat.card ι - 4) =
      σ.sClosure.levelCount (Nat.card ι - 4) := by
  apply levelCount_card_sub_four_eq_of_signedHookChannelReversalBalance
    (k := k) σ τ D hfour
  exact signedHookChannelReversalBalance_of_endpointRemainder
    (k := k) σ τ D h

/-- Paper-facing colevel-four equality from the reduced endpoint remainder
after exact outer `M5`/`M3` cancellation. -/
theorem levelCount_card_sub_four_eq_of_reducedEndpointRemainder
    (D : AlignedBiduality σ τ) (hfour : 4 ≤ Nat.card ι)
    (h : ReducedEndpointRemainderReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    σ.qClosure.levelCount (Nat.card ι - 4) =
      σ.sClosure.levelCount (Nat.card ι - 4) := by
  apply levelCount_card_sub_four_eq_of_signedHookChannelReversalBalance
    (k := k) σ τ D hfour
  exact signedHookChannelReversalBalance_of_reducedEndpointRemainder
    (k := k) σ τ D h

/-- Paper-facing cosize-four equality from the corner-reduced endpoint
remainder after all three occurrence-preserving outer-channel overlaps have
been cancelled. -/
theorem levelCount_card_sub_four_eq_of_cornerReducedEndpointRemainder
    (D : AlignedBiduality σ τ) (hfour : 4 ≤ Nat.card ι)
    (h : CornerReducedEndpointRemainderReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    σ.qClosure.levelCount (Nat.card ι - 4) =
      σ.sClosure.levelCount (Nat.card ι - 4) := by
  apply levelCount_card_sub_four_eq_of_reducedEndpointRemainder
    (k := k) σ τ D hfour
  exact
    (reducedEndpointRemainderReversalBalance_iff_cornerReduced
      (k := k) (R := R) (S := S) σ τ).2 h

/-- Paper-facing cosize-four equality from the exact endpoint remainder in
the current manuscript's same-chain/different-chain boundary coordinates. -/
theorem levelCount_card_sub_four_eq_of_diagonalComplementEndpointRemainder
    (D : AlignedBiduality σ τ) (hfour : 4 ≤ Nat.card ι)
    (h : DiagonalComplementEndpointRemainderReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    σ.qClosure.levelCount (Nat.card ι - 4) =
      σ.sClosure.levelCount (Nat.card ι - 4) := by
  apply levelCount_card_sub_four_eq_of_cornerReducedEndpointRemainder
    (k := k) σ τ D hfour
  exact
    (cornerReducedEndpointRemainderReversalBalance_iff_diagonalComplement
      (k := k) σ τ D).2 h

/-- Paper-facing cosize-four equality from the intrinsic different-orbit
endpoint remainder, after the short length-three same-orbit correction has
been cancelled exactly. -/
theorem levelCount_card_sub_four_eq_of_intrinsicDifferentOrbitEndpointRemainder
    (D : AlignedBiduality σ τ) (hfour : 4 ≤ Nat.card ι)
    (h : IntrinsicDifferentOrbitEndpointRemainderReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    σ.qClosure.levelCount (Nat.card ι - 4) =
      σ.sClosure.levelCount (Nat.card ι - 4) := by
  apply levelCount_card_sub_four_eq_of_diagonalComplementEndpointRemainder
    (k := k) σ τ D hfour
  exact
    (diagonalComplementEndpointRemainderReversalBalance_iff_intrinsicDifferentOrbit
      (k := k) σ τ D).2 h

/-- Paper-facing colevel-four equality from the final surviving-outer
corner equation. -/
theorem levelCount_card_sub_four_eq_of_intrinsicSurvivingOuterCorner
    (D : AlignedBiduality σ τ) (hfour : 4 ≤ Nat.card ι)
    (h : IntrinsicSurvivingOuterCornerReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    σ.qClosure.levelCount (Nat.card ι - 4) =
      σ.sClosure.levelCount (Nat.card ι - 4) := by
  apply levelCount_card_sub_four_eq_of_intrinsicDifferentOrbitEndpointRemainder
    (k := k) σ τ D hfour
  exact
    (intrinsicDifferentOrbitEndpointRemainderReversalBalance_iff_survivingOuterCorner
      (k := k) σ τ D).2 h

/-- Paper-facing colevel-four equality from the reduced aligned
outer-transport remainder. -/
theorem levelCount_card_sub_four_eq_of_intrinsicOuterTransportRemainder
    (D : AlignedBiduality σ τ) (hfour : 4 ≤ Nat.card ι)
    (h : IntrinsicOuterTransportRemainderReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    σ.qClosure.levelCount (Nat.card ι - 4) =
      σ.sClosure.levelCount (Nat.card ι - 4) := by
  apply levelCount_card_sub_four_eq_of_intrinsicSurvivingOuterCorner
    (k := k) σ τ D hfour
  exact
    (intrinsicSurvivingOuterCornerReversalBalance_iff_outerTransportRemainder
      (k := k) σ τ D).2 h

/-- Paper-facing colevel-four equality from the local endpoint-index
remainder. -/
theorem levelCount_card_sub_four_eq_of_intrinsicOuterLocalIndexRemainder
    (D : AlignedBiduality σ τ) (hfour : 4 ≤ Nat.card ι)
    (h : IntrinsicOuterLocalIndexRemainderReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    σ.qClosure.levelCount (Nat.card ι - 4) =
      σ.sClosure.levelCount (Nat.card ι - 4) := by
  apply levelCount_card_sub_four_eq_of_intrinsicOuterTransportRemainder
    (k := k) σ τ D hfour
  apply
    (intrinsicOuterTransportRemainderReversalBalance_iff_statusRemainder
      (k := k) (R := R) (S := S) σ τ).2
  exact
    (intrinsicOuterStatusRemainderReversalBalance_iff_localIndexRemainder
      (k := k) σ τ D).2 h

/-- Paper-facing colevel-four equality from the fully local outer-strata
balance with crossed reverse-last exceptions. -/
theorem levelCount_card_sub_four_eq_of_intrinsicOuterLocalStrata
    (D : AlignedBiduality σ τ) (hfour : 4 ≤ Nat.card ι)
    (h : IntrinsicOuterLocalStrataReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    σ.qClosure.levelCount (Nat.card ι - 4) =
      σ.sClosure.levelCount (Nat.card ι - 4) := by
  apply levelCount_card_sub_four_eq_of_intrinsicOuterLocalIndexRemainder
    (k := k) σ τ D hfour
  exact
    (intrinsicOuterLocalIndexRemainderReversalBalance_iff_localStrata
      (k := k) σ τ D).2 h

/-- Paper-facing colevel-four equality from the stronger split endpoint
balances. -/
theorem levelCount_card_sub_four_eq_of_endpointBalances
    (D : AlignedBiduality σ τ) (hfour : 4 ≤ Nat.card ι)
    (hterminal : TrimmedTerminalReverseExceptionBalance
      (k := k) (R := R) (S := S) σ τ)
    (houter : ChannelOuterEndpointReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    σ.qClosure.levelCount (Nat.card ι - 4) =
      σ.sClosure.levelCount (Nat.card ι - 4) := by
  apply levelCount_card_sub_four_eq_of_signedHookChannelReversalBalance
    (k := k) σ τ D hfour
  exact signedHookChannelReversalBalance_of_endpointBalances
    (k := k) σ τ D hterminal houter

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
