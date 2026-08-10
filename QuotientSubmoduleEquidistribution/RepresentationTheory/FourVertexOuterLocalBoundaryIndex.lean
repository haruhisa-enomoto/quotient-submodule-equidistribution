import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexDifferentOrbitTargetCorners
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexOuterEndpointTwoSourceTransport

/-!
# Candidate local full-boundary index for the outer four-vertex strata

The invariant full-boundary index is the complement of the fixed
projective/injective-source intersection in the different-orbit target
boundary.  A strong candidate local classification identifies that
complement, together with the reverse-last exception, with the three local
outer strata left by the signed-strip reduction.  This file packages that
single-skeleton statement and proves only the implication from two such
local classifications to the crossed outer balance.
-/

set_option autoImplicit false
noncomputable section

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData

universe u v

variable {K R : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (AR : σ.FiniteARTranslationData)

/-- The three local outer strata remaining after all exact endpoint
overlaps and aligned status transports have been cancelled. -/
abbrev OuterLocalStrataFamily :=
  HookM6Channel.InjectiveFourthEndpoint σ AR ⊕
    (AR.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair σ ⊕
      AR.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair σ)

/-- The raw full-boundary index together with the exceptional reverse-last
part of the regular `M6` reconstruction. -/
abbrev TargetBoundaryComplementReverseLastFamily :=
  AR.DifferentOrbitTargetBoundaryNoOuterIntersectionPair σ ⊕
    AR.BoundaryM6ReverseLastPair σ

/-- Source-boundary form of the same raw boundary index.  Both summands
now live at the literal source endpoint, which is the natural coordinate
for classifying the reverse-last exception. -/
abbrev SourceBoundaryComplementReverseLastFamily :=
  AR.DifferentOrbitSourceBoundaryNoOuterIntersectionPair σ ⊕
    AR.BoundaryM6ReverseLastPair σ

/-- Expanded endpoint coordinate for the source-boundary family.  The
complement is resolved occurrence-by-occurrence into its projective-target
and trimmed literal-source branches, while the native reverse-last exception
is retained as a separate tagged summand. -/
abbrev SourceBoundaryEndpointReverseLastFamily :=
  (AR.DifferentOrbitProjectiveTargetCommonTargetPair σ ⊕
      AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair σ) ⊕
    AR.BoundaryM6ReverseLastPair σ

/-- The full square shift carries the source-boundary family exactly to
the target-boundary family while leaving the tagged reverse-last summand
unchanged. -/
def sourceBoundaryComplementReverseLastEquivTarget :
    AR.SourceBoundaryComplementReverseLastFamily σ ≃
      AR.TargetBoundaryComplementReverseLastFamily σ :=
  Equiv.sumCongr
    (AR.differentOrbitCommonTargetBoundaryNoOuterIntersectionEquiv σ)
    (Equiv.refl _)

include K in
/-- Exact endpoint expansion of the source-boundary complement/reverse-last
family.  In contrast to the earlier cardinal formula, this map retains every
ordered labelled-arrow occurrence. -/
def sourceBoundaryComplementReverseLastEquivEndpoint :
    AR.SourceBoundaryComplementReverseLastFamily σ ≃
      AR.SourceBoundaryEndpointReverseLastFamily σ :=
  Equiv.sumCongr
    (AR.differentOrbitSourceBoundaryComplementEquivProjectiveTargetSumLiteral
      (K := K) σ)
    (Equiv.refl _)

/-- Candidate strong local occurrence classification.  It is deliberately a
cardinal statement here; neither this definition nor the results below prove
it. -/
def OuterLocalBoundaryIndex : Prop :=
  Fintype.card (AR.OuterLocalStrataFamily σ) =
    Fintype.card (AR.TargetBoundaryComplementReverseLastFamily σ)

/-- Expanded cardinal form of the local boundary index. -/
theorem outerLocalBoundaryIndex_iff :
    AR.OuterLocalBoundaryIndex σ ↔
      Fintype.card (HookM6Channel.InjectiveFourthEndpoint σ AR) +
          Fintype.card
            (AR.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
              σ) +
          Fintype.card
            (AR.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair
              σ) =
        Fintype.card
            (AR.DifferentOrbitTargetBoundaryNoOuterIntersectionPair σ) +
          Fintype.card (AR.BoundaryM6ReverseLastPair σ) := by
  unfold OuterLocalBoundaryIndex
  simp only [OuterLocalStrataFamily,
    TargetBoundaryComplementReverseLastFamily, Fintype.card_sum]
  omega

/-- Equivalent source-boundary form of the candidate local index. -/
theorem outerLocalBoundaryIndex_iff_sourceBoundary :
    AR.OuterLocalBoundaryIndex σ ↔
      Fintype.card (AR.OuterLocalStrataFamily σ) =
        Fintype.card (AR.SourceBoundaryComplementReverseLastFamily σ) := by
  unfold OuterLocalBoundaryIndex
  rw [Fintype.card_congr
    (AR.sourceBoundaryComplementReverseLastEquivTarget σ)]

include K in
/-- Fully expanded source-endpoint form of the candidate local index. -/
theorem outerLocalBoundaryIndex_iff_sourceEndpoint :
    AR.OuterLocalBoundaryIndex σ ↔
      Fintype.card (AR.OuterLocalStrataFamily σ) =
        Fintype.card (AR.SourceBoundaryEndpointReverseLastFamily σ) := by
  rw [AR.outerLocalBoundaryIndex_iff_sourceBoundary σ,
    Fintype.card_congr
      (AR.sourceBoundaryComplementReverseLastEquivEndpoint (K := K) σ)]

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedBiduality

universe u v w

variable {K R S : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [Ring S] [Algebra K S] [FiniteDimensional K S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

include K in
/-- The exact target-boundary complements have equal cardinality under
aligned reversal. -/
theorem targetBoundaryComplement_card_eq
    (D : AlignedBiduality σ τ)
    (ARσ : σ.FiniteARTranslationData)
    (ARτ : τ.FiniteARTranslationData) :
    Fintype.card
        (ARσ.DifferentOrbitTargetBoundaryNoOuterIntersectionPair σ) =
      Fintype.card
        (ARτ.DifferentOrbitTargetBoundaryNoOuterIntersectionPair τ) := by
  have hσ :=
    ARσ.projectiveTarget_add_literal_card_eq_targetBoundaryComplement
      (K := K) σ
  have hτ :=
    ARτ.projectiveTarget_add_literal_card_eq_targetBoundaryComplement
      (K := K) τ
  have hboundary := D.projectiveTarget_add_literal_boundary_card_eq
    (K := K) σ τ ARσ ARτ
  omega

include K in
/-- Exact reformulation of the crossed outer balance after adjoining the
equal target-boundary complements on the two sides. -/
theorem outerLocalStrata_crossedReverseLast_iff_crossedBoundaryFamilies
    (D : AlignedBiduality σ τ)
    (ARσ : σ.FiniteARTranslationData)
    (ARτ : τ.FiniteARTranslationData) :
    (Fintype.card
            (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
              σ ARσ) +
          Fintype.card
            (ARσ.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
              σ) +
          Fintype.card
            (ARσ.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair
              σ) +
          Fintype.card (ARτ.BoundaryM6ReverseLastPair τ) =
        Fintype.card
            (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
              τ ARτ) +
          Fintype.card
            (ARτ.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
              τ) +
          Fintype.card
            (ARτ.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair
              τ) +
          Fintype.card (ARσ.BoundaryM6ReverseLastPair σ)) ↔
      (Fintype.card (ARσ.OuterLocalStrataFamily σ) +
          Fintype.card
            (ARτ.TargetBoundaryComplementReverseLastFamily τ) =
        Fintype.card (ARτ.OuterLocalStrataFamily τ) +
          Fintype.card
            (ARσ.TargetBoundaryComplementReverseLastFamily σ)) := by
  have hcomplement := D.targetBoundaryComplement_card_eq
    (K := K) σ τ ARσ ARτ
  simp only [FiniteARTranslationData.OuterLocalStrataFamily,
    FiniteARTranslationData.TargetBoundaryComplementReverseLastFamily,
    Fintype.card_sum]
  constructor <;> intro h <;> omega

include K in
/-- Exact source-boundary-complement coordinate form of the crossed outer
balance. -/
theorem outerLocalStrata_crossedReverseLast_iff_crossedSourceBoundaryFamilies
    (D : AlignedBiduality σ τ)
    (ARσ : σ.FiniteARTranslationData)
    (ARτ : τ.FiniteARTranslationData) :
    (Fintype.card
            (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
              σ ARσ) +
          Fintype.card
            (ARσ.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
              σ) +
          Fintype.card
            (ARσ.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair
              σ) +
          Fintype.card (ARτ.BoundaryM6ReverseLastPair τ) =
        Fintype.card
            (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
              τ ARτ) +
          Fintype.card
            (ARτ.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
              τ) +
          Fintype.card
            (ARτ.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair
              τ) +
          Fintype.card (ARσ.BoundaryM6ReverseLastPair σ)) ↔
      (Fintype.card (ARσ.OuterLocalStrataFamily σ) +
          Fintype.card
            (ARτ.SourceBoundaryComplementReverseLastFamily τ) =
        Fintype.card (ARτ.OuterLocalStrataFamily τ) +
          Fintype.card
            (ARσ.SourceBoundaryComplementReverseLastFamily σ)) := by
  have htarget :=
    D.outerLocalStrata_crossedReverseLast_iff_crossedBoundaryFamilies
      (K := K) σ τ ARσ ARτ
  have hσ := Fintype.card_congr
    (ARσ.sourceBoundaryComplementReverseLastEquivTarget σ)
  have hτ := Fintype.card_congr
    (ARτ.sourceBoundaryComplementReverseLastEquivTarget τ)
  constructor <;> intro h
  · have := htarget.1 h
    omega
  · apply htarget.2
    omega

include K in
/-- Fully expanded source-endpoint form of the crossed outer balance.  Its
right-hand family is the tagged sum of projective-target occurrences,
trimmed literal-source occurrences, and the native reverse-last exception. -/
theorem outerLocalStrata_crossedReverseLast_iff_crossedSourceEndpointFamilies
    (D : AlignedBiduality σ τ)
    (ARσ : σ.FiniteARTranslationData)
    (ARτ : τ.FiniteARTranslationData) :
    (Fintype.card
            (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
              σ ARσ) +
          Fintype.card
            (ARσ.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
              σ) +
          Fintype.card
            (ARσ.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair
              σ) +
          Fintype.card (ARτ.BoundaryM6ReverseLastPair τ) =
        Fintype.card
            (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
              τ ARτ) +
          Fintype.card
            (ARτ.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
              τ) +
          Fintype.card
            (ARτ.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair
              τ) +
          Fintype.card (ARσ.BoundaryM6ReverseLastPair σ)) ↔
      (Fintype.card (ARσ.OuterLocalStrataFamily σ) +
          Fintype.card
            (ARτ.SourceBoundaryEndpointReverseLastFamily τ) =
        Fintype.card (ARτ.OuterLocalStrataFamily τ) +
          Fintype.card
            (ARσ.SourceBoundaryEndpointReverseLastFamily σ)) := by
  have hsource :=
    D.outerLocalStrata_crossedReverseLast_iff_crossedSourceBoundaryFamilies
      (K := K) σ τ ARσ ARτ
  have hσ := Fintype.card_congr
    (ARσ.sourceBoundaryComplementReverseLastEquivEndpoint (K := K) σ)
  have hτ := Fintype.card_congr
    (ARτ.sourceBoundaryComplementReverseLastEquivEndpoint (K := K) τ)
  constructor <;> intro h
  · have := hsource.1 h
    omega
  · apply hsource.2
    omega

include K in
/-- Two copies of the local full-boundary classification imply the crossed
outer-strata/reverse-last balance. -/
theorem outerLocalStrata_add_crossedReverseLast_card_eq
    (D : AlignedBiduality σ τ)
    (ARσ : σ.FiniteARTranslationData)
    (ARτ : τ.FiniteARTranslationData)
    (hσ : ARσ.OuterLocalBoundaryIndex σ)
    (hτ : ARτ.OuterLocalBoundaryIndex τ) :
    Fintype.card
          (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
            σ ARσ) +
          Fintype.card
            (ARσ.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
              σ) +
          Fintype.card
            (ARσ.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair
              σ) +
          Fintype.card (ARτ.BoundaryM6ReverseLastPair τ) =
      Fintype.card
          (FiniteARTranslationData.HookM6Channel.InjectiveFourthEndpoint
            τ ARτ) +
          Fintype.card
            (ARτ.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
              τ) +
          Fintype.card
            (ARτ.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair
              τ) +
          Fintype.card (ARσ.BoundaryM6ReverseLastPair σ) := by
  have hcomplement := D.targetBoundaryComplement_card_eq
    (K := K) σ τ ARσ ARτ
  rw [ARσ.outerLocalBoundaryIndex_iff σ] at hσ
  rw [ARτ.outerLocalBoundaryIndex_iff τ] at hτ
  omega

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedBiduality
