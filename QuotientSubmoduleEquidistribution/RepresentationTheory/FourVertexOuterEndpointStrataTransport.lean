import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexOuterEndpointTransport

/-!
# Aligned transport of intrinsic outer endpoint strata

The canonical outer-endpoint equivalence exchanges projective and
injective status on the second source.  This file restricts it to the
resulting intrinsic strata and identifies the first exact crossed pairing:
the injective-common-target part of the outer `M2` stratum is the
translated-projective injective-second outer `M3` stratum on the aligned
dual skeleton.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {K R S : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [Ring S] [Algebra K S] [FiniteDimensional K S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {iota : Type v} {kappa : Type w} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)
  (tau : IndecomposableSkeleton.{u, w, u} S kappa)

namespace FiniteARTranslationData

variable {T : Type u} [Ring T] [IsNoetherianRing T]
  {jota : Type v} [Fintype jota] [DecidableEq jota]
  (rho : IndecomposableSkeleton.{u, v, u} T jota)
  (AR : rho.FiniteARTranslationData)

/-- The projective/noninjective-second outer stratum whose common target
is injective. -/
abbrev FirstPISecondProjectiveNoninjectiveTargetInjectiveOuterPair :=
  {p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair rho //
    Projective (rho.obj p.pair.1.2.1.1) ∧
      ¬ Injective (rho.obj p.pair.1.2.1.1) ∧
      Injective (rho.obj p.pair.1.1.1.2)}

noncomputable instance
    firstPISecondProjectiveNoninjectiveTargetInjectiveOuterPairFintype :
    Fintype
      (AR.FirstPISecondProjectiveNoninjectiveTargetInjectiveOuterPair rho) :=
  Fintype.ofFinite _

/-- The projective/noninjective-second outer stratum whose common target
is noninjective. -/
abbrev FirstPISecondProjectiveNoninjectiveTargetNoninjectiveOuterPair :=
  {p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair rho //
    Projective (rho.obj p.pair.1.2.1.1) ∧
      ¬ Injective (rho.obj p.pair.1.2.1.1) ∧
      ¬ Injective (rho.obj p.pair.1.1.1.2)}

noncomputable instance
    firstPISecondProjectiveNoninjectiveTargetNoninjectiveOuterPairFintype :
    Fintype
      (AR.FirstPISecondProjectiveNoninjectiveTargetNoninjectiveOuterPair rho) :=
  Fintype.ofFinite _

/-- The nonprojective/injective-second outer stratum, before imposing the
translated-target condition. -/
abbrev FirstPISecondNonprojectiveInjectiveOuterPair :=
  {p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair rho //
    ¬ Projective (rho.obj p.pair.1.2.1.1) ∧
      Injective (rho.obj p.pair.1.2.1.1)}

noncomputable instance firstPISecondNonprojectiveInjectiveOuterPairFintype :
    Fintype (AR.FirstPISecondNonprojectiveInjectiveOuterPair rho) :=
  Fintype.ofFinite _

/-- The nonprojective/injective-second outer stratum for which the
translate of the common target remains nonprojective. -/
abbrev FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair :=
  {p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair rho //
    ¬ Projective (rho.obj p.pair.1.2.1.1) ∧
      Injective (rho.obj p.pair.1.2.1.1) ∧
      ¬ Projective
        (rho.obj (AR.arTranslation rho
          ⟨p.pair.1.1.1.2, p.target_nonprojective⟩).1)}

noncomputable instance
    firstPISecondInjectiveTranslatedTargetNonprojectiveOuterPairFintype :
    Fintype
      (AR.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair rho) :=
  Fintype.ofFinite _

/-- The nonprojective/noninjective-second outer stratum. -/
abbrev FirstPISecondNonprojectiveNoninjectiveOuterPair :=
  {p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair rho //
    ¬ Projective (rho.obj p.pair.1.2.1.1) ∧
      ¬ Injective (rho.obj p.pair.1.2.1.1)}

noncomputable instance
    firstPISecondNonprojectiveNoninjectiveOuterPairFintype :
    Fintype (AR.FirstPISecondNonprojectiveNoninjectiveOuterPair rho) :=
  Fintype.ofFinite _

/-- Split the projective/noninjective-second outer stratum according to
injectivity of its common target. -/
def firstPISecondProjectiveNoninjectiveEquivTargetInjectiveSumNoninjective :
    AR.FirstPISecondProjectiveNoninjectiveOuterPair rho ≃
      AR.FirstPISecondProjectiveNoninjectiveTargetInjectiveOuterPair rho ⊕
        AR.FirstPISecondProjectiveNoninjectiveTargetNoninjectiveOuterPair
          rho where
  toFun p := by
    classical
    by_cases h : Injective (rho.obj p.1.pair.1.1.1.2)
    · exact Sum.inl ⟨p.1, p.2.1, p.2.2, h⟩
    · exact Sum.inr ⟨p.1, p.2.1, p.2.2, h⟩
  invFun p := by
    rcases p with p | p
    · exact ⟨p.1, p.2.1, p.2.2.1⟩
    · exact ⟨p.1, p.2.1, p.2.2.1⟩
  left_inv p := by
    classical
    by_cases h : Injective (rho.obj p.1.pair.1.1.1.2)
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.2.2.2]
    · simp [p.2.2.2]

end FiniteARTranslationData

namespace AlignedBiduality

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- The aligned outer transport exchanges the projective/noninjective and
nonprojective/injective second-source strata. -/
def firstPISecondProjectiveNoninjectiveEquivNonprojectiveInjective
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    ARsigma.FirstPISecondProjectiveNoninjectiveOuterPair sigma ≃
      ARtau.FirstPISecondNonprojectiveInjectiveOuterPair tau := by
  let E := D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
  apply E.subtypeEquiv
  intro p
  have hP := D.firstPIOuterEquivAligned_second_projective_iff_injective
    sigma tau ARsigma ARtau p
  have hI := D.firstPIOuterEquivAligned_second_injective_iff_projective
    sigma tau ARsigma ARtau p
  constructor
  · rintro ⟨hProjective, hNoninjective⟩
    exact ⟨(not_congr hI).1 hNoninjective, hP.1 hProjective⟩
  · rintro ⟨hNonprojective, hInjective⟩
    exact ⟨hP.2 hInjective, (not_congr hI).2 hNonprojective⟩

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- The aligned outer transport preserves the nonprojective/noninjective
second-source stratum, while exchanging the two status coordinates. -/
def firstPISecondNonprojectiveNoninjectiveEquiv
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    ARsigma.FirstPISecondNonprojectiveNoninjectiveOuterPair sigma ≃
      ARtau.FirstPISecondNonprojectiveNoninjectiveOuterPair tau := by
  let E := D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
  apply E.subtypeEquiv
  intro p
  have hP := D.firstPIOuterEquivAligned_second_projective_iff_injective
    sigma tau ARsigma ARtau p
  have hI := D.firstPIOuterEquivAligned_second_injective_iff_projective
    sigma tau ARsigma ARtau p
  constructor
  · rintro ⟨hNonprojective, hNoninjective⟩
    exact ⟨(not_congr hI).1 hNoninjective,
      (not_congr hP).1 hNonprojective⟩
  · rintro ⟨hNonprojective, hNoninjective⟩
    exact ⟨(not_congr hP).2 hNoninjective,
      (not_congr hI).2 hNonprojective⟩

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- The injective-common-target part of outer `M2` is exactly the
translated-projective injective-second outer `M3` endpoint on the aligned
dual skeleton. -/
def firstPISecondProjectiveNoninjectiveTargetInjectiveEquivTranslatedTarget
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    ARsigma.FirstPISecondProjectiveNoninjectiveTargetInjectiveOuterPair
        sigma ≃
      ARtau.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair tau := by
  let E := D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
  let F :
      ARsigma.FirstPISecondProjectiveNoninjectiveTargetInjectiveOuterPair
          sigma ≃
        {q : ARtau.FirstProjectiveInjectiveDifferentOrbitOuterPair tau //
          ¬ Projective (tau.obj q.pair.1.2.1.1) ∧
            Injective (tau.obj q.pair.1.2.1.1) ∧
            Projective
              (tau.obj (ARtau.arTranslation tau
                ⟨q.pair.1.1.1.2, q.target_nonprojective⟩).1)} := by
    apply E.subtypeEquiv
    intro p
    have hP := D.firstPIOuterEquivAligned_second_projective_iff_injective
      sigma tau ARsigma ARtau p
    have hI := D.firstPIOuterEquivAligned_second_injective_iff_projective
      sigma tau ARsigma ARtau p
    have hT :=
      D.firstPIOuterEquivAligned_translatedTarget_projective_iff_target_injective
        sigma tau ARsigma ARtau p
    constructor
    · rintro ⟨hProjective, hNoninjective, hTargetInjective⟩
      exact ⟨(not_congr hI).1 hNoninjective, hP.1 hProjective,
        hT.2 hTargetInjective⟩
    · rintro ⟨hNonprojective, hInjective, hTranslatedProjective⟩
      exact ⟨hP.2 hInjective, (not_congr hI).2 hNonprojective,
        hT.1 hTranslatedProjective⟩
  exact F.trans
    { toFun := fun q ↦
        { outer := q.1
          second_nonprojective := q.2.1
          second_injective := q.2.2.1
          translatedTarget_projective := q.2.2.2 }
      invFun := fun q ↦
        ⟨q.outer, q.second_nonprojective, q.second_injective,
          q.translatedTarget_projective⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- The remaining noninjective-common-target part of outer `M2` is
transported exactly to the injective-second outer stratum whose translated
target is nonprojective. -/
def firstPISecondProjectiveNoninjectiveTargetNoninjectiveEquivTranslatedTargetNonprojective
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    ARsigma.FirstPISecondProjectiveNoninjectiveTargetNoninjectiveOuterPair
        sigma ≃
      ARtau.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair
        tau := by
  let E := D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
  apply E.subtypeEquiv
  intro p
  have hP := D.firstPIOuterEquivAligned_second_projective_iff_injective
    sigma tau ARsigma ARtau p
  have hI := D.firstPIOuterEquivAligned_second_injective_iff_projective
    sigma tau ARsigma ARtau p
  have hT :=
    D.firstPIOuterEquivAligned_translatedTarget_projective_iff_target_injective
      sigma tau ARsigma ARtau p
  constructor
  · rintro ⟨hProjective, hNoninjective, hTargetNoninjective⟩
    exact ⟨(not_congr hI).1 hNoninjective, hP.1 hProjective,
      (not_congr hT).2 hTargetNoninjective⟩
  · rintro ⟨hNonprojective, hInjective, hTranslatedNonprojective⟩
    exact ⟨hP.2 hInjective, (not_congr hI).2 hNonprojective,
      (not_congr hT).1 hTranslatedNonprojective⟩

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- Cardinal form of the first crossed outer-stratum cancellation: all
projective/noninjective-second endpoints on the source are the
translated-projective injective-second `M3` endpoints on the target plus
the explicitly isolated noninjective-target remainder. -/
theorem firstPISecondProjectiveNoninjective_card_eq_translatedTarget_add_remainder
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    Fintype.card
        (ARsigma.FirstPISecondProjectiveNoninjectiveOuterPair sigma) =
      Fintype.card
          (ARtau.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair
            tau) +
        Fintype.card
          (ARsigma.FirstPISecondProjectiveNoninjectiveTargetNoninjectiveOuterPair
            sigma) := by
  have hsplit := Fintype.card_congr
    (ARsigma.firstPISecondProjectiveNoninjectiveEquivTargetInjectiveSumNoninjective
      sigma)
  have hcross := Fintype.card_congr
    (D.firstPISecondProjectiveNoninjectiveTargetInjectiveEquivTranslatedTarget
      sigma tau ARsigma ARtau)
  simp only [Fintype.card_sum] at hsplit
  omega

omit [Algebra K S] [FiniteDimensional K S] in
include K in
/-- Channel-level form of the first crossed cancellation.  The exact
projective-anchor `M6` overlap together with the unused outer `M2`
complement equals the crossed injective-second outer `M3` stratum plus the
noninjective-common-target remainder. -/
theorem hookM6ProjectiveAnchor_add_unusedM2_card_eq_crossedM3_add_remainder
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    Fintype.card
          (FiniteARTranslationData.HookM6Channel.InjectiveFourthProjectiveAnchor
            sigma ARsigma) +
        Fintype.card
          (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
            (K := K) sigma ARsigma) =
      Fintype.card
          (ARtau.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair
            tau) +
        Fintype.card
          (ARsigma.FirstPISecondProjectiveNoninjectiveTargetNoninjectiveOuterPair
            sigma) := by
  classical
  have hM2 := Fintype.card_congr
    (FiniteARTranslationData.hookWallBadUInjectiveFourthEquivFirstPISecondProjectiveNoninjective
      (K := K) sigma ARsigma)
  have himage := Fintype.card_congr
    (FiniteARTranslationData.hookM6ProjectiveAnchorEquivHookWallBadUImage
      (K := K) sigma ARsigma)
  have hsplit := Fintype.card_congr
    (Equiv.sumCompl (fun W :
        FiniteARTranslationData.HookWallBadU.InjectiveFourthEndpoint
          sigma ARsigma ↦
      W ∈ FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorImage
        (K := K) sigma ARsigma))
  have hcross :=
    D.firstPISecondProjectiveNoninjective_card_eq_translatedTarget_add_remainder
      sigma tau ARsigma ARtau
  simp only [Fintype.card_sum] at hsplit
  change
    Fintype.card
          (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorImage
            (K := K) sigma ARsigma) +
        Fintype.card
          (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
            (K := K) sigma ARsigma) =
      Fintype.card
        (FiniteARTranslationData.HookWallBadU.InjectiveFourthEndpoint
          sigma ARsigma) at hsplit
  omega

end AlignedBiduality

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
