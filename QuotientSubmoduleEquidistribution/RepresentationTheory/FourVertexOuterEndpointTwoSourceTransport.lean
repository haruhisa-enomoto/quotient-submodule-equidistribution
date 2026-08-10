import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexOuterEndpointStrataTransport

/-!
# Two-source coordinates for transported outer endpoints

For an oriented outer endpoint with a nonprojective, noninjective second
source, the second arrow is interior.  Its membership in the first two
trimmed source layers is equivalent to projectivity of the AR translate of
the common target.  This endpoint-coordinate form is the starting point for
transporting the remaining deep/interior outer strata.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData

universe u v

variable {K R : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R]
  {iota : Type v} [Fintype iota] [DecidableEq iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)
  (AR : sigma.FiniteARTranslationData)

omit [Algebra K R] [FiniteDimensional K R] [DecidableEq iota] in
/-- For an outer pair with an interior second arrow, membership of that
arrow in the first two trimmed source layers is exactly projectivity of
the AR translate of the common target. -/
theorem firstPISecond_twoSource_iff_translatedTarget_projective
    (p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma)
    (hsecondP : ¬ Projective (sigma.obj p.pair.1.2.1.1))
    (hsecondI : ¬ Injective (sigma.obj p.pair.1.2.1.1)) :
    let H := toInteriorArrow sigma AR p.pair.1.2
      ⟨by
        rw [← p.pair.2]
        exact p.target_nonprojective,
      hsecondI⟩
    ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
        H ↔
      Projective
        (sigma.obj (AR.arTranslation sigma
          ⟨p.pair.1.1.1.2, p.target_nonprojective⟩).1) := by
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let U := M.arrowInteriorOrbitData sigma
  have hsecondTargetNP :
      ¬ Projective (sigma.obj p.pair.1.2.1.2) := by
    rw [← p.pair.2]
    exact p.target_nonprojective
  let H := toInteriorArrow sigma AR p.pair.1.2
    ⟨hsecondTargetNP, hsecondI⟩
  have hsource : ¬ O.InteriorSource H := by
    intro h
    apply hsecondP
    exact (M.arrowInterior_source_iff sigma H).1 h
  let tSecond : sigma.NonprojectiveLabel :=
    ⟨p.pair.1.2.1.2, hsecondTargetNP⟩
  let tFirst : sigma.NonprojectiveLabel :=
    ⟨p.pair.1.1.1.2, p.target_nonprojective⟩
  have ht : tSecond = tFirst := Subtype.ext p.pair.2.symm
  have hval := M.arrowOrbitData_tau_val sigma
    ⟨p.pair.1.2, hsecondTargetNP⟩
  have hinterior :
      (U.tau ⟨H, hsource⟩).1.1 =
        (O.tau ⟨p.pair.1.2, hsecondTargetNP⟩).1 := by
    rfl
  have hrotate :
      (U.tau ⟨H, hsource⟩).1.1.1.1 =
        (AR.arTranslation sigma tFirst).1 := by
    rw [hinterior]
    calc
      (O.tau ⟨p.pair.1.2, hsecondTargetNP⟩).1.1.1 =
          (M.tau tSecond).1 := congrArg Prod.fst hval
      _ = (M.tau tFirst).1 := congrArg
        (fun x : sigma.NonprojectiveLabel ↦ (M.tau x).1) ht
      _ = (AR.arTranslation sigma tFirst).1 := rfl
  constructor
  · rintro (hfirst | hsecond)
    · exact (hsecondP ((M.arrowInterior_source_iff sigma H).1 hfirst)).elim
    · have h := (M.arrowInterior_source_iff sigma
          (U.tau ⟨H, hsource⟩).1).1 (hsecond hsource)
      simpa [tFirst] using hrotate ▸ h
  · intro htranslated
    right
    intro hnot
    apply (M.arrowInterior_source_iff sigma
      (U.tau ⟨H, hnot⟩).1).2
    have hproof : ⟨H, hnot⟩ = (⟨H, hsource⟩ :
        {a : M.InteriorArrow sigma // ¬ O.InteriorSource a}) := by
      rfl
    rw [hproof]
    simpa [tFirst] using hrotate.symm ▸ htranslated

/-- An oriented outer occurrence whose second arrow is interior but lies
beyond the first two trimmed source layers. -/
@[ext]
structure FirstPISecondInteriorNotTwoSourceOuterPair where
  outer : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma
  second_nonprojective : ¬ Projective (sigma.obj outer.pair.1.2.1.1)
  second_noninjective : ¬ Injective (sigma.obj outer.pair.1.2.1.1)
  second_not_twoSource :
    ¬ ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      (toInteriorArrow sigma AR outer.pair.1.2
        ⟨by
          rw [← outer.pair.2]
          exact outer.target_nonprojective,
        second_noninjective⟩)

noncomputable instance firstPISecondInteriorNotTwoSourceOuterPairFinite :
    Finite (AR.FirstPISecondInteriorNotTwoSourceOuterPair sigma) :=
  Finite.of_injective
    (fun p ↦ p.outer.pair) (by
      intro p q h
      apply FirstPISecondInteriorNotTwoSourceOuterPair.ext
      exact FirstProjectiveInjectiveDifferentOrbitOuterPair.ext h)

noncomputable instance firstPISecondInteriorNotTwoSourceOuterPairFintype :
    Fintype (AR.FirstPISecondInteriorNotTwoSourceOuterPair sigma) :=
  Fintype.ofFinite _

/-- Nonprojective/noninjective-second outer occurrences whose common target
is injective. -/
abbrev FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair :=
  {p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma //
    ¬ Projective (sigma.obj p.pair.1.2.1.1) ∧
      ¬ Injective (sigma.obj p.pair.1.2.1.1) ∧
      Injective (sigma.obj p.pair.1.1.1.2)}

/-- Nonprojective/noninjective-second outer occurrences whose common target
is noninjective. -/
abbrev FirstPISecondNonprojectiveNoninjectiveTargetNoninjectiveOuterPair :=
  {p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma //
    ¬ Projective (sigma.obj p.pair.1.2.1.1) ∧
      ¬ Injective (sigma.obj p.pair.1.2.1.1) ∧
      ¬ Injective (sigma.obj p.pair.1.1.1.2)}

noncomputable instance
    firstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPairFintype :
    Fintype
      (AR.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
        sigma) :=
  Fintype.ofFinite _

noncomputable instance
    firstPISecondNonprojectiveNoninjectiveTargetNoninjectiveOuterPairFintype :
    Fintype
      (AR.FirstPISecondNonprojectiveNoninjectiveTargetNoninjectiveOuterPair
        sigma) :=
  Fintype.ofFinite _

include K AR in
/-- The exact second-boundary outer `M6` family has the cardinality of its
intrinsic image inside the two-source, nonprojective/noninjective-second
outer stratum. -/
theorem hookM6SecondBoundary_card_eq_firstPISecondInteriorM6Image :
    Fintype.card
        (HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary
          sigma AR) =
      Fintype.card (AR.FirstPISecondInteriorM6Image (K := K) sigma) := by
  let G :=
    hookWallBadBInjectiveFirstSecondNoninjectiveEquivFirstPISecondInteriorTwoSource
      (K := K) sigma AR
  let f := fun M :
      HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary
        sigma AR ↦
    G (M.toHookWallBadBSecondNoninjective (K := K) sigma AR)
  have hf : Function.Injective f := by
    intro M N h
    have hW :
        M.toHookWallBadBSecondNoninjective (K := K) sigma AR =
          N.toHookWallBadBSecondNoninjective (K := K) sigma AR :=
      G.injective h
    apply
      HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary.toHookWallBadB_injective
        (K := K) sigma AR
    exact congrArg Subtype.val hW
  exact Fintype.card_congr (Equiv.ofInjective f hf)

include K AR in
/-- The full intrinsic two-source outer stratum is the exact
second-boundary `M6` image plus its recorded occurrence complement. -/
theorem firstPISecondInteriorTwoSource_card_eq_m6SecondBoundary_add_complement :
    Fintype.card (AR.FirstPISecondInteriorTwoSourceOuterPair sigma) =
      Fintype.card
          (HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary
            sigma AR) +
        Fintype.card
          (AR.FirstPISecondInteriorM6Complement (K := K) sigma) := by
  classical
  have hsplit := Fintype.card_congr
    (Equiv.sumCompl (fun p :
        AR.FirstPISecondInteriorTwoSourceOuterPair sigma ↦
      p ∈ AR.FirstPISecondInteriorM6Image (K := K) sigma))
  have himage :=
    AR.hookM6SecondBoundary_card_eq_firstPISecondInteriorM6Image
      (K := K) sigma
  simp only [Fintype.card_sum] at hsplit
  change
    Fintype.card (AR.FirstPISecondInteriorM6Image (K := K) sigma) +
        Fintype.card
          (AR.FirstPISecondInteriorM6Complement (K := K) sigma) =
      Fintype.card (AR.FirstPISecondInteriorTwoSourceOuterPair sigma) at hsplit
  omega

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData

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

namespace AlignedBiduality

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- On the nonprojective/noninjective-second stratum, the transported
second arrow belongs to the first two trimmed source layers exactly when
the original common target is injective. -/
theorem firstPIOuterEquivAligned_second_twoSource_iff_target_injective
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma)
    (hsecondP : ¬ Projective (sigma.obj p.pair.1.2.1.1))
    (hsecondI : ¬ Injective (sigma.obj p.pair.1.2.1.1)) :
    let Ep := D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p
    let H := FiniteARTranslationData.toInteriorArrow tau ARtau Ep.pair.1.2
      ⟨by
        rw [← Ep.pair.2]
        exact Ep.target_nonprojective,
      (not_congr
        (D.firstPIOuterEquivAligned_second_projective_iff_injective
          sigma tau ARsigma ARtau p)).1 hsecondP⟩
    ((ARtau.arMeshRotationData tau).arrowInteriorOrbitData tau).TwoSource H ↔
      Injective (sigma.obj p.pair.1.1.1.2) := by
  let Ep := D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p
  have hEpP : ¬ Projective (tau.obj Ep.pair.1.2.1.1) :=
    (not_congr
      (D.firstPIOuterEquivAligned_second_injective_iff_projective
        sigma tau ARsigma ARtau p)).1 hsecondI
  have hEpI : ¬ Injective (tau.obj Ep.pair.1.2.1.1) :=
    (not_congr
      (D.firstPIOuterEquivAligned_second_projective_iff_injective
        sigma tau ARsigma ARtau p)).1 hsecondP
  exact
    (ARtau.firstPISecond_twoSource_iff_translatedTarget_projective
      tau Ep hEpP hEpI).trans
        (D.firstPIOuterEquivAligned_translatedTarget_projective_iff_target_injective
          sigma tau ARsigma ARtau p)

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- Dually, the original second arrow belongs to the first two trimmed
source layers exactly when the transported common target is injective. -/
theorem firstPIOuterEquivAligned_target_injective_iff_second_twoSource
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma)
    (hsecondP : ¬ Projective (sigma.obj p.pair.1.2.1.1))
    (hsecondI : ¬ Injective (sigma.obj p.pair.1.2.1.1)) :
    Injective (tau.obj
        (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p).pair.1.1.1.2) ↔
      let H := FiniteARTranslationData.toInteriorArrow sigma ARsigma
        p.pair.1.2
        ⟨by
          rw [← p.pair.2]
          exact p.target_nonprojective,
        hsecondI⟩
      ((ARsigma.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
        H := by
  have hlocal :=
    ARsigma.firstPISecond_twoSource_iff_translatedTarget_projective
      sigma p hsecondP hsecondI
  exact
    (D.firstPIOuterEquivAligned_target_injective_iff_translatedTarget_projective
      sigma tau ARsigma ARtau p).trans hlocal.symm

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- The intrinsic two-source, nonprojective/noninjective-second stratum is
transported exactly to the same second-source status with injective common
target. -/
def firstPISecondInteriorTwoSourceEquivTargetInjective
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    ARsigma.FirstPISecondInteriorTwoSourceOuterPair sigma ≃
      ARtau.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
        tau := by
  let E := D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
  let SourceSubtype :=
    {p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma //
      ∃ hP : ¬ Projective (sigma.obj p.pair.1.2.1.1),
      ∃ hI : ¬ Injective (sigma.obj p.pair.1.2.1.1),
        ((ARsigma.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
          (FiniteARTranslationData.toInteriorArrow sigma ARsigma
            p.pair.1.2
            ⟨by
              rw [← p.pair.2]
              exact p.target_nonprojective,
            hI⟩)}
  let S : ARsigma.FirstPISecondInteriorTwoSourceOuterPair sigma ≃
      SourceSubtype := {
    toFun p := ⟨p.outer, p.second_nonprojective,
      p.second_noninjective, p.second_twoSource⟩
    invFun p := by
      let hP := Classical.choose p.2
      let hI := Classical.choose (Classical.choose_spec p.2)
      let htwo := Classical.choose_spec (Classical.choose_spec p.2)
      exact
        { outer := p.1
          second_nonprojective := hP
          second_noninjective := hI
          second_twoSource := htwo }
    left_inv p := by
      apply FiniteARTranslationData.FirstPISecondInteriorTwoSourceOuterPair.ext
      rfl
    right_inv p := by
      apply Subtype.ext
      rfl }
  let F : SourceSubtype ≃
      ARtau.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
        tau := by
    apply E.subtypeEquiv
    intro p
    have hP := D.firstPIOuterEquivAligned_second_projective_iff_injective
      sigma tau ARsigma ARtau p
    have hI := D.firstPIOuterEquivAligned_second_injective_iff_projective
      sigma tau ARsigma ARtau p
    constructor
    · rintro ⟨hp, hi, htwo⟩
      refine ⟨(not_congr hI).1 hi, (not_congr hP).1 hp, ?_⟩
      exact
        (D.firstPIOuterEquivAligned_target_injective_iff_second_twoSource
          sigma tau ARsigma ARtau p hp hi).2 htwo
    · rintro ⟨hp, hi, htarget⟩
      have hp' := (not_congr hP).2 hi
      have hi' := (not_congr hI).2 hp
      refine ⟨hp', hi', ?_⟩
      exact
        (D.firstPIOuterEquivAligned_target_injective_iff_second_twoSource
          sigma tau ARsigma ARtau p hp' hi').1 htarget
  exact S.trans F

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- The complementary deep second-arrow stratum is transported exactly to
the same second-source status with noninjective common target. -/
def firstPISecondInteriorNotTwoSourceEquivTargetNoninjective
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    ARsigma.FirstPISecondInteriorNotTwoSourceOuterPair sigma ≃
      ARtau.FirstPISecondNonprojectiveNoninjectiveTargetNoninjectiveOuterPair
        tau := by
  let E := D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
  let SourceSubtype :=
    {p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma //
      ∃ hP : ¬ Projective (sigma.obj p.pair.1.2.1.1),
      ∃ hI : ¬ Injective (sigma.obj p.pair.1.2.1.1),
        ¬ ((ARsigma.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
          (FiniteARTranslationData.toInteriorArrow sigma ARsigma
            p.pair.1.2
            ⟨by
              rw [← p.pair.2]
              exact p.target_nonprojective,
            hI⟩)}
  let S : ARsigma.FirstPISecondInteriorNotTwoSourceOuterPair sigma ≃
      SourceSubtype := {
    toFun p := ⟨p.outer, p.second_nonprojective,
      p.second_noninjective, p.second_not_twoSource⟩
    invFun p := by
      let hP := Classical.choose p.2
      let hI := Classical.choose (Classical.choose_spec p.2)
      let htwo := Classical.choose_spec (Classical.choose_spec p.2)
      exact
        { outer := p.1
          second_nonprojective := hP
          second_noninjective := hI
          second_not_twoSource := htwo }
    left_inv p := by
      apply FiniteARTranslationData.FirstPISecondInteriorNotTwoSourceOuterPair.ext
      rfl
    right_inv p := by
      apply Subtype.ext
      rfl }
  let F : SourceSubtype ≃
      ARtau.FirstPISecondNonprojectiveNoninjectiveTargetNoninjectiveOuterPair
        tau := by
    apply E.subtypeEquiv
    intro p
    have hP := D.firstPIOuterEquivAligned_second_projective_iff_injective
      sigma tau ARsigma ARtau p
    have hI := D.firstPIOuterEquivAligned_second_injective_iff_projective
      sigma tau ARsigma ARtau p
    constructor
    · rintro ⟨hp, hi, htwo⟩
      refine ⟨(not_congr hI).1 hi, (not_congr hP).1 hp, ?_⟩
      exact
        (not_congr
          (D.firstPIOuterEquivAligned_target_injective_iff_second_twoSource
            sigma tau ARsigma ARtau p hp hi)).2 htwo
    · rintro ⟨hp, hi, htarget⟩
      have hp' := (not_congr hP).2 hi
      have hi' := (not_congr hI).2 hp
      refine ⟨hp', hi', ?_⟩
      exact
        (not_congr
          (D.firstPIOuterEquivAligned_target_injective_iff_second_twoSource
            sigma tau ARsigma ARtau p hp' hi')).1 htarget
  exact S.trans F

end AlignedBiduality

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
