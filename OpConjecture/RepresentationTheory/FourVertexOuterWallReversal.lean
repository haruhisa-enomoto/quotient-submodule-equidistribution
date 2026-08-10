import OpConjecture.RepresentationTheory.FourVertexOuterMirrorPackaging

/-!
# Reversal invariance of the unused wall complements

The two unused wall complements are characterized intrinsically: the
projective-anchor `M6` overlap uses exactly the projective-second
occurrences with noninjective common target, and the second-boundary
`M6` overlap uses exactly the interior-two-source occurrences with
noninjective common target.  Hence both complements are the injective
common-target parts of their strata.  Under the aligned crossing the
three surviving wall strata permute — projective-second swaps with
injective-second, interior-two-source is self-paired — so the wall sum
`M2 complement + M3 complement` is reversal invariant.
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

omit [DecidableEq ι] in
include K in
/-- A projective, noninjective co-source forbids a translation-fixed
common target. -/
theorem target_ne_translation_of_projective_cosource
    (w t : ι)
    (hwP : Projective (σ.obj w))
    (hwNI : ¬ Injective (σ.obj w))
    (htNP : ¬ Projective (σ.obj t))
    (hwt : HasIrreducibleMorphism (σ.obj w) (σ.obj t)) :
    t ≠ (AR.arTranslation σ ⟨t, htNP⟩).1 := by
  intro hfix
  apply hwNI
  have htw : HasIrreducibleMorphism
      (σ.obj (AR.arTranslation σ ⟨t, htNP⟩).1) (σ.obj w) :=
    (AR.arTranslation_incidence σ ⟨t, htNP⟩ w).1 hwt
  rw [← hfix] at htw
  exact AR.injective_of_projective_two_cycle (K := K) σ w t hwP hwt htw

omit [DecidableEq ι] in
include K in
/-- With a projective translated target there is no return arrow from
the common target onto a nonprojective co-source. -/
theorem not_hom_target_source_of_translatedTarget_projective
    (w t : ι)
    (hwNP : ¬ Projective (σ.obj w))
    (htNP : ¬ Projective (σ.obj t))
    (htvP : Projective (σ.obj (AR.arTranslation σ ⟨t, htNP⟩).1))
    (hwt : HasIrreducibleMorphism (σ.obj w) (σ.obj t)) :
    ¬ HasIrreducibleMorphism (σ.obj t) (σ.obj w) := by
  intro htw
  have hne : t ≠ (AR.arTranslation σ ⟨t, htNP⟩).1 := by
    intro hfix
    apply htNP
    rw [hfix]
    exact htvP
  have hfixw :=
    (hom_target_source_iff_translation_fixed (K := K) σ AR w t hwNP
      htNP hne hwt).1 htw
  have hwtv :=
    (hom_source_translate_iff_translation_fixed (K := K) σ AR w t hwNP
      htNP hne hwt).2 hfixw
  have htvw : HasIrreducibleMorphism
      (σ.obj (AR.arTranslation σ ⟨t, htNP⟩).1) (σ.obj w) :=
    (AR.arTranslation_incidence σ ⟨t, htNP⟩ w).1 hwt
  exact (AR.arTranslation σ ⟨t, htNP⟩).2
    (AR.injective_of_projective_two_cycle (K := K) σ
      (AR.arTranslation σ ⟨t, htNP⟩).1 w htvP htvw hwtv)

include K in
/-- The projective-anchor `M6` overlap uses exactly the
projective-second occurrences whose common target is noninjective. -/
theorem mem_firstPISecondProjectiveM6Image_iff
    (p : AR.FirstPISecondProjectiveNoninjectiveOuterPair σ) :
    p ∈ AR.FirstPISecondProjectiveM6Image (K := K) σ ↔
      ¬ Injective (σ.obj p.1.pair.1.1.1.2) := by
  constructor
  · rintro ⟨M, rfl⟩
    intro hI
    apply hookM6InjectiveFourthToOuterPair_target_noninjective σ AR M.1
    rw [hookM6InjectiveFourthToOuterPair_pair_eq σ AR M.1,
      ← M.toHookWallBadU_commonTargetPair (K := K) σ AR]
    exact hI
  · intro htNI
    have hwt : HasIrreducibleMorphism
        (σ.obj p.1.pair.1.2.1.1) (σ.obj p.1.pair.1.1.1.2) := by
      have h := p.1.pair.1.2.2
      rw [← p.1.pair.2] at h
      exact h
    have hne :=
      target_ne_translation_of_projective_cosource (K := K) σ AR
        p.1.pair.1.2.1.1 p.1.pair.1.1.1.2 p.2.1 p.2.2
        p.1.target_nonprojective hwt
    obtain ⟨M, hM⟩ :=
      (mem_range_hookM6InjectiveFourthToTargetNoninjectiveCell_iff_normalized
        (K := K) σ AR ⟨p.1, p.2.2, htNI⟩).2
        ⟨(target_ne_outerCellLast_iff σ AR ⟨p.1, p.2.2, htNI⟩).2 hne,
          not_hom_target_projective_source (K := K) σ AR
            p.1.pair.1.2.1.1 p.1.pair.1.1.1.2 p.2.1
            p.1.target_nonprojective hne hwt,
          not_hom_second_source_first_source (K := K) σ AR
            p.1.pair.1.1.1.1 p.1.pair.1.2.1.1 p.1.pair.1.1.1.2
            p.1.pair.1.1.2 hwt,
          not_hom_target_projective_source (K := K) σ AR
            p.1.pair.1.1.1.1 p.1.pair.1.1.1.2 p.1.first_projective
            p.1.target_nonprojective hne p.1.pair.1.1.2⟩
    have houter : hookM6InjectiveFourthToOuterPair (σ := σ) (AR := AR)
        M = p.1 := congrArg Subtype.val hM
    have hcp : M.1.commonTargetPair σ AR = p.1.pair :=
      (hookM6InjectiveFourthToOuterPair_pair_eq σ AR M).symm.trans
        (congrArg FirstProjectiveInjectiveDifferentOrbitOuterPair.pair
          houter)
    have hanchor := congrArg
      (fun q : CommonTargetArrowPair σ ↦ q.1.2.1.1) hcp
    change (M.1.1.triple.hookOrbitAnchor σ AR).1.1 =
      p.1.pair.1.2.1.1 at hanchor
    refine ⟨⟨M, ?_⟩, ?_⟩
    · rw [hanchor]
      exact p.2.1
    · apply Subtype.ext
      apply FirstProjectiveInjectiveDifferentOrbitOuterPair.ext
      exact (HookM6Channel.InjectiveFourthProjectiveAnchor.toHookWallBadU_commonTargetPair
        (K := K) σ AR ⟨M, by rw [hanchor]; exact p.2.1⟩).trans hcp

include K in
/-- The second-boundary `M6` overlap uses exactly the
interior-two-source occurrences whose common target is noninjective. -/
theorem mem_firstPISecondInteriorM6Image_iff
    (p : AR.FirstPISecondInteriorTwoSourceOuterPair σ) :
    p ∈ AR.FirstPISecondInteriorM6Image (K := K) σ ↔
      ¬ Injective (σ.obj p.outer.pair.1.1.1.2) := by
  constructor
  · rintro ⟨M, rfl⟩
    intro hI
    apply hookM6InjectiveFourthToOuterPair_target_noninjective σ AR
      M.1.1
    rw [hookM6InjectiveFourthToOuterPair_pair_eq σ AR M.1.1,
      ← HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary.toHookWallBadB_commonTargetPair
        (K := K) σ AR M]
    exact hI
  · intro htNI
    have hwt : HasIrreducibleMorphism
        (σ.obj p.outer.pair.1.2.1.1) (σ.obj p.outer.pair.1.1.1.2) := by
      have h := p.outer.pair.1.2.2
      rw [← p.outer.pair.2] at h
      exact h
    have htvP :=
      (firstPISecond_twoSource_iff_translatedTarget_projective σ AR
        p.outer p.second_nonprojective p.second_noninjective).1
        p.second_twoSource
    have hne : p.outer.pair.1.1.1.2 ≠
        (AR.arTranslation σ
          ⟨p.outer.pair.1.1.1.2, p.outer.target_nonprojective⟩).1 := by
      intro hfix
      apply p.outer.target_nonprojective
      rw [hfix]
      exact htvP
    obtain ⟨M, hM⟩ :=
      (mem_range_hookM6InjectiveFourthToTargetNoninjectiveCell_iff_normalized
        (K := K) σ AR ⟨p.outer, p.second_noninjective, htNI⟩).2
        ⟨(target_ne_outerCellLast_iff σ AR
            ⟨p.outer, p.second_noninjective, htNI⟩).2 hne,
          not_hom_target_source_of_translatedTarget_projective
            (K := K) σ AR p.outer.pair.1.2.1.1 p.outer.pair.1.1.1.2
            p.second_nonprojective p.outer.target_nonprojective htvP hwt,
          not_hom_second_source_first_source (K := K) σ AR
            p.outer.pair.1.1.1.1 p.outer.pair.1.2.1.1
            p.outer.pair.1.1.1.2 p.outer.pair.1.1.2 hwt,
          not_hom_target_projective_source (K := K) σ AR
            p.outer.pair.1.1.1.1 p.outer.pair.1.1.1.2
            p.outer.first_projective p.outer.target_nonprojective hne
            p.outer.pair.1.1.2⟩
    have houter : hookM6InjectiveFourthToOuterPair (σ := σ) (AR := AR)
        M = p.outer := congrArg Subtype.val hM
    have hcp : M.1.commonTargetPair σ AR = p.outer.pair :=
      (hookM6InjectiveFourthToOuterPair_pair_eq σ AR M).symm.trans
        (congrArg FirstProjectiveInjectiveDifferentOrbitOuterPair.pair
          houter)
    have hanchor := congrArg
      (fun q : CommonTargetArrowPair σ ↦ q.1.2.1.1) hcp
    change (M.1.1.triple.hookOrbitAnchor σ AR).1.1 =
      p.outer.pair.1.2.1.1 at hanchor
    have harrow := congrArg
      (fun q : CommonTargetArrowPair σ ↦ q.1.2) hcp
    change M.1.1.triple.hookOrbitAnchor σ AR =
      p.outer.pair.1.2 at harrow
    have hNPA : ¬ Projective (σ.obj
        (M.1.1.triple.hookOrbitAnchor σ AR).1.1) := by
      rw [hanchor]
      exact p.second_nonprojective
    have hTS : ((AR.arMeshRotationData σ).arrowInteriorOrbitData
        σ).TwoSource
      (toInteriorArrow σ AR (M.1.1.triple.hookOrbitAnchor σ AR)
        (M.1.hookOrbitAnchor_isInterior σ AR)) := by
      convert p.second_twoSource using 1
      apply Subtype.ext
      exact harrow
    refine ⟨⟨⟨M, hNPA⟩, hTS⟩, ?_⟩
    apply FirstPISecondInteriorTwoSourceOuterPair.ext
    apply FirstProjectiveInjectiveDifferentOrbitOuterPair.ext
    exact (HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary.toHookWallBadB_commonTargetPair
      (K := K) σ AR ⟨⟨M, hNPA⟩, hTS⟩).trans hcp

/-- Projective-second occurrences surviving the `M6` overlap: the
common target is injective. -/
abbrev WallSecondProjectiveTargetInjectivePair :=
  {p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair σ //
    Projective (σ.obj p.pair.1.2.1.1) ∧
      ¬ Injective (σ.obj p.pair.1.2.1.1) ∧
      Injective (σ.obj p.pair.1.1.1.2)}

/-- Injective-second occurrences with projective translated target, in
crossing-aligned conjunct order. -/
abbrev WallSecondInjectiveTranslatedTargetProjectivePair :=
  {p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair σ //
    Injective (σ.obj p.pair.1.2.1.1) ∧
      ¬ Projective (σ.obj p.pair.1.2.1.1) ∧
      Projective (σ.obj (AR.arTranslation σ
        ⟨p.pair.1.1.1.2, p.target_nonprojective⟩).1)}

/-- Interior-two-source occurrences surviving the `M6` overlap, in
translated-target form: both the translated target is projective and
the common target is injective. -/
abbrev WallSecondInteriorTargetInjectivePair :=
  {p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair σ //
    ¬ Projective (σ.obj p.pair.1.2.1.1) ∧
      ¬ Injective (σ.obj p.pair.1.2.1.1) ∧
      Projective (σ.obj (AR.arTranslation σ
        ⟨p.pair.1.1.1.2, p.target_nonprojective⟩).1) ∧
      Injective (σ.obj p.pair.1.1.1.2)}

noncomputable instance wallSecondProjectiveTargetInjectivePairFintype :
    Fintype (AR.WallSecondProjectiveTargetInjectivePair σ) :=
  Fintype.ofFinite _

noncomputable instance
    wallSecondInjectiveTranslatedTargetProjectivePairFintype :
    Fintype (AR.WallSecondInjectiveTranslatedTargetProjectivePair σ) :=
  Fintype.ofFinite _

noncomputable instance wallSecondInteriorTargetInjectivePairFintype :
    Fintype (AR.WallSecondInteriorTargetInjectivePair σ) :=
  Fintype.ofFinite _

/-- The unused projective-second complement is the injective-target part
of its stratum. -/
def firstPISecondProjectiveM6ComplementEquivWall :
    AR.FirstPISecondProjectiveM6Complement (K := K) σ ≃
      AR.WallSecondProjectiveTargetInjectivePair σ where
  toFun q :=
    ⟨q.1.1, q.1.2.1, q.1.2.2, by
      by_contra h
      exact q.2
        ((mem_firstPISecondProjectiveM6Image_iff (K := K) σ AR q.1).2 h)⟩
  invFun p :=
    ⟨⟨p.1, p.2.1, p.2.2.1⟩, fun hmem ↦
      (mem_firstPISecondProjectiveM6Image_iff (K := K) σ AR
        ⟨p.1, p.2.1, p.2.2.1⟩).1 hmem p.2.2.2⟩
  left_inv q := Subtype.ext (Subtype.ext rfl)
  right_inv p := Subtype.ext rfl

/-- The unused interior-two-source complement is the injective-target
part of its stratum, in translated-target form. -/
def firstPISecondInteriorM6ComplementEquivWall :
    AR.FirstPISecondInteriorM6Complement (K := K) σ ≃
      AR.WallSecondInteriorTargetInjectivePair σ where
  toFun q :=
    ⟨q.1.outer, q.1.second_nonprojective, q.1.second_noninjective,
      (firstPISecond_twoSource_iff_translatedTarget_projective σ AR
        q.1.outer q.1.second_nonprojective q.1.second_noninjective).1
        q.1.second_twoSource, by
      by_contra h
      exact q.2
        ((mem_firstPISecondInteriorM6Image_iff (K := K) σ AR q.1).2 h)⟩
  invFun p :=
    ⟨{ outer := p.1
       second_nonprojective := p.2.1
       second_noninjective := p.2.2.1
       second_twoSource :=
         (firstPISecond_twoSource_iff_translatedTarget_projective σ AR
           p.1 p.2.1 p.2.2.1).2 p.2.2.2.1 },
     fun hmem ↦
      (mem_firstPISecondInteriorM6Image_iff (K := K) σ AR _).1 hmem
        p.2.2.2.2⟩
  left_inv q := Subtype.ext
    (FirstPISecondInteriorTwoSourceOuterPair.ext rfl)
  right_inv p := Subtype.ext rfl

/-- The translated-target stratum in crossing-aligned subtype form. -/
def firstPISecondInjectiveTranslatedTargetProjectiveEquivWall :
    AR.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair σ ≃
      AR.WallSecondInjectiveTranslatedTargetProjectivePair σ where
  toFun q :=
    ⟨q.outer, q.second_injective, q.second_nonprojective,
      q.translatedTarget_projective⟩
  invFun p :=
    { outer := p.1
      second_nonprojective := p.2.2.1
      second_injective := p.2.1
      translatedTarget_projective := p.2.2.2 }
  left_inv _ :=
    FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair.ext rfl
  right_inv _ := Subtype.ext rfl

include K in
/-- Cardinality of the unused `M2` complement in wall-stratum form. -/
theorem hookWallBadU_M6ProjectiveAnchorComplement_card_eq_wall :
    Fintype.card
        (HookWallBadU.M6ProjectiveAnchorComplement (K := K) σ AR) =
      Fintype.card (AR.WallSecondProjectiveTargetInjectivePair σ) :=
  Fintype.card_congr
    ((hookWallBadUM6ProjectiveAnchorComplementEquivIntrinsic
      (K := K) σ AR).trans
      (firstPISecondProjectiveM6ComplementEquivWall (K := K) σ AR))

include K in
/-- Cardinality of the unused `M3` complement in wall-stratum form. -/
theorem hookWallBadB_M6SecondBoundaryComplement_card_eq_wall :
    Fintype.card
        (HookWallBadBUnrestricted.M6SecondBoundaryComplement
          (K := K) σ AR) =
      Fintype.card (AR.WallSecondInteriorTargetInjectivePair σ) +
        Fintype.card
          (AR.WallSecondInjectiveTranslatedTargetProjectivePair σ) := by
  rw [Fintype.card_congr
    ((hookWallBadBM6SecondBoundaryComplementEquivIntrinsicSumTranslatedTarget
      (K := K) σ AR).trans
      (Equiv.sumCongr
        (firstPISecondInteriorM6ComplementEquivWall (K := K) σ AR)
        (firstPISecondInjectiveTranslatedTargetProjectiveEquivWall
          σ AR)))]
  exact Fintype.card_sum

end FiniteARTranslationData

namespace AlignedBiduality

/-- The aligned crossing carries the surviving projective-second wall
stratum onto the opposite translated-target stratum. -/
def wallSecondProjectiveTargetInjectiveEquivAligned
    (D : AlignedBiduality σ τ)
    (ARsigma : σ.FiniteARTranslationData)
    (ARtau : τ.FiniteARTranslationData) :
    ARsigma.WallSecondProjectiveTargetInjectivePair σ ≃
      ARtau.WallSecondInjectiveTranslatedTargetProjectivePair τ :=
  (D.firstPIOuterEquivAligned σ τ ARsigma ARtau).subtypeEquiv fun p ↦
    and_congr
      (D.firstPIOuterEquivAligned_second_projective_iff_injective
        σ τ ARsigma ARtau p)
      (and_congr
        (not_congr
          (D.firstPIOuterEquivAligned_second_injective_iff_projective
            σ τ ARsigma ARtau p))
        (D.firstPIOuterEquivAligned_translatedTarget_projective_iff_target_injective
          σ τ ARsigma ARtau p).symm)

/-- The aligned crossing carries the translated-target stratum onto the
opposite surviving projective-second wall stratum. -/
def wallSecondInjectiveTranslatedTargetProjectiveEquivAligned
    (D : AlignedBiduality σ τ)
    (ARsigma : σ.FiniteARTranslationData)
    (ARtau : τ.FiniteARTranslationData) :
    ARsigma.WallSecondInjectiveTranslatedTargetProjectivePair σ ≃
      ARtau.WallSecondProjectiveTargetInjectivePair τ :=
  (D.firstPIOuterEquivAligned σ τ ARsigma ARtau).subtypeEquiv fun p ↦
    and_congr
      (D.firstPIOuterEquivAligned_second_injective_iff_projective
        σ τ ARsigma ARtau p)
      (and_congr
        (not_congr
          (D.firstPIOuterEquivAligned_second_projective_iff_injective
            σ τ ARsigma ARtau p))
        (D.firstPIOuterEquivAligned_target_injective_iff_translatedTarget_projective
          σ τ ARsigma ARtau p).symm)

/-- The aligned crossing carries the surviving interior-two-source wall
stratum onto its opposite counterpart. -/
def wallSecondInteriorTargetInjectiveEquivAligned
    (D : AlignedBiduality σ τ)
    (ARsigma : σ.FiniteARTranslationData)
    (ARtau : τ.FiniteARTranslationData) :
    ARsigma.WallSecondInteriorTargetInjectivePair σ ≃
      ARtau.WallSecondInteriorTargetInjectivePair τ :=
  (D.firstPIOuterEquivAligned σ τ ARsigma ARtau).subtypeEquiv fun p ↦ by
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨(not_congr
          (D.firstPIOuterEquivAligned_second_injective_iff_projective
            σ τ ARsigma ARtau p)).1 h2,
        (not_congr
          (D.firstPIOuterEquivAligned_second_projective_iff_injective
            σ τ ARsigma ARtau p)).1 h1,
        (D.firstPIOuterEquivAligned_translatedTarget_projective_iff_target_injective
          σ τ ARsigma ARtau p).2 h4,
        (D.firstPIOuterEquivAligned_target_injective_iff_translatedTarget_projective
          σ τ ARsigma ARtau p).2 h3⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨(not_congr
          (D.firstPIOuterEquivAligned_second_projective_iff_injective
            σ τ ARsigma ARtau p)).2 h2,
        (not_congr
          (D.firstPIOuterEquivAligned_second_injective_iff_projective
            σ τ ARsigma ARtau p)).2 h1,
        (D.firstPIOuterEquivAligned_target_injective_iff_translatedTarget_projective
          σ τ ARsigma ARtau p).1 h4,
        (D.firstPIOuterEquivAligned_translatedTarget_projective_iff_target_injective
          σ τ ARsigma ARtau p).1 h3⟩

include K in
/-- The unused wall sum `M2 complement + M3 complement` is reversal
invariant: the three surviving wall strata permute under the aligned
crossing. -/
theorem wall_sum_reversal_invariant
    (D : AlignedBiduality σ τ)
    (ARsigma : σ.FiniteARTranslationData)
    (ARtau : τ.FiniteARTranslationData) :
    Fintype.card
        (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
          (K := K) τ ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
          (K := K) τ ARtau) =
    Fintype.card
        (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
          (K := K) σ ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
          (K := K) σ ARsigma) := by
  rw [FiniteARTranslationData.hookWallBadU_M6ProjectiveAnchorComplement_card_eq_wall
      (K := K) σ ARsigma,
    FiniteARTranslationData.hookWallBadU_M6ProjectiveAnchorComplement_card_eq_wall
      (K := K) τ ARtau,
    FiniteARTranslationData.hookWallBadB_M6SecondBoundaryComplement_card_eq_wall
      (K := K) σ ARsigma,
    FiniteARTranslationData.hookWallBadB_M6SecondBoundaryComplement_card_eq_wall
      (K := K) τ ARtau]
  have e1 := Fintype.card_congr
    (D.wallSecondProjectiveTargetInjectiveEquivAligned σ τ
      ARsigma ARtau)
  have e2 := Fintype.card_congr
    (D.wallSecondInjectiveTranslatedTargetProjectiveEquivAligned σ τ
      ARsigma ARtau)
  have e3 := Fintype.card_congr
    (D.wallSecondInteriorTargetInjectiveEquivAligned σ τ
      ARsigma ARtau)
  omega

end AlignedBiduality

end OpConjecture.IndecomposableSkeleton
