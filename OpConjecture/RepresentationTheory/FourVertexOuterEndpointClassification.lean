import OpConjecture.RepresentationTheory.FourVertexOuterEndpointOccurrences
import OpConjecture.RepresentationTheory.FourVertexDiagonalM4RegularCuts

/-!
# Intrinsic classification of the outer four-vertex endpoints

The surviving outer-channel terms are most useful only after their labelled
common-target occurrences have been characterized intrinsically.  This file
starts that characterization in an oriented form: the first arrow is the
one whose source is projective-injective.  The ordering is essential for the
crossed endpoint balance.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton.FiniteARTranslationData

universe u v

variable {K R : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R]
  {iota : Type v} [Fintype iota] [DecidableEq iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)
  (AR : sigma.FiniteARTranslationData)

/-- An ordered different-component common-target occurrence whose target is
nonprojective and whose first source is simultaneously projective and
injective. -/
@[ext]
structure FirstProjectiveInjectiveDifferentOrbitOuterPair where
  pair : CommonTargetArrowPair sigma
  target_nonprojective : ¬ Projective (sigma.obj pair.1.1.1.2)
  first_projective : Projective (sigma.obj pair.1.1.1.1)
  first_injective : Injective (sigma.obj pair.1.1.1.1)
  differentOrbit :
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit pair.1.1 pair.1.2

noncomputable instance firstProjectiveInjectiveDifferentOrbitOuterPairFinite :
    Finite (AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma) :=
  Finite.of_injective
    (fun p ↦ p.pair) (by
      intro p q h
      exact FirstProjectiveInjectiveDifferentOrbitOuterPair.ext h)

noncomputable instance firstProjectiveInjectiveDifferentOrbitOuterPairFintype :
    Fintype (AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma) :=
  Fintype.ofFinite _

/-- The oriented outer stratum in which the second source is projective but
noninjective. -/
abbrev FirstPISecondProjectiveNoninjectiveOuterPair :=
  {p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma //
    Projective (sigma.obj p.pair.1.2.1.1) ∧
      ¬ Injective (sigma.obj p.pair.1.2.1.1)}

noncomputable instance firstPISecondProjectiveNoninjectiveOuterPairFintype :
    Fintype (AR.FirstPISecondProjectiveNoninjectiveOuterPair sigma) :=
  Fintype.ofFinite _

namespace HookWallBadU.InjectiveFourthEndpoint

variable (W : HookWallBadU.InjectiveFourthEndpoint sigma AR)

/-- An outer `M2` endpoint, with its oriented intrinsic endpoint data. -/
def firstPISecondProjectiveNoninjectiveOuterPair :
    AR.FirstPISecondProjectiveNoninjectiveOuterPair sigma := by
  let p := W.1.commonTargetPair sigma AR
  let P : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma :=
    { pair := p
      target_nonprojective := by
        simpa [p, HookWallBadU.commonTargetPair,
          HookWallBadU.associatedArrow] using
            W.1.1.triple.u_nonprojective
      first_projective := by
        simpa [p, HookWallBadU.commonTargetPair,
          HookWallBadU.associatedArrow] using W.1.1.z_projective
      first_injective := by
        simpa [p, HookWallBadU.commonTargetPair,
          HookWallBadU.associatedArrow] using W.2
      differentOrbit := W.commonTargetPair_differentOrbit sigma AR }
  refine ⟨P, ?_, ?_⟩
  · simpa [P, p, HookWallBadU.commonTargetPair,
      StripAdmissibleTriple.firstArrow] using W.1.1.a_projective
  · simpa [P, p, HookWallBadU.commonTargetPair,
      StripAdmissibleTriple.firstArrow] using
        W.1.1.triple.a_noninjective sigma AR

omit [DecidableEq iota] in
/-- The oriented intrinsic `M2` occurrence retains the wall term. -/
theorem firstPISecondProjectiveNoninjectiveOuterPair_injective :
    Function.Injective
      (firstPISecondProjectiveNoninjectiveOuterPair sigma AR) := by
  intro W Z h
  apply Subtype.ext
  apply HookWallBadU.commonTargetPair_injective sigma AR
  exact congrArg (fun p ↦ p.1.pair) h

end HookWallBadU.InjectiveFourthEndpoint

namespace FirstPISecondProjectiveNoninjectiveOuterPair

variable (p : AR.FirstPISecondProjectiveNoninjectiveOuterPair sigma)

include K AR in
/-- Reconstruct the unique outer `M2` wall term from its second arrow. -/
def toHookWallBadU : HookWallBadU.InjectiveFourthEndpoint sigma AR := by
  let q := p.1.pair.1.2
  let T := AR.stripTripleOfProjectiveArrow (k := K) sigma q
    p.2.1 p.2.2 (by
      simpa only [p.1.pair.2] using p.1.target_nonprojective)
  let W₀ : AR.HookWallChoice sigma :=
    { triple := T
      a_projective := p.2.1
      z := p.1.pair.1.1.1.1
      z_projective := p.1.first_projective }
  let W : AR.HookWallBadU sigma := ⟨W₀, by
    change HasIrreducibleMorphism
      (sigma.obj p.1.pair.1.1.1.1) (sigma.obj T.u)
    have hTu : T.u = q.1.2 := by rfl
    rw [hTu, ← p.1.pair.2]
    exact p.1.pair.1.1.2⟩
  exact ⟨W, p.1.first_injective⟩

include K AR in
omit [DecidableEq iota] in
/-- Reconstruction preserves the complete ordered common-target
occurrence. -/
theorem toHookWallBadU_commonTargetPair :
    (p.toHookWallBadU (K := K) sigma AR).1.commonTargetPair sigma AR =
      p.1.pair := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact p.1.pair.2.symm
  · exact AR.stripTripleOfProjectiveArrow_firstArrow
      (k := K) sigma p.1.pair.1.2 p.2.1 p.2.2 (by
        simpa only [p.1.pair.2] using p.1.target_nonprojective)

end FirstPISecondProjectiveNoninjectiveOuterPair

include K AR in
/-- Outer `M2` endpoints are exactly the oriented intrinsic endpoint stratum
whose second source is projective and noninjective. -/
def hookWallBadUInjectiveFourthEquivFirstPISecondProjectiveNoninjective :
    HookWallBadU.InjectiveFourthEndpoint sigma AR ≃
      AR.FirstPISecondProjectiveNoninjectiveOuterPair sigma where
  toFun W := W.firstPISecondProjectiveNoninjectiveOuterPair sigma AR
  invFun p := p.toHookWallBadU (K := K) sigma AR
  left_inv W := by
    apply HookWallBadU.InjectiveFourthEndpoint.firstPISecondProjectiveNoninjectiveOuterPair_injective
      sigma AR
    apply Subtype.ext
    apply FirstProjectiveInjectiveDifferentOrbitOuterPair.ext
    exact (W.firstPISecondProjectiveNoninjectiveOuterPair sigma AR).toHookWallBadU_commonTargetPair
      (K := K) sigma AR
  right_inv p := by
    apply Subtype.ext
    apply FirstProjectiveInjectiveDifferentOrbitOuterPair.ext
    exact p.toHookWallBadU_commonTargetPair (K := K) sigma AR

/-- The part of injective-first outer `M3` whose second source is still
noninjective, so that its second arrow survives the trimmed boundary. -/
abbrev HookWallBadBUnrestricted.InjectiveFirstSecondNoninjective :=
  {W : HookWallBadBUnrestricted.InjectiveEndpointFirstInjective sigma AR //
    ¬ Injective (sigma.obj W.1.1.1.triple.u)}

noncomputable instance
    hookWallBadBUnrestrictedInjectiveFirstSecondNoninjectiveFintype :
    Fintype
      (HookWallBadBUnrestricted.InjectiveFirstSecondNoninjective
        sigma AR) :=
  Fintype.ofFinite _

/-- The terminal-source part of injective-first outer `M3`: its second
source is injective as well. -/
abbrev HookWallBadBUnrestricted.InjectiveFirstSecondInjective :=
  {W : HookWallBadBUnrestricted.InjectiveEndpointFirstInjective sigma AR //
    Injective (sigma.obj W.1.1.1.triple.u)}

noncomputable instance
    hookWallBadBUnrestrictedInjectiveFirstSecondInjectiveFintype :
    Fintype
      (HookWallBadBUnrestricted.InjectiveFirstSecondInjective sigma AR) :=
  Fintype.ofFinite _

/-- Split injective-first outer `M3` exactly according to whether its
second arrow survives deletion of injective-source boundary arrows. -/
def hookWallBadBInjectiveFirstEquivSecondNoninjectiveSumInjective :
    HookWallBadBUnrestricted.InjectiveEndpointFirstInjective sigma AR ≃
      HookWallBadBUnrestricted.InjectiveFirstSecondNoninjective sigma AR ⊕
        HookWallBadBUnrestricted.InjectiveFirstSecondInjective sigma AR where
  toFun W := by
    classical
    by_cases h : Injective (sigma.obj W.1.1.1.triple.u)
    · exact Sum.inr ⟨W, h⟩
    · exact Sum.inl ⟨W, h⟩
  invFun W := by
    rcases W with W | W
    · exact W.1
    · exact W.1
  left_inv W := by
    classical
    by_cases h : Injective (sigma.obj W.1.1.1.triple.u)
    · simp [h]
    · simp [h]
  right_inv W := by
    classical
    rcases W with W | W
    · simp [W.2]
    · simp [W.2]

/-- An oriented outer occurrence whose second source is nonprojective and
noninjective and whose second arrow belongs to the first two layers of its
trimmed mesh-rotation chain. -/
@[ext]
structure FirstPISecondInteriorTwoSourceOuterPair where
  outer : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma
  second_nonprojective : ¬ Projective (sigma.obj outer.pair.1.2.1.1)
  second_noninjective : ¬ Injective (sigma.obj outer.pair.1.2.1.1)
  second_twoSource :
    ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      (toInteriorArrow sigma AR outer.pair.1.2
        ⟨by
          rw [← outer.pair.2]
          exact outer.target_nonprojective,
        second_noninjective⟩)

noncomputable instance firstPISecondInteriorTwoSourceOuterPairFinite :
    Finite (AR.FirstPISecondInteriorTwoSourceOuterPair sigma) :=
  Finite.of_injective
    (fun p ↦ p.outer.pair) (by
      intro p q h
      apply FirstPISecondInteriorTwoSourceOuterPair.ext
      exact FirstProjectiveInjectiveDifferentOrbitOuterPair.ext h)

noncomputable instance firstPISecondInteriorTwoSourceOuterPairFintype :
    Fintype (AR.FirstPISecondInteriorTwoSourceOuterPair sigma) :=
  Fintype.ofFinite _

/-- An oriented outer occurrence whose second source is injective and
nonprojective, while the AR translate of the common target is projective.
This is the untrimmed endpoint analogue of the second-source-boundary
condition. -/
@[ext]
structure FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair where
  outer : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma
  second_nonprojective : ¬ Projective (sigma.obj outer.pair.1.2.1.1)
  second_injective : Injective (sigma.obj outer.pair.1.2.1.1)
  translatedTarget_projective : Projective
    (sigma.obj (AR.arTranslation sigma
      ⟨outer.pair.1.1.1.2, outer.target_nonprojective⟩).1)

noncomputable instance
    firstPISecondInjectiveTranslatedTargetProjectiveOuterPairFinite :
    Finite
      (AR.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair
        sigma) :=
  Finite.of_injective
    (fun p ↦ p.outer.pair) (by
      intro p q h
      apply FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair.ext
      exact FirstProjectiveInjectiveDifferentOrbitOuterPair.ext h)

noncomputable instance
    firstPISecondInjectiveTranslatedTargetProjectiveOuterPairFintype :
    Fintype
      (AR.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair
        sigma) :=
  Fintype.ofFinite _

/-- An oriented outer occurrence with no projective source: its first source
is noninjective, its second source is injective, and the AR translate of the
nonprojective common target is projective.  Unlike the projective-injective
first-source strata above, this type does not impose a component condition. -/
@[ext]
structure FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair where
  pair : CommonTargetArrowPair sigma
  target_nonprojective : ¬ Projective (sigma.obj pair.1.1.1.2)
  first_nonprojective : ¬ Projective (sigma.obj pair.1.1.1.1)
  first_noninjective : ¬ Injective (sigma.obj pair.1.1.1.1)
  second_nonprojective : ¬ Projective (sigma.obj pair.1.2.1.1)
  second_injective : Injective (sigma.obj pair.1.2.1.1)
  translatedTarget_projective : Projective
    (sigma.obj (AR.arTranslation sigma
      ⟨pair.1.1.1.2, target_nonprojective⟩).1)

noncomputable instance
    firstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPairFinite :
    Finite
      (AR.FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair
        sigma) :=
  Finite.of_injective
    (fun p ↦ p.pair) (by
      intro p q h
      exact
        FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair.ext
          h)

noncomputable instance
    firstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPairFintype :
    Fintype
      (AR.FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair
        sigma) :=
  Fintype.ofFinite _

namespace HookWallBadBUnrestricted.InjectiveFirstSecondNoninjective

variable
  (W : HookWallBadBUnrestricted.InjectiveFirstSecondNoninjective sigma AR)

/-- A surviving injective-first outer `M3` endpoint, with its oriented
intrinsic second-boundary data. -/
def firstPISecondInteriorTwoSourceOuterPair :
    AR.FirstPISecondInteriorTwoSourceOuterPair sigma := by
  let p := W.1.1.1.commonTargetPair sigma AR
  let P : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma :=
    { pair := p
      target_nonprojective := by
        simpa [p, HookWallBadBUnrestricted.commonTargetPair,
          HookWallBadBUnrestricted.associatedArrow] using
            W.1.1.1.1.triple.b_nonprojective
      first_projective := by
        simpa [p, HookWallBadBUnrestricted.commonTargetPair,
          HookWallBadBUnrestricted.associatedArrow] using
            W.1.1.1.1.z_projective
      first_injective := by
        simpa [p, HookWallBadBUnrestricted.commonTargetPair,
          HookWallBadBUnrestricted.associatedArrow] using W.1.2
      differentOrbit := W.1.commonTargetPair_differentOrbit sigma AR }
  refine
    { outer := P
      second_nonprojective := by
        simpa [P, p, HookWallBadBUnrestricted.commonTargetPair,
          StripAdmissibleTriple.secondArrow] using
            W.1.1.1.1.triple.u_nonprojective
      second_noninjective := by
        simpa [P, p, HookWallBadBUnrestricted.commonTargetPair,
          StripAdmissibleTriple.secondArrow] using W.2
      second_twoSource := ?_ }
  have htwo := W.1.1.1.1.triple.secondArrow_interior_twoSource
    sigma AR W.1.1.1.1.a_projective W.2
  convert htwo using 1
  apply Subtype.ext
  rfl

omit [DecidableEq iota] in
/-- The intrinsic second-boundary occurrence retains its outer `M3` term. -/
theorem firstPISecondInteriorTwoSourceOuterPair_injective :
    Function.Injective
      (firstPISecondInteriorTwoSourceOuterPair sigma AR) := by
  intro W Z h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply HookWallBadBUnrestricted.commonTargetPair_injective sigma AR
  exact congrArg (fun p ↦ p.outer.pair) h

end HookWallBadBUnrestricted.InjectiveFirstSecondNoninjective

namespace HookWallBadBUnrestricted.InjectiveFirstSecondInjective

variable
  (W : HookWallBadBUnrestricted.InjectiveFirstSecondInjective sigma AR)

/-- An injective-second-source outer `M3` endpoint, with the projective
translate of its common target recorded intrinsically. -/
def firstPISecondInjectiveTranslatedTargetProjectiveOuterPair :
    AR.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair sigma := by
  let p := W.1.1.1.commonTargetPair sigma AR
  let P : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma :=
    { pair := p
      target_nonprojective := by
        simpa [p, HookWallBadBUnrestricted.commonTargetPair,
          HookWallBadBUnrestricted.associatedArrow] using
            W.1.1.1.1.triple.b_nonprojective
      first_projective := by
        simpa [p, HookWallBadBUnrestricted.commonTargetPair,
          HookWallBadBUnrestricted.associatedArrow] using
            W.1.1.1.1.z_projective
      first_injective := by
        simpa [p, HookWallBadBUnrestricted.commonTargetPair,
          HookWallBadBUnrestricted.associatedArrow] using W.1.2
      differentOrbit := W.1.commonTargetPair_differentOrbit sigma AR }
  refine
    { outer := P
      second_nonprojective := by
        simpa [P, p, HookWallBadBUnrestricted.commonTargetPair,
          StripAdmissibleTriple.secondArrow] using
            W.1.1.1.1.triple.u_nonprojective
      second_injective := by
        simpa [P, p, HookWallBadBUnrestricted.commonTargetPair,
          StripAdmissibleTriple.secondArrow] using W.2
      translatedTarget_projective := ?_ }
  have htau := W.1.1.1.1.triple.tau_b
  simpa [P, p, HookWallBadBUnrestricted.commonTargetPair,
    HookWallBadBUnrestricted.associatedArrow] using
      (show Projective
        (sigma.obj
          (AR.arTranslation sigma
            ⟨W.1.1.1.1.triple.b,
              W.1.1.1.1.triple.b_nonprojective⟩).1) by
        rw [htau]
        exact W.1.1.1.1.a_projective)

omit [DecidableEq iota] in
/-- The translated-target occurrence retains its injective-second-source
outer `M3` term. -/
theorem
    firstPISecondInjectiveTranslatedTargetProjectiveOuterPair_injective :
    Function.Injective
      (firstPISecondInjectiveTranslatedTargetProjectiveOuterPair
        sigma AR) := by
  intro W Z h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply HookWallBadBUnrestricted.commonTargetPair_injective sigma AR
  exact congrArg (fun p ↦ p.outer.pair) h

end HookWallBadBUnrestricted.InjectiveFirstSecondInjective

namespace FirstPISecondInteriorTwoSourceOuterPair

variable (p : AR.FirstPISecondInteriorTwoSourceOuterPair sigma)

include K AR in
/-- Reconstruct the unique injective-first outer `M3` term from the second
trimmed source-boundary occurrence. -/
def toHookWallBadB :
    HookWallBadBUnrestricted.InjectiveFirstSecondNoninjective sigma AR := by
  let H := toInteriorArrow sigma AR p.outer.pair.1.2
    ⟨by
      rw [← p.outer.pair.2]
      exact p.outer.target_nonprojective,
    p.second_noninjective⟩
  let S := AR.sourceBoundaryHook (k := K) sigma H p.second_twoSource
  have hsecond : p.outer.pair.1.2 = S.triple.secondArrow sigma AR := by
    rcases S.hookArrow_eq with hfirst | hsecond
    · exfalso
      apply p.second_nonprojective
      have hs := congrArg
        (fun q : sigma.IrreduciblePair ↦ q.1.1) hfirst
      change p.outer.pair.1.2.1.1 = S.triple.a at hs
      rw [hs]
      exact S.a_projective
    · exact hsecond
  have htarget : p.outer.pair.1.2.1.2 = S.triple.b := by
    rw [hsecond]
    rfl
  let W₀ : AR.HookWallChoice sigma :=
    { triple := S.triple
      a_projective := S.a_projective
      z := p.outer.pair.1.1.1.1
      z_projective := p.outer.first_projective }
  let W : AR.HookWallBadBUnrestricted sigma := ⟨W₀, by
    change HasIrreducibleMorphism
      (sigma.obj p.outer.pair.1.1.1.1) (sigma.obj S.triple.b)
    rw [← htarget, ← p.outer.pair.2]
    exact p.outer.pair.1.1.2⟩
  exact ⟨⟨⟨W, Or.inl p.outer.first_injective⟩,
    p.outer.first_injective⟩, by
      change ¬ Injective (sigma.obj S.triple.u)
      intro hI
      apply p.second_noninjective
      have hs := congrArg
        (fun q : sigma.IrreduciblePair ↦ q.1.1) hsecond
      rw [hs]
      exact hI⟩

include K AR in
omit [DecidableEq iota] in
/-- The outer `M3` reconstruction preserves the complete ordered
common-target occurrence. -/
theorem toHookWallBadB_commonTargetPair :
    (p.toHookWallBadB (K := K) sigma AR).1.1.1.commonTargetPair sigma AR =
      p.outer.pair := by
  let H := toInteriorArrow sigma AR p.outer.pair.1.2
    ⟨by
      rw [← p.outer.pair.2]
      exact p.outer.target_nonprojective,
    p.second_noninjective⟩
  let S := AR.sourceBoundaryHook (k := K) sigma H p.second_twoSource
  have hsecond : p.outer.pair.1.2 = S.triple.secondArrow sigma AR := by
    rcases S.hookArrow_eq with hfirst | hsecond
    · exfalso
      apply p.second_nonprojective
      have hs := congrArg
        (fun q : sigma.IrreduciblePair ↦ q.1.1) hfirst
      change p.outer.pair.1.2.1.1 = S.triple.a at hs
      rw [hs]
      exact S.a_projective
    · exact hsecond
  have htarget : p.outer.pair.1.2.1.2 = S.triple.b := by
    rw [hsecond]
    rfl
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact htarget.symm.trans p.outer.pair.2.symm
  · exact hsecond.symm

end FirstPISecondInteriorTwoSourceOuterPair

namespace FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair

variable
  (p : AR.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair sigma)

include K AR in
/-- Reconstruct the unique injective-second-source outer `M3` term from the
projective translate of its common target. -/
def toHookWallBadB :
    HookWallBadBUnrestricted.InjectiveFirstSecondInjective sigma AR := by
  let bLabel : sigma.NonprojectiveLabel :=
    ⟨p.outer.pair.1.1.1.2, p.outer.target_nonprojective⟩
  let a := (AR.arTranslation sigma bLabel).1
  let u := p.outer.pair.1.2.1.1
  have huB : HasIrreducibleMorphism (sigma.obj u) (sigma.obj bLabel.1) := by
    change HasIrreducibleMorphism
      (sigma.obj p.outer.pair.1.2.1.1)
        (sigma.obj p.outer.pair.1.1.1.2)
    rw [p.outer.pair.2]
    exact p.outer.pair.1.2.2
  have haU : HasIrreducibleMorphism (sigma.obj a) (sigma.obj u) := by
    exact (AR.arTranslation_incidence sigma bLabel u).1 huB
  let q : sigma.IrreduciblePair := ⟨(a, u), haU⟩
  let T := AR.stripTripleOfProjectiveArrow (k := K) sigma q
    p.translatedTarget_projective
    (AR.arTranslation sigma bLabel).2
    p.second_nonprojective
  have hTb : T.b = bLabel.1 := by
    change ((AR.arTranslationEquiv sigma).symm
      ⟨(AR.arTranslation sigma bLabel).1,
        (AR.arTranslation sigma bLabel).2⟩).1 = bLabel.1
    exact congrArg Subtype.val
      ((AR.arTranslationEquiv sigma).symm_apply_apply bLabel)
  have hsecond : T.secondArrow sigma AR = p.outer.pair.1.2 := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hTb.trans p.outer.pair.2
  let W₀ : AR.HookWallChoice sigma :=
    { triple := T
      a_projective := p.translatedTarget_projective
      z := p.outer.pair.1.1.1.1
      z_projective := p.outer.first_projective }
  let W : AR.HookWallBadBUnrestricted sigma := ⟨W₀, by
    change HasIrreducibleMorphism
      (sigma.obj p.outer.pair.1.1.1.1) (sigma.obj T.b)
    rw [hTb]
    exact p.outer.pair.1.1.2⟩
  exact ⟨⟨⟨W, Or.inl p.outer.first_injective⟩,
    p.outer.first_injective⟩, by
      change Injective (sigma.obj T.u)
      exact p.second_injective⟩

include K AR in
omit [DecidableEq iota] in
/-- The injective-second-source reconstruction preserves the complete
ordered common-target occurrence. -/
theorem toHookWallBadB_commonTargetPair :
    (p.toHookWallBadB (K := K) sigma AR).1.1.1.commonTargetPair sigma AR =
      p.outer.pair := by
  let bLabel : sigma.NonprojectiveLabel :=
    ⟨p.outer.pair.1.1.1.2, p.outer.target_nonprojective⟩
  let a := (AR.arTranslation sigma bLabel).1
  let u := p.outer.pair.1.2.1.1
  have huB : HasIrreducibleMorphism (sigma.obj u) (sigma.obj bLabel.1) := by
    change HasIrreducibleMorphism
      (sigma.obj p.outer.pair.1.2.1.1)
        (sigma.obj p.outer.pair.1.1.1.2)
    rw [p.outer.pair.2]
    exact p.outer.pair.1.2.2
  have haU : HasIrreducibleMorphism (sigma.obj a) (sigma.obj u) := by
    exact (AR.arTranslation_incidence sigma bLabel u).1 huB
  let q : sigma.IrreduciblePair := ⟨(a, u), haU⟩
  let T := AR.stripTripleOfProjectiveArrow (k := K) sigma q
    p.translatedTarget_projective
    (AR.arTranslation sigma bLabel).2
    p.second_nonprojective
  have hTb : T.b = bLabel.1 := by
    change ((AR.arTranslationEquiv sigma).symm
      ⟨(AR.arTranslation sigma bLabel).1,
        (AR.arTranslation sigma bLabel).2⟩).1 = bLabel.1
    exact congrArg Subtype.val
      ((AR.arTranslationEquiv sigma).symm_apply_apply bLabel)
  have hsecond : T.secondArrow sigma AR = p.outer.pair.1.2 := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hTb.trans p.outer.pair.2
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hTb
  · exact hsecond

end FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair

include K AR in
/-- Injective-first outer `M3` endpoints with noninjective second source are
exactly the oriented intrinsic second trimmed source-boundary stratum. -/
def hookWallBadBInjectiveFirstSecondNoninjectiveEquivFirstPISecondInteriorTwoSource :
    HookWallBadBUnrestricted.InjectiveFirstSecondNoninjective sigma AR ≃
      AR.FirstPISecondInteriorTwoSourceOuterPair sigma where
  toFun W := W.firstPISecondInteriorTwoSourceOuterPair sigma AR
  invFun p := p.toHookWallBadB (K := K) sigma AR
  left_inv W := by
    apply HookWallBadBUnrestricted.InjectiveFirstSecondNoninjective.firstPISecondInteriorTwoSourceOuterPair_injective
      sigma AR
    apply FirstPISecondInteriorTwoSourceOuterPair.ext
    apply FirstProjectiveInjectiveDifferentOrbitOuterPair.ext
    exact (W.firstPISecondInteriorTwoSourceOuterPair sigma AR).toHookWallBadB_commonTargetPair
      (K := K) sigma AR
  right_inv p := by
    apply FirstPISecondInteriorTwoSourceOuterPair.ext
    apply FirstProjectiveInjectiveDifferentOrbitOuterPair.ext
    exact p.toHookWallBadB_commonTargetPair (K := K) sigma AR

include K AR in
/-- Injective-first outer `M3` endpoints with injective second source are
exactly the oriented intrinsic stratum with projective translated common
target. -/
def hookWallBadBInjectiveFirstSecondInjectiveEquivTranslatedTargetProjective :
    HookWallBadBUnrestricted.InjectiveFirstSecondInjective sigma AR ≃
      AR.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair
        sigma where
  toFun W :=
    W.firstPISecondInjectiveTranslatedTargetProjectiveOuterPair sigma AR
  invFun p := p.toHookWallBadB (K := K) sigma AR
  left_inv W := by
    apply HookWallBadBUnrestricted.InjectiveFirstSecondInjective.firstPISecondInjectiveTranslatedTargetProjectiveOuterPair_injective
      sigma AR
    apply FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair.ext
    apply FirstProjectiveInjectiveDifferentOrbitOuterPair.ext
    exact (W.firstPISecondInjectiveTranslatedTargetProjectiveOuterPair
      sigma AR).toHookWallBadB_commonTargetPair (K := K) sigma AR
  right_inv p := by
    apply FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair.ext
    apply FirstProjectiveInjectiveDifferentOrbitOuterPair.ext
    exact p.toHookWallBadB_commonTargetPair (K := K) sigma AR

include K AR in
/-- Complete intrinsic classification of injective-first outer `M3`: its
second arrow either survives in the first two trimmed source layers or has
injective source and projective translated common target. -/
def hookWallBadBInjectiveFirstEquivIntrinsicSecondEndpointSum :
    HookWallBadBUnrestricted.InjectiveEndpointFirstInjective sigma AR ≃
      AR.FirstPISecondInteriorTwoSourceOuterPair sigma ⊕
        AR.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair
          sigma :=
  (hookWallBadBInjectiveFirstEquivSecondNoninjectiveSumInjective
      sigma AR).trans <|
    Equiv.sumCongr
      (hookWallBadBInjectiveFirstSecondNoninjectiveEquivFirstPISecondInteriorTwoSource
        (K := K) sigma AR)
      (hookWallBadBInjectiveFirstSecondInjectiveEquivTranslatedTargetProjective
        (K := K) sigma AR)

namespace HookM5Preliminary.InjectiveMiddleNoProjectiveFirst

variable
  (M : HookM5Preliminary.InjectiveMiddleNoProjectiveFirst sigma AR)

/-- The unused outer `M5` endpoint in intrinsic ordered common-target
coordinates. -/
def firstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair :
    AR.FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair
      sigma := by
  let p := M.1.1.commonTargetPair sigma AR
  refine
    { pair := p
      target_nonprojective := by
        change ¬ Projective
          (sigma.obj (M.1.1.rotatedAssociatedArrow sigma AR).1.2)
        rw [M.1.1.rotatedAssociatedArrow_target_eq_hookArrow_target
          sigma AR]
        exact M.1.1.hookArrow_target_nonprojective sigma AR
      first_nonprojective := by
        simpa [p, HookM5Preliminary.commonTargetPair] using M.2
      first_noninjective := by
        simpa [p, HookM5Preliminary.commonTargetPair] using
          (M.1.1.rotatedAssociatedArrow_isInterior sigma AR).2
      second_nonprojective := by
        simpa [p, HookM5Preliminary.commonTargetPair,
          HookM5Preliminary.hookArrow, M.1.2.1,
          StripAdmissibleTriple.secondArrow] using
            M.1.1.triple.u_nonprojective
      second_injective := by
        simpa [p, HookM5Preliminary.commonTargetPair,
          HookM5Preliminary.hookArrow, M.1.2.1,
          StripAdmissibleTriple.secondArrow] using M.1.2.2
      translatedTarget_projective := by
        have hb : p.1.1.1.2 = M.1.1.triple.b := by
          change
            (M.1.1.rotatedAssociatedArrow sigma AR).1.2 =
              M.1.1.triple.b
          rw [M.1.1.rotatedAssociatedArrow_target_eq_hookArrow_target
            sigma AR]
          simp [HookM5Preliminary.hookArrow, M.1.2.1,
            StripAdmissibleTriple.secondArrow]
        let bLabel : sigma.NonprojectiveLabel :=
          ⟨p.1.1.1.2, by
            change ¬ Projective
              (sigma.obj (M.1.1.rotatedAssociatedArrow sigma AR).1.2)
            rw [M.1.1.rotatedAssociatedArrow_target_eq_hookArrow_target
              sigma AR]
            exact M.1.1.hookArrow_target_nonprojective sigma AR⟩
        have hbLabel : bLabel =
            ⟨M.1.1.triple.b,
              M.1.1.triple.b_nonprojective⟩ :=
          Subtype.ext hb
        have htau := M.1.1.triple.tau_b
        change Projective
          (sigma.obj (AR.arTranslation sigma bLabel).1)
        rw [hbLabel, htau]
        exact M.1.1.a_projective }

/-- The intrinsic ordered occurrence retains the no-projective outer `M5`
term. -/
theorem
    firstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair_injective :
    Function.Injective
      (firstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair
        sigma AR) := by
  intro M N h
  apply Subtype.ext
  apply Subtype.ext
  apply HookM5Preliminary.commonTargetPair_injective sigma AR
  exact congrArg
    FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair.pair
      h

end HookM5Preliminary.InjectiveMiddleNoProjectiveFirst

namespace FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair

variable
  (p : AR.FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair
    sigma)

structure HookM5PreliminaryReconstruction where
  term : HookM5Preliminary.InjectiveMiddleNoProjectiveFirst sigma AR
  occurrence_eq : term.1.1.commonTargetPair sigma AR = p.pair

include K AR in
/-- Reconstruct the unique no-projective outer `M5` term from its intrinsic
ordered common-target occurrence. -/
def hookM5PreliminaryReconstruction :
    p.HookM5PreliminaryReconstruction sigma AR := by
  let bLabel : sigma.NonprojectiveLabel :=
    ⟨p.pair.1.1.1.2, p.target_nonprojective⟩
  let a := (AR.arTranslation sigma bLabel).1
  let u := p.pair.1.2.1.1
  have huB : HasIrreducibleMorphism (sigma.obj u) (sigma.obj bLabel.1) := by
    change HasIrreducibleMorphism
      (sigma.obj p.pair.1.2.1.1) (sigma.obj p.pair.1.1.1.2)
    rw [p.pair.2]
    exact p.pair.1.2.2
  have haU : HasIrreducibleMorphism (sigma.obj a) (sigma.obj u) :=
    (AR.arTranslation_incidence sigma bLabel u).1 huB
  let q : sigma.IrreduciblePair := ⟨(a, u), haU⟩
  let T := AR.stripTripleOfProjectiveArrow (k := K) sigma q
    p.translatedTarget_projective
    (AR.arTranslation sigma bLabel).2
    p.second_nonprojective
  have hTb : T.b = bLabel.1 := by
    change ((AR.arTranslationEquiv sigma).symm
      ⟨(AR.arTranslation sigma bLabel).1,
        (AR.arTranslation sigma bLabel).2⟩).1 = bLabel.1
    exact congrArg Subtype.val
      ((AR.arTranslationEquiv sigma).symm_apply_apply bLabel)
  let x := p.pair.1.1.1.1
  let zLabel : sigma.NonprojectiveLabel :=
    (AR.arTranslationEquiv sigma).symm ⟨x, p.first_noninjective⟩
  let z := zLabel.1
  have htauZ : (AR.arTranslation sigma zLabel).1 = x := by
    exact congrArg Subtype.val
      ((AR.arTranslationEquiv sigma).apply_symm_apply
        ⟨x, p.first_noninjective⟩)
  have hbZ : HasIrreducibleMorphism (sigma.obj bLabel.1) (sigma.obj z) := by
    apply (AR.arTranslation_incidence sigma zLabel bLabel.1).2
    rw [htauZ]
    exact p.pair.1.1.2
  have hTbZ : HasIrreducibleMorphism (sigma.obj T.b) (sigma.obj z) := by
    rw [hTb]
    exact hbZ
  have hzNot : z ∉ T.support := by
    simp only [StripAdmissibleTriple.support, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩
    · intro hza
      apply zLabel.2
      have hTa : T.a = a := rfl
      have hTaP : Projective (sigma.obj T.a) := by
        rw [hTa]
        exact p.translatedTarget_projective
      have hzP : Projective (sigma.obj z) := hza.symm ▸ hTaP
      simpa only [z] using hzP
    · intro hzu
      apply T.b_not_to_u
      simpa only [hzu] using hTbZ
    · intro hzb
      exact sigma.hasNoIrreducibleEndomorphism_obj T.b (by
        simpa only [hzb] using hTbZ)
  have huNotZ : ¬ HasIrreducibleMorphism
      (sigma.obj T.u) (sigma.obj z) := by
    intro huZ
    exact AR.no_irreducible_transitiveTriangle
      (K := K) sigma T.u_to_b hTbZ huZ
  let P : AR.HookM5Preliminary sigma :=
    { triple := T
      a_projective := p.translatedTarget_projective
      z := z
      z_not_mem := hzNot
      z_nonprojective := zLabel.2
      outgoing_to_z := Or.inr hTbZ }
  have hhook : P.hookArrow sigma AR = T.secondArrow sigma AR := by
    simp [P, HookM5Preliminary.hookArrow, huNotZ]
  have hassociated : P.associatedArrow sigma AR =
      (⟨(T.b, z), hTbZ⟩ : sigma.IrreduciblePair) := by
    apply Subtype.ext
    simp [P, HookM5Preliminary.associatedArrow, huNotZ]
  have hrotated : P.rotatedAssociatedArrow sigma AR = p.pair.1.1 := by
    let zLabel' : sigma.NonprojectiveLabel :=
      ⟨z, P.z_nonprojective⟩
    have hzLabel : zLabel' = zLabel := Subtype.ext rfl
    let associatedTargetLabel : sigma.NonprojectiveLabel :=
      ⟨(P.associatedArrow sigma AR).1.2, by
        simpa only [P.associatedArrow_target sigma AR] using
          P.z_nonprojective⟩
    have hassociatedTargetLabel : associatedTargetLabel = zLabel' := by
      apply Subtype.ext
      exact P.associatedArrow_target sigma AR
    have hval :=
      (AR.arMeshRotationData sigma).arrowOrbitData_tau_val sigma
        ⟨P.associatedArrow sigma AR, by
          simpa only [P.associatedArrow_target sigma AR] using
            P.z_nonprojective⟩
    have hsource := congrArg Prod.fst hval
    change (P.rotatedAssociatedArrow sigma AR).1.1 =
      (AR.arTranslation sigma associatedTargetLabel).1 at hsource
    apply Subtype.ext
    apply Prod.ext
    · calc
        (P.rotatedAssociatedArrow sigma AR).1.1 =
            (AR.arTranslation sigma associatedTargetLabel).1 := hsource
        _ = (AR.arTranslation sigma zLabel').1 := by
          rw [hassociatedTargetLabel]
        _ = x := by rw [hzLabel, htauZ]
        _ = p.pair.1.1.1.1 := rfl
    · calc
        (P.rotatedAssociatedArrow sigma AR).1.2 =
            (P.associatedArrow sigma AR).1.1 :=
          congrArg Prod.snd hval
        _ = T.b := congrArg (fun r : sigma.IrreduciblePair ↦ r.1.1)
          hassociated
        _ = p.pair.1.1.1.2 := hTb
  have hsecond : P.hookArrow sigma AR = p.pair.1.2 := by
    rw [hhook]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hTb.trans p.pair.2
  let X : HookM5Preliminary.InjectiveMiddleEndpoint sigma AR :=
    ⟨P, huNotZ, p.second_injective⟩
  let Y : HookM5Preliminary.InjectiveMiddleNoProjectiveFirst sigma AR :=
    ⟨X, by
      change ¬ Projective
        (sigma.obj (P.rotatedAssociatedArrow sigma AR).1.1)
      rw [hrotated]
      exact p.first_nonprojective⟩
  refine ⟨Y, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hrotated
  · exact hsecond

include K AR in
/-- The term underlying the intrinsic no-projective outer `M5`
reconstruction. -/
def toHookM5Preliminary :
    HookM5Preliminary.InjectiveMiddleNoProjectiveFirst sigma AR :=
  (p.hookM5PreliminaryReconstruction (K := K) sigma AR).term

include K AR in
/-- Reconstruction preserves the complete ordered common-target
occurrence. -/
theorem toHookM5Preliminary_commonTargetPair :
    (p.toHookM5Preliminary (K := K) sigma AR).1.1.commonTargetPair
        sigma AR = p.pair :=
  (p.hookM5PreliminaryReconstruction (K := K) sigma AR).occurrence_eq

end FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair

include K AR in
/-- No-projective outer `M5` endpoints are exactly the intrinsic ordered
noninjective/injective-source stratum with projective translated target. -/
def hookM5NoProjectiveFirstEquivIntrinsic :
    HookM5Preliminary.InjectiveMiddleNoProjectiveFirst sigma AR ≃
      AR.FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair
        sigma where
  toFun M :=
    M.firstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair
      sigma AR
  invFun p := p.toHookM5Preliminary (K := K) sigma AR
  left_inv M := by
    apply HookM5Preliminary.InjectiveMiddleNoProjectiveFirst.firstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair_injective
      sigma AR
    apply
      FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair.ext
    exact
      (M.firstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair
        sigma AR).toHookM5Preliminary_commonTargetPair
          (K := K) sigma AR
  right_inv p := by
    apply
      FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair.ext
    exact p.toHookM5Preliminary_commonTargetPair (K := K) sigma AR

/-- Different-component part of the intrinsic no-projective outer `M5`
endpoint. -/
abbrev FirstNISINoProjectiveDifferentOrbitOuterPair :=
  {p :
      AR.FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair
        sigma //
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit p.pair.1.1 p.pair.1.2}

/-- Same-component part of the intrinsic no-projective outer `M5`
endpoint.  This subtype is retained explicitly rather than being silently
discarded from the different-component endpoint equation. -/
abbrev FirstNISINoProjectiveSameOrbitOuterPair :=
  {p :
      AR.FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair
        sigma //
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    O.SameSuccessorOrbit p.pair.1.1 p.pair.1.2}

noncomputable instance firstNISINoProjectiveDifferentOrbitOuterPairFintype :
    Fintype (AR.FirstNISINoProjectiveDifferentOrbitOuterPair sigma) :=
  Fintype.ofFinite _

noncomputable instance firstNISINoProjectiveSameOrbitOuterPairFintype :
    Fintype (AR.FirstNISINoProjectiveSameOrbitOuterPair sigma) :=
  Fintype.ofFinite _

omit [DecidableEq iota] in
/-- The apparent same-component branch is empty.  If `u → b` is the
second arrow, then `u` is injective and the two preceding mesh rotations
end respectively at `u` and at the projective label `τ b`.  Thus these
three occurrences are the whole successor component.  A further occurrence
with target `b` can coincide with none of them. -/
theorem FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair.not_sameOrbit
    (p : AR.FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair
      sigma) :
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit p.pair.1.1 p.pair.1.2 := by
  classical
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let A := p.pair.1.1
  let B := p.pair.1.2
  let Bsub : {q : sigma.IrreduciblePair //
      ¬ Projective (sigma.obj q.1.2)} :=
    ⟨B, by
      change ¬ Projective (sigma.obj p.pair.1.2.1.2)
      rw [← p.pair.2]
      exact p.target_nonprojective⟩
  let q₁sub := O.tau Bsub
  let q₁ := q₁sub.1
  have hq₁Target : q₁.1.2 = B.1.1 := by
    exact congrArg Prod.snd (M.arrowOrbitData_tau_val sigma Bsub)
  have hq₁TargetNonprojective : ¬ Projective (sigma.obj q₁.1.2) := by
    rw [hq₁Target]
    exact p.second_nonprojective
  let q₁np : {q : sigma.IrreduciblePair //
      ¬ Projective (sigma.obj q.1.2)} :=
    ⟨q₁, hq₁TargetNonprojective⟩
  let q₀sub := O.tau q₁np
  let q₀ := q₀sub.1
  have hq₀Target : q₀.1.2 = q₁.1.1 := by
    exact congrArg Prod.snd (M.arrowOrbitData_tau_val sigma q₁np)
  have hq₁Source : q₁.1.1 =
      (AR.arTranslation sigma
        ⟨p.pair.1.1.1.2, p.target_nonprojective⟩).1 := by
    have hsource := congrArg Prod.fst
      (M.arrowOrbitData_tau_val sigma Bsub)
    change q₁.1.1 = (AR.arTranslation sigma
      ⟨B.1.2, Bsub.2⟩).1 at hsource
    calc
      q₁.1.1 = (AR.arTranslation sigma ⟨B.1.2, Bsub.2⟩).1 :=
        hsource
      _ = (AR.arTranslation sigma
          ⟨p.pair.1.1.1.2, p.target_nonprojective⟩).1 := by
        congr 2
        apply Subtype.ext
        exact p.pair.2.symm
  have hq₀SourceBoundary : Projective (sigma.obj q₀.1.2) := by
    rw [hq₀Target, hq₁Source]
    exact p.translatedTarget_projective
  have hsucc₀ : O.successor q₀ = q₁ := by
    change O.successor q₀sub.1 = q₁
    rw [show O.successor q₀sub.1 =
        (O.tau.symm ⟨q₀sub.1, q₀sub.2⟩).1 by
      simp [OpConjecture.BoundaryTranslationChains.Data.successor,
        q₀sub.2]]
    exact congrArg Subtype.val (O.tau.symm_apply_apply q₁np)
  have hsucc₁ : O.successor q₁ = B := by
    change O.successor q₁sub.1 = B
    rw [show O.successor q₁sub.1 =
        (O.tau.symm ⟨q₁sub.1, q₁sub.2⟩).1 by
      simp [OpConjecture.BoundaryTranslationChains.Data.successor,
        q₁sub.2]]
    exact congrArg Subtype.val (O.tau.symm_apply_apply Bsub)
  have hq₀B : O.SameSuccessorOrbit q₀ B := by
    refine ⟨2, 0, ?_⟩
    simp only [Function.iterate_succ_apply,
      Function.iterate_zero, id_eq, hsucc₀, hsucc₁]
  change ¬ O.SameSuccessorOrbit A B
  intro hAB
  have hq₀A : O.SameSuccessorOrbit q₀ A :=
    O.sameSuccessorOrbit_trans hq₀B
      (O.sameSuccessorOrbit_symm hAB)
  obtain ⟨r, hr⟩ :=
    O.exists_iterate_eq_of_mem_source_of_sameSuccessorOrbit
      hq₀SourceBoundary hq₀A
  rcases r with _ | r
  · apply p.target_nonprojective
    have ht := congrArg (fun q : sigma.IrreduciblePair ↦ q.1.2) hr
    change q₀.1.2 = A.1.2 at ht
    rw [← ht]
    exact hq₀SourceBoundary
  · rcases r with _ | r
    · have hr₁ : O.successor q₀ = A := by
        simpa using hr
      have ht := congrArg (fun q : sigma.IrreduciblePair ↦ q.1.2) hr₁
      have hub : B.1.1 = B.1.2 := by
        calc
          B.1.1 = q₁.1.2 := hq₁Target.symm
          _ = A.1.2 := by
            rw [← hsucc₀]
            exact ht
          _ = B.1.2 := p.pair.2
      exact sigma.hasNoIrreducibleEndomorphism_obj B.1.2 (by
        simpa only [hub] using B.2)
    · have hiter : (O.successor^[Nat.succ (Nat.succ r)]) q₀ = B := by
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
          hsucc₀, hsucc₁]
        exact O.iterate_eq_self_of_mem_target B p.second_injective r
      have hBA : B = A := hiter.symm.trans hr
      have hs := congrArg
        (fun q : sigma.IrreduciblePair ↦ q.1.1) hBA
      apply p.first_noninjective
      rw [← hs]
      exact p.second_injective

omit [DecidableEq iota] in
/-- Consequently the same-component subtype of the intrinsic outer `M5`
endpoint is empty. -/
theorem firstNISINoProjectiveSameOrbitOuterPair_isEmpty :
    IsEmpty (AR.FirstNISINoProjectiveSameOrbitOuterPair sigma) :=
  ⟨fun p ↦
    p.1.not_sameOrbit sigma AR p.2⟩

/-- Exhaustive intrinsic component split of the no-projective outer `M5`
endpoint. -/
def firstNISINoProjectiveEquivDifferentOrbitSumSameOrbit :
    AR.FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair
        sigma ≃
      AR.FirstNISINoProjectiveDifferentOrbitOuterPair sigma ⊕
        AR.FirstNISINoProjectiveSameOrbitOuterPair sigma where
  toFun p := by
    classical
    by_cases h :
        ((AR.arMeshRotationData sigma).arrowOrbitData sigma).SameSuccessorOrbit
          p.pair.1.1 p.pair.1.2
    · exact Sum.inr ⟨p, h⟩
    · exact Sum.inl ⟨p, h⟩
  invFun p := by
    rcases p with p | p
    · exact p.1
    · exact p.1
  left_inv p := by
    classical
    by_cases h :
        ((AR.arMeshRotationData sigma).arrowOrbitData sigma).SameSuccessorOrbit
          p.pair.1.1 p.pair.1.2
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.2]
    · simp [p.2]

omit [DecidableEq iota] in
/-- After the empty same-component branch is removed, every intrinsic
no-projective outer `M5` endpoint lies on two different arrow components. -/
def firstNISINoProjectiveEquivDifferentOrbit :
    AR.FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair
        sigma ≃
      AR.FirstNISINoProjectiveDifferentOrbitOuterPair sigma := by
  letI : IsEmpty (AR.FirstNISINoProjectiveSameOrbitOuterPair sigma) :=
    AR.firstNISINoProjectiveSameOrbitOuterPair_isEmpty sigma
  exact (AR.firstNISINoProjectiveEquivDifferentOrbitSumSameOrbit
    sigma).trans (Equiv.sumEmpty _ _)

include K AR in
/-- The actual no-projective outer `M5` family splits exactly into its
different- and same-component intrinsic endpoint parts. -/
def hookM5NoProjectiveFirstEquivDifferentOrbitSumSameOrbit :
    HookM5Preliminary.InjectiveMiddleNoProjectiveFirst sigma AR ≃
      AR.FirstNISINoProjectiveDifferentOrbitOuterPair sigma ⊕
        AR.FirstNISINoProjectiveSameOrbitOuterPair sigma :=
  (hookM5NoProjectiveFirstEquivIntrinsic (K := K) sigma AR).trans
    (AR.firstNISINoProjectiveEquivDifferentOrbitSumSameOrbit sigma)

include K AR in
omit [DecidableEq iota] in
/-- Exact intrinsic different-component classification of every actual
no-projective outer `M5` term. -/
def hookM5NoProjectiveFirstEquivDifferentOrbit :
    HookM5Preliminary.InjectiveMiddleNoProjectiveFirst sigma AR ≃
      AR.FirstNISINoProjectiveDifferentOrbitOuterPair sigma :=
  (hookM5NoProjectiveFirstEquivIntrinsic (K := K) sigma AR).trans
    (AR.firstNISINoProjectiveEquivDifferentOrbit sigma)

namespace FirstNISINoProjectiveDifferentOrbitOuterPair

variable (p : AR.FirstNISINoProjectiveDifferentOrbitOuterPair sigma)

/-- Forget the refined orientation while retaining the corresponding full
different-component injective-source/no-projective-source endpoint. -/
def differentOrbitInjectiveSourceNoProjectivePair :
    AR.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
      sigma :=
  ⟨⟨⟨p.1.pair, Or.inr p.1.second_injective⟩,
      not_or_intro p.1.first_nonprojective p.1.second_nonprojective⟩,
    p.2⟩

omit [DecidableEq iota] in
/-- The full endpoint occurrence retains the oriented intrinsic `M5`
coordinates. -/
theorem differentOrbitInjectiveSourceNoProjectivePair_injective :
    Function.Injective
      (differentOrbitInjectiveSourceNoProjectivePair sigma AR) := by
  intro p q h
  apply Subtype.ext
  apply
    FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair.ext
  exact congrArg
    (fun r :
      AR.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
        sigma ↦ r.1.1.1) h

end FirstNISINoProjectiveDifferentOrbitOuterPair

/-- Exact occurrence image of the different-component part of the
no-projective outer `M5` endpoint inside the full injective-source endpoint. -/
abbrev FirstNISINoProjectiveDifferentOrbitImage :=
  Set.range
    (FirstNISINoProjectiveDifferentOrbitOuterPair.differentOrbitInjectiveSourceNoProjectivePair
      sigma AR)

noncomputable instance firstNISINoProjectiveDifferentOrbitImageFintype :
    Fintype (AR.FirstNISINoProjectiveDifferentOrbitImage sigma) :=
  Fintype.ofFinite _

/-- The refined different-component intrinsic `M5` stratum is exactly
equivalent to its full-endpoint occurrence image. -/
def firstNISINoProjectiveDifferentOrbitEquivImage :
    AR.FirstNISINoProjectiveDifferentOrbitOuterPair sigma ≃
      AR.FirstNISINoProjectiveDifferentOrbitImage sigma :=
  Equiv.ofInjective
    (FirstNISINoProjectiveDifferentOrbitOuterPair.differentOrbitInjectiveSourceNoProjectivePair
      sigma AR)
    (FirstNISINoProjectiveDifferentOrbitOuterPair.differentOrbitInjectiveSourceNoProjectivePair_injective
      sigma AR)

namespace DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair

variable
  (p : AR.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
    sigma)

omit [DecidableEq iota] in
include K in
/-- A common target admitting an arrow from an injective source cannot be
projective. -/
theorem target_nonprojective :
    ¬ Projective (sigma.obj p.1.1.1.1.1.1.2) := by
  intro hP
  rcases p.1.1.2 with hI | hI
  · exact arrowToProjective_source_noninjective
      (K := K) sigma p.1.1.1.1.1 hP hI
  · apply arrowToProjective_source_noninjective
      (K := K) sigma p.1.1.1.1.2
    · rw [← p.1.1.1.2]
      exact hP
    · exact hI

end DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair

omit [DecidableEq iota] in
/-- Intrinsic membership criterion for the exact no-projective outer `M5`
image.  Inside the full different-component injective-source endpoint, the
image consists precisely of the orientation in which only the second source
is injective and the translate of the common target is projective. -/
theorem mem_firstNISINoProjectiveDifferentOrbitImage_iff
    (p : AR.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
      sigma) :
    p ∈ AR.FirstNISINoProjectiveDifferentOrbitImage sigma ↔
      ¬ Injective (sigma.obj p.1.1.1.1.1.1.1) ∧
        Injective (sigma.obj p.1.1.1.1.2.1.1) ∧
          Projective
            (sigma.obj (AR.arTranslation sigma
              ⟨p.1.1.1.1.1.1.2,
                p.target_nonprojective (K := K) sigma⟩).1) := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1.first_noninjective, q.1.second_injective,
      q.1.translatedTarget_projective⟩
  · rintro ⟨hfirstNI, hsecondI, htranslatedP⟩
    have htargetNP := p.target_nonprojective (K := K) sigma
    let q₀ :
        AR.FirstNoninjectiveSecondInjectiveTranslatedTargetProjectiveOuterPair
          sigma :=
      { pair := p.1.1.1
        target_nonprojective := htargetNP
        first_nonprojective := fun hP ↦ p.1.2 (Or.inl hP)
        first_noninjective := hfirstNI
        second_nonprojective := fun hP ↦ p.1.2 (Or.inr hP)
        second_injective := hsecondI
        translatedTarget_projective := htranslatedP }
    let q : AR.FirstNISINoProjectiveDifferentOrbitOuterPair sigma :=
      ⟨q₀, p.2⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The complementary orientation in the full no-projective endpoint: the
first source is injective. -/
abbrev DifferentOrbitNoProjectiveFirstInjectivePair :=
  {p : AR.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
      sigma //
    Injective (sigma.obj p.1.1.1.1.1.1.1)}

/-- Complementary orientation in which the first source remains
noninjective (and hence the second source is injective). -/
abbrev DifferentOrbitNoProjectiveFirstNoninjectivePair :=
  {p : AR.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
      sigma //
    ¬ Injective (sigma.obj p.1.1.1.1.1.1.1)}

/-- The genuinely deeper part of the first-noninjective orientation: the
translate of the common target is still nonprojective. -/
abbrev DifferentOrbitNoProjectiveFirstNoninjectiveDeepPair :=
  {p : AR.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
      sigma //
    ¬ Injective (sigma.obj p.1.1.1.1.1.1.1) ∧
      ¬ Projective
        (sigma.obj (AR.arTranslation sigma
          ⟨p.1.1.1.1.1.1.2,
            p.target_nonprojective (K := K) sigma⟩).1)}

/-- Dual source-coordinate form of the full no-projective endpoint: at
least one arrow ends at a projective, while both arrow targets are
noninjective. -/
abbrev DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair :=
  {p : AR.DifferentOrbitProjectiveTargetCommonSourcePair sigma //
    ¬ Injective (sigma.obj p.1.1.1.1.1.2) ∧
      ¬ Injective (sigma.obj p.1.1.1.2.1.2)}

/-- Orientation in which the first common-source arrow is the one ending
at a projective. -/
abbrev DifferentOrbitFirstProjectiveTargetNoninjectiveCommonSourcePair :=
  {p : AR.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair
      sigma //
    Projective (sigma.obj p.1.1.1.1.1.1.2)}

/-- Complementary orientation: the first target is nonprojective, so the
second common-source arrow is the projective-target occurrence. -/
abbrev DifferentOrbitFirstNonprojectiveTargetNoninjectiveCommonSourcePair :=
  {p : AR.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair
      sigma //
    ¬ Projective (sigma.obj p.1.1.1.1.1.1.2)}

namespace DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair

variable
  (p : AR.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair
    sigma)

omit [DecidableEq iota] in
include K in
/-- The common source is noninjective: one of its two arrows ends at a
projective. -/
theorem source_noninjective :
    ¬ Injective (sigma.obj p.1.1.1.1.1.1.1) := by
  rcases p.1.1.2 with hP | hP
  · exact arrowToProjective_source_noninjective
      (K := K) sigma p.1.1.1.1.1 hP
  · rw [p.1.1.1.2]
    exact arrowToProjective_source_noninjective
      (K := K) sigma p.1.1.1.1.2 hP

include K AR in
/-- The inverse AR translate of the common source, defined canonically from
the projective-target endpoint condition. -/
def inverseCommonSource : sigma.NonprojectiveLabel :=
  (AR.arTranslationEquiv sigma).symm
    ⟨p.1.1.1.1.1.1.1, p.source_noninjective (K := K) sigma⟩

end DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair

/-- In the first-nonprojective-target orientation, the inverse translate of
the common source is injective. -/
abbrev DifferentOrbitFirstNonprojectiveTargetInverseInjectiveCommonSourcePair :=
  {p : AR.DifferentOrbitFirstNonprojectiveTargetNoninjectiveCommonSourcePair
      sigma //
    Injective
      (sigma.obj (p.1.inverseCommonSource (K := K) sigma AR).1)}

/-- Complementary first-nonprojective-target source coordinate: the inverse
translate of the common source remains noninjective. -/
abbrev DifferentOrbitFirstNonprojectiveTargetInverseNoninjectiveCommonSourcePair :=
  {p : AR.DifferentOrbitFirstNonprojectiveTargetNoninjectiveCommonSourcePair
      sigma //
    ¬ Injective
      (sigma.obj (p.1.inverseCommonSource (K := K) sigma AR).1)}

omit [DecidableEq iota] in
include K AR in
/-- Advancing both arrows from a projective-target common-source endpoint
produces a trimmed literal-source common-target pair.  The hypotheses that
both old targets are noninjective are exactly what makes the two advanced
arrows interior. -/
def differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivFullOrbitLiteral :
    AR.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair sigma ≃
      AR.FullOrbitDifferentInteriorLiteralSourceCommonTargetPair sigma := by
  classical
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let forward :
      AR.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair sigma →
        AR.FullOrbitDifferentInteriorLiteralSourceCommonTargetPair sigma :=
    fun p ↦ by
      let pair : CommonSourceArrowPair sigma := p.1.1.1
      have hfirstSourceNI :
          ¬ Injective (sigma.obj pair.1.1.1.1) := by
        exact p.source_noninjective (K := K) sigma
      have hsecondSourceNI :
          ¬ Injective (sigma.obj pair.1.2.1.1) := by
        rw [← pair.2]
        exact hfirstSourceNI
      let firstRaw := (O.tau.symm ⟨pair.1.1, hfirstSourceNI⟩).1
      let secondRaw := (O.tau.symm ⟨pair.1.2, hsecondSourceNI⟩).1
      have hfirstVal := M.arrowOrbitData_tau_symm_val sigma
        ⟨pair.1.1, hfirstSourceNI⟩
      have hsecondVal := M.arrowOrbitData_tau_symm_val sigma
        ⟨pair.1.2, hsecondSourceNI⟩
      have hfirstNP : ¬ Projective (sigma.obj firstRaw.1.2) := by
        change ¬ Projective
          (sigma.obj
            ((AR.arTranslationEquiv sigma).symm
              ⟨pair.1.1.1.1, hfirstSourceNI⟩).1)
        exact
          ((AR.arTranslationEquiv sigma).symm
            ⟨pair.1.1.1.1, hfirstSourceNI⟩).2
      have hsecondNP : ¬ Projective (sigma.obj secondRaw.1.2) := by
        change ¬ Projective
          (sigma.obj
            ((AR.arTranslationEquiv sigma).symm
              ⟨pair.1.2.1.1, hsecondSourceNI⟩).1)
        exact
          ((AR.arTranslationEquiv sigma).symm
            ⟨pair.1.2.1.1, hsecondSourceNI⟩).2
      have hfirstNI : ¬ Injective (sigma.obj firstRaw.1.1) := by
        rw [show firstRaw.1.1 = pair.1.1.1.2 from
          congrArg Prod.fst hfirstVal]
        exact p.2.1
      have hsecondNI : ¬ Injective (sigma.obj secondRaw.1.1) := by
        rw [show secondRaw.1.1 = pair.1.2.1.2 from
          congrArg Prod.fst hsecondVal]
        exact p.2.2
      let first := toInteriorArrow sigma AR firstRaw ⟨hfirstNP, hfirstNI⟩
      let second := toInteriorArrow sigma AR secondRaw ⟨hsecondNP, hsecondNI⟩
      have htarget : first.1.1.2 = second.1.1.2 := by
        change firstRaw.1.2 = secondRaw.1.2
        rw [show firstRaw.1.2 =
              ((AR.arTranslationEquiv sigma).symm
                ⟨pair.1.1.1.1, hfirstSourceNI⟩).1 from
            congrArg Prod.snd hfirstVal,
          show secondRaw.1.2 =
              ((AR.arTranslationEquiv sigma).symm
                ⟨pair.1.2.1.1, hsecondSourceNI⟩).1 from
            congrArg Prod.snd hsecondVal]
        have hlabel :
            (⟨pair.1.1.1.1, hfirstSourceNI⟩ :
              sigma.NoninjectiveLabel) =
            ⟨pair.1.2.1.1, hsecondSourceNI⟩ :=
          Subtype.ext pair.2
        exact congrArg
          (fun x ↦ ((AR.arTranslationEquiv sigma).symm x).1) hlabel
      let interiorPair : AR.InteriorCommonTargetArrowPair sigma :=
        ⟨(first, second), htarget⟩
      have hliteral :
          O.InteriorSource first ∨ O.InteriorSource second := by
        rcases p.1.1.2 with hP | hP
        · left
          apply (M.arrowInterior_source_iff sigma first).2
          rw [show first.1.1.1 = pair.1.1.1.2 from
            congrArg Prod.fst hfirstVal]
          exact hP
        · right
          apply (M.arrowInterior_source_iff sigma second).2
          rw [show second.1.1.1 = pair.1.2.1.2 from
            congrArg Prod.fst hsecondVal]
          exact hP
      let literal : AR.InteriorLiteralSourceCommonTargetPair sigma :=
        ⟨interiorPair, hliteral⟩
      refine ⟨literal, ?_⟩
      have hfirstSuccessor : O.successor pair.1.1 = firstRaw := by
        change (if hI : Injective (sigma.obj pair.1.1.1.1) then pair.1.1
          else (O.tau.symm ⟨pair.1.1, hI⟩).1) = firstRaw
        simp [hfirstSourceNI, firstRaw]
      have hsecondSuccessor : O.successor pair.1.2 = secondRaw := by
        change (if hI : Injective (sigma.obj pair.1.2.1.1) then pair.1.2
          else (O.tau.symm ⟨pair.1.2, hI⟩).1) = secondRaw
        simp [hsecondSourceNI, secondRaw]
      change ¬ O.SameSuccessorOrbit firstRaw secondRaw
      rw [← hfirstSuccessor, ← hsecondSuccessor,
        O.sameSuccessorOrbit_successor_iff]
      exact p.1.2
  let backward :
      AR.FullOrbitDifferentInteriorLiteralSourceCommonTargetPair sigma →
        AR.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair sigma :=
    fun p ↦ by
      let pair : AR.InteriorCommonTargetArrowPair sigma := p.1.1
      let firstRaw := (O.tau ⟨pair.1.1.1, pair.1.1.2.1⟩).1
      let secondRaw := (O.tau ⟨pair.1.2.1, pair.1.2.2.1⟩).1
      have hfirstVal := M.arrowOrbitData_tau_val sigma
        ⟨pair.1.1.1, pair.1.1.2.1⟩
      have hsecondVal := M.arrowOrbitData_tau_val sigma
        ⟨pair.1.2.1, pair.1.2.2.1⟩
      have hsource : firstRaw.1.1 = secondRaw.1.1 := by
        rw [show firstRaw.1.1 =
              (AR.arTranslation sigma
                ⟨pair.1.1.1.1.2, pair.1.1.2.1⟩).1 from
            congrArg Prod.fst hfirstVal,
          show secondRaw.1.1 =
              (AR.arTranslation sigma
                ⟨pair.1.2.1.1.2, pair.1.2.2.1⟩).1 from
            congrArg Prod.fst hsecondVal]
        have hlabel :
            (⟨pair.1.1.1.1.2, pair.1.1.2.1⟩ :
              sigma.NonprojectiveLabel) =
            ⟨pair.1.2.1.1.2, pair.1.2.2.1⟩ :=
          Subtype.ext pair.2
        exact congrArg (fun x ↦ (AR.arTranslation sigma x).1) hlabel
      let commonSource : CommonSourceArrowPair sigma :=
        ⟨(firstRaw, secondRaw), hsource⟩
      have hprojective :
          Projective (sigma.obj firstRaw.1.2) ∨
            Projective (sigma.obj secondRaw.1.2) := by
        rcases p.1.2 with hP | hP
        · left
          rw [show firstRaw.1.2 = pair.1.1.1.1.1 from
            congrArg Prod.snd hfirstVal]
          exact (M.arrowInterior_source_iff sigma pair.1.1).1 hP
        · right
          rw [show secondRaw.1.2 = pair.1.2.1.1.1 from
            congrArg Prod.snd hsecondVal]
          exact (M.arrowInterior_source_iff sigma pair.1.2).1 hP
      let projectiveTarget : ProjectiveTargetCommonSourcePair sigma :=
        ⟨commonSource, hprojective⟩
      have hfirstNI : ¬ Injective (sigma.obj firstRaw.1.2) := by
        rw [show firstRaw.1.2 = pair.1.1.1.1.1 from
          congrArg Prod.snd hfirstVal]
        exact pair.1.1.2.2
      have hsecondNI : ¬ Injective (sigma.obj secondRaw.1.2) := by
        rw [show secondRaw.1.2 = pair.1.2.1.1.1 from
          congrArg Prod.snd hsecondVal]
        exact pair.1.2.2.2
      have hdifferent : ¬ O.SameSuccessorOrbit firstRaw secondRaw := by
        intro hsame
        apply p.2
        have hfirstSuccessor : O.successor firstRaw = pair.1.1.1 := by
          have hnotI : ¬ Injective (sigma.obj firstRaw.1.1) :=
            (O.tau ⟨pair.1.1.1, pair.1.1.2.1⟩).2
          change (if hI : Injective (sigma.obj firstRaw.1.1) then firstRaw
            else (O.tau.symm ⟨firstRaw, hI⟩).1) = pair.1.1.1
          rw [dif_neg hnotI]
          exact congrArg Subtype.val
            (O.tau.symm_apply_apply
              ⟨pair.1.1.1, pair.1.1.2.1⟩)
        have hsecondSuccessor : O.successor secondRaw = pair.1.2.1 := by
          have hnotI : ¬ Injective (sigma.obj secondRaw.1.1) :=
            (O.tau ⟨pair.1.2.1, pair.1.2.2.1⟩).2
          change (if hI : Injective (sigma.obj secondRaw.1.1) then secondRaw
            else (O.tau.symm ⟨secondRaw, hI⟩).1) = pair.1.2.1
          rw [dif_neg hnotI]
          exact congrArg Subtype.val
            (O.tau.symm_apply_apply
              ⟨pair.1.2.1, pair.1.2.2.1⟩)
        have hsameSuccessor :=
          (O.sameSuccessorOrbit_successor_iff firstRaw secondRaw).2 hsame
        simpa [hfirstSuccessor, hsecondSuccessor] using hsameSuccessor
      let different : AR.DifferentOrbitProjectiveTargetCommonSourcePair
          sigma := ⟨projectiveTarget, hdifferent⟩
      exact ⟨different, hfirstNI, hsecondNI⟩
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro p
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · change
            (O.tau (O.tau.symm
              ⟨p.1.1.1.1.1,
                p.source_noninjective (K := K) sigma⟩)).1 =
              p.1.1.1.1.1
          exact congrArg Subtype.val
            (O.tau.apply_symm_apply
              ⟨p.1.1.1.1.1, p.source_noninjective (K := K) sigma⟩)
        · have hsecondSourceNI : ¬ Injective
              (sigma.obj p.1.1.1.1.2.1.1) := by
            rw [← p.1.1.1.2]
            exact p.source_noninjective (K := K) sigma
          change
            (O.tau (O.tau.symm
              ⟨p.1.1.1.1.2, hsecondSourceNI⟩)).1 =
              p.1.1.1.1.2
          exact congrArg Subtype.val
            (O.tau.apply_symm_apply
              ⟨p.1.1.1.1.2, hsecondSourceNI⟩)
      right_inv := by
        intro p
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          change
            (O.tau.symm (O.tau
              ⟨p.1.1.1.1.1, p.1.1.1.1.2.1⟩)).1 =
              p.1.1.1.1.1
          exact congrArg Subtype.val
            (O.tau.symm_apply_apply
              ⟨p.1.1.1.1.1, p.1.1.1.1.2.1⟩)
        · apply Subtype.ext
          change
            (O.tau.symm (O.tau
              ⟨p.1.1.1.2.1, p.1.1.1.2.2.1⟩)).1 =
              p.1.1.1.2.1
          exact congrArg Subtype.val
            (O.tau.symm_apply_apply
              ⟨p.1.1.1.2.1, p.1.1.1.2.2.1⟩) }

omit [DecidableEq iota] in
include K AR in
/-- Intrinsic oriented endpoint equivalence: the full projective-target
source coordinate with noninjective targets is exactly the trimmed
different-component literal common-target layer. -/
def differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivInteriorLiteral :
    AR.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair sigma ≃
      AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma :=
  (AR.differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivFullOrbitLiteral
    (K := K) sigma).trans
      (AR.fullOrbitDifferentInteriorLiteralEquivInteriorDifferentOrbitLiteral
        (K := K) sigma)

omit [DecidableEq iota] in
include K AR in
/-- Under endpoint rotation, the first interior occurrence lies literally
on the source boundary exactly when the old first arrow ends at a
projective. -/
theorem differentOrbitProjectiveTargetNoninjectiveCommonSource_first_source_iff
    (p : AR.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair
      sigma) :
    let E :=
      AR.differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivInteriorLiteral
        (K := K) sigma
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    O.InteriorSource (E p).1.1.1.1 ↔
      Projective (sigma.obj p.1.1.1.1.1.1.2) := by
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let E :=
    AR.differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivInteriorLiteral
      (K := K) sigma
  dsimp only
  rw [M.arrowInterior_source_iff]
  change Projective
      (sigma.obj
        (((O.tau.symm
          ⟨p.1.1.1.1.1,
            p.source_noninjective (K := K) sigma⟩).1).1.1)) ↔ _
  rw [show
      ((O.tau.symm
        ⟨p.1.1.1.1.1,
          p.source_noninjective (K := K) sigma⟩).1).1.1 =
        p.1.1.1.1.1.1.2 from
    congrArg Prod.fst
      (M.arrowOrbitData_tau_symm_val sigma
        ⟨p.1.1.1.1.1,
          p.source_noninjective (K := K) sigma⟩)]

omit [DecidableEq iota] in
include K AR in
/-- Under endpoint rotation, the first interior occurrence lies at the
terminal boundary exactly when the inverse translate of the old common
source is injective. -/
theorem differentOrbitProjectiveTargetNoninjectiveCommonSource_first_target_iff
    (p : AR.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair
      sigma) :
    let E :=
      AR.differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivInteriorLiteral
        (K := K) sigma
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    O.InteriorTarget (E p).1.1.1.1 ↔
      Injective
        (sigma.obj (p.inverseCommonSource (K := K) sigma AR).1) := by
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let E :=
    AR.differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivInteriorLiteral
      (K := K) sigma
  dsimp only
  rw [M.arrowInterior_target_iff]
  change Injective
      (sigma.obj
        (((O.tau.symm
          ⟨p.1.1.1.1.1,
            p.source_noninjective (K := K) sigma⟩).1).1.2)) ↔ _
  rw [show
      ((O.tau.symm
        ⟨p.1.1.1.1.1,
          p.source_noninjective (K := K) sigma⟩).1).1.2 =
        (p.inverseCommonSource (K := K) sigma AR).1 from
    congrArg Prod.snd
      (M.arrowOrbitData_tau_symm_val sigma
        ⟨p.1.1.1.1.1,
          p.source_noninjective (K := K) sigma⟩)]

omit [DecidableEq iota] in
include K AR in
/-- The first-nonprojective-target endpoint whose inverse common source is
injective rotates exactly to the terminal literal-source endpoint whose
first occurrence is not itself on the source boundary. -/
def differentOrbitInverseInjectiveCommonSourceEquivTerminalFirstNotSource :
    AR.DifferentOrbitFirstNonprojectiveTargetInverseInjectiveCommonSourcePair
        (K := K) sigma ≃
      AR.InteriorTerminalFirstNotSourceCommonTargetPair sigma := by
  let E :=
    AR.differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivInteriorLiteral
      (K := K) sigma
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let hsource := fun
      (q : AR.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair
        sigma) ↦
    AR.differentOrbitProjectiveTargetNoninjectiveCommonSource_first_source_iff
      (K := K) sigma q
  let htarget := fun
      (q : AR.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair
        sigma) ↦
    AR.differentOrbitProjectiveTargetNoninjectiveCommonSource_first_target_iff
      (K := K) sigma q
  let forward :
      AR.DifferentOrbitFirstNonprojectiveTargetInverseInjectiveCommonSourcePair
          (K := K) sigma →
        AR.InteriorTerminalFirstNotSourceCommonTargetPair sigma :=
    fun p ↦ by
      let q := p.1.1
      let c := E q
      refine ⟨⟨c.1, Or.inl ?_⟩, ?_⟩
      · exact (htarget q).2 p.2
      · intro hs
        exact p.1.2 ((hsource q).1 hs)
  let backward :
      AR.InteriorTerminalFirstNotSourceCommonTargetPair sigma →
        AR.DifferentOrbitFirstNonprojectiveTargetInverseInjectiveCommonSourcePair
          (K := K) sigma :=
    fun p ↦ by
      let c : AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma :=
        ⟨p.1.1,
          AR.interiorTerminalFirstNotSourceCommonTarget_differentOrbit
            sigma p⟩
      let q := E.symm c
      have hc : E q = c := E.apply_symm_apply c
      have hnotSource : ¬ O.InteriorSource (E q).1.1.1.1 := by
        rw [hc]
        exact p.2
      have hfirstNP : ¬ Projective
          (sigma.obj q.1.1.1.1.1.1.2) :=
        fun hP ↦ hnotSource ((hsource q).2 hP)
      have hfirstTarget : O.InteriorTarget p.1.1.1.1.1 :=
        (M.arrowInterior_target_iff sigma p.1.1.1.1.1).2 (by
          rw [p.1.1.1.2]
          exact
            AR.interiorLiteralSourceTerminalCommonTarget_target_injective
              sigma p.1)
      have htargetE : O.InteriorTarget (E q).1.1.1.1 := by
        rw [hc]
        exact hfirstTarget
      exact ⟨⟨q, hfirstNP⟩, (htarget q).1 htargetE⟩
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro p
        apply Subtype.ext
        apply Subtype.ext
        change E.symm _ = p.1.1
        rw [show
          (⟨(E p.1.1).1,
              AR.interiorTerminalFirstNotSourceCommonTarget_differentOrbit
                sigma (forward p)⟩ :
              AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma) =
            E p.1.1 by
          apply Subtype.ext
          rfl]
        exact E.symm_apply_apply p.1.1
      right_inv := by
        intro p
        apply Subtype.ext
        apply Subtype.ext
        change (E (E.symm _)).1 = p.1.1
        rw [E.apply_symm_apply] }

/-- The nonterminal companion of the preceding terminal branch: the first
literal occurrence is not on the source boundary, and the common target is
noninjective.  Literal-source membership then forces the second occurrence
to be the distinguished source-boundary occurrence. -/
abbrev InteriorDifferentOrbitFirstNotSourceNoninjectiveTargetPair :=
  {p : AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma //
    ¬ ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
        p.1.1.1.1 ∧
      ¬ Injective (sigma.obj p.1.1.1.2.1.1.2)}

noncomputable instance
    interiorDifferentOrbitFirstNotSourceNoninjectiveTargetPairFintype :
    Fintype
      (AR.InteriorDifferentOrbitFirstNotSourceNoninjectiveTargetPair
        sigma) :=
  Fintype.ofFinite _

omit [DecidableEq iota] in
include K AR in
/-- The first-nonprojective-target source coordinate whose inverse common
source remains noninjective rotates exactly to the first-not-source,
noninjective-target literal boundary. -/
def differentOrbitInverseNoninjectiveCommonSourceEquivFirstNotSourceNoninjectiveTarget :
    AR.DifferentOrbitFirstNonprojectiveTargetInverseNoninjectiveCommonSourcePair
        (K := K) sigma ≃
      AR.InteriorDifferentOrbitFirstNotSourceNoninjectiveTargetPair
        sigma := by
  let E :=
    AR.differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivInteriorLiteral
      (K := K) sigma
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let hsource := fun
      (q : AR.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair
        sigma) ↦
    AR.differentOrbitProjectiveTargetNoninjectiveCommonSource_first_source_iff
      (K := K) sigma q
  let htarget := fun
      (q : AR.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair
        sigma) ↦
    AR.differentOrbitProjectiveTargetNoninjectiveCommonSource_first_target_iff
      (K := K) sigma q
  let forward :
      AR.DifferentOrbitFirstNonprojectiveTargetInverseNoninjectiveCommonSourcePair
          (K := K) sigma →
        AR.InteriorDifferentOrbitFirstNotSourceNoninjectiveTargetPair
          sigma :=
    fun p ↦ by
      let q := p.1.1
      let c := E q
      refine ⟨c, ?_, ?_⟩
      · intro hs
        exact p.1.2 ((hsource q).1 hs)
      · intro hcommonI
        apply p.2
        apply (htarget q).1
        apply (M.arrowInterior_target_iff sigma c.1.1.1.1).2
        rw [c.1.1.2]
        exact hcommonI
  let backward :
      AR.InteriorDifferentOrbitFirstNotSourceNoninjectiveTargetPair sigma →
        AR.DifferentOrbitFirstNonprojectiveTargetInverseNoninjectiveCommonSourcePair
          (K := K) sigma :=
    fun p ↦ by
      let q := E.symm p.1
      have hc : E q = p.1 := E.apply_symm_apply p.1
      have hnotSource : ¬ O.InteriorSource (E q).1.1.1.1 := by
        rw [hc]
        exact p.2.1
      have hfirstNP : ¬ Projective
          (sigma.obj q.1.1.1.1.1.1.2) :=
        fun hP ↦ hnotSource ((hsource q).2 hP)
      have hinverseNI : ¬ Injective
          (sigma.obj (q.inverseCommonSource (K := K) sigma AR).1) := by
        intro hinverseI
        have htargetE : O.InteriorTarget (E q).1.1.1.1 :=
          (htarget q).2 hinverseI
        have htargetP : O.InteriorTarget p.1.1.1.1.1 := by
          rw [← hc]
          exact htargetE
        have hfirstI : Injective
            (sigma.obj p.1.1.1.1.1.1.1.2) :=
          (M.arrowInterior_target_iff sigma p.1.1.1.1.1).1 htargetP
        apply p.2.2
        rw [← p.1.1.1.2]
        exact hfirstI
      exact ⟨⟨q, hfirstNP⟩, hinverseNI⟩
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro p
        apply Subtype.ext
        apply Subtype.ext
        change E.symm (E p.1.1) = p.1.1
        exact E.symm_apply_apply p.1.1
      right_inv := by
        intro p
        apply Subtype.ext
        change E (E.symm p.1) = p.1
        exact E.apply_symm_apply p.1 }

/-- The noninjective first boundary restricted to orientations whose second
occurrence is not also on the literal source boundary. -/
abbrev DifferentOrbitFirstSourceNoninjectiveTargetSecondNotSourcePair :=
  {p : AR.DifferentOrbitFirstSourceNoninjectiveTargetPair sigma //
    ¬ ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
      p.1.1.1.1.2}

noncomputable instance
    differentOrbitFirstSourceNoninjectiveTargetSecondNotSourcePairFintype :
    Fintype
      (AR.DifferentOrbitFirstSourceNoninjectiveTargetSecondNotSourcePair
        sigma) :=
  Fintype.ofFinite _

/-- Complementary orientation in which both labelled occurrences lie
literally on the trimmed source boundary. -/
abbrev DifferentOrbitFirstSourceNoninjectiveTargetSecondSourcePair :=
  {p : AR.DifferentOrbitFirstSourceNoninjectiveTargetPair sigma //
    ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
      p.1.1.1.1.2}

noncomputable instance
    differentOrbitFirstSourceNoninjectiveTargetSecondSourcePairFintype :
    Fintype
      (AR.DifferentOrbitFirstSourceNoninjectiveTargetSecondSourcePair
        sigma) :=
  Fintype.ofFinite _

/-- Exact split of the different-component noninjective first boundary by
whether its second labelled occurrence is also a literal source. -/
def differentOrbitFirstSourceNoninjectiveTargetEquivSecondSourceSumSecondNotSource :
    AR.DifferentOrbitFirstSourceNoninjectiveTargetPair sigma ≃
      AR.DifferentOrbitFirstSourceNoninjectiveTargetSecondSourcePair sigma ⊕
        AR.DifferentOrbitFirstSourceNoninjectiveTargetSecondNotSourcePair
          sigma := by
  classical
  let P : AR.DifferentOrbitFirstSourceNoninjectiveTargetPair sigma → Prop :=
    fun p ↦
      ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
        p.1.1.1.1.2
  simpa [P] using (Equiv.sumCompl P).symm

omit [DecidableEq iota] in
/-- Cardinal form of the two-orientation noninjective first-boundary
split. -/
theorem differentOrbitFirstSourceNoninjectiveTarget_card_eq_secondSource_add_secondNotSource :
    Fintype.card
        (AR.DifferentOrbitFirstSourceNoninjectiveTargetPair sigma) =
      Fintype.card
          (AR.DifferentOrbitFirstSourceNoninjectiveTargetSecondSourcePair
            sigma) +
        Fintype.card
          (AR.DifferentOrbitFirstSourceNoninjectiveTargetSecondNotSourcePair
            sigma) := by
  rw [Fintype.card_congr
    (AR.differentOrbitFirstSourceNoninjectiveTargetEquivSecondSourceSumSecondNotSource
      sigma)]
  exact Fintype.card_sum

omit [DecidableEq iota] in
/-- Swapping the two labelled occurrences turns a first-not-source literal
pair into a first-source pair whose second occurrence is not a source. -/
def interiorDifferentOrbitFirstNotSourceNoninjectiveTargetEquivFirstSourceSecondNotSource :
    AR.InteriorDifferentOrbitFirstNotSourceNoninjectiveTargetPair sigma ≃
      AR.DifferentOrbitFirstSourceNoninjectiveTargetSecondNotSourcePair
        sigma where
  toFun p := by
    let M := AR.arMeshRotationData sigma
    let O := M.arrowOrbitData sigma
    let U := M.arrowInteriorOrbitData sigma
    let pair := p.1.1.1
    have hsecondSource : O.InteriorSource pair.1.2 :=
      p.1.1.2.resolve_left p.2.1
    let swapped : AR.InteriorCommonTargetArrowPair sigma :=
      ⟨(pair.1.2, pair.1.1), pair.2.symm⟩
    have htargetNI : ¬ Injective
        (sigma.obj swapped.1.2.1.1.2) := by
      change ¬ Injective (sigma.obj pair.1.1.1.1.2)
      rw [pair.2]
      exact p.2.2
    have hdifferent :
        InteriorCommonTargetArrowPair.DifferentOrbit sigma AR swapped := by
      change ¬ U.SameSuccessorOrbit pair.1.2 pair.1.1
      intro h
      exact p.1.2 (U.sameSuccessorOrbit_symm h)
    exact ⟨⟨⟨⟨swapped, hsecondSource⟩, htargetNI⟩,
      hdifferent⟩, p.2.1⟩
  invFun p := by
    let M := AR.arMeshRotationData sigma
    let O := M.arrowOrbitData sigma
    let U := M.arrowInteriorOrbitData sigma
    let pair := p.1.1.1.1
    let swapped : AR.InteriorCommonTargetArrowPair sigma :=
      ⟨(pair.1.2, pair.1.1), pair.2.symm⟩
    have hliteral : O.InteriorSource swapped.1.2 := p.1.1.1.2
    have hdifferent :
        InteriorCommonTargetArrowPair.DifferentOrbit sigma AR swapped := by
      change ¬ U.SameSuccessorOrbit pair.1.2 pair.1.1
      intro h
      exact p.1.2 (U.sameSuccessorOrbit_symm h)
    have htargetNI : ¬ Injective
        (sigma.obj swapped.1.2.1.1.2) := by
      change ¬ Injective (sigma.obj pair.1.1.1.1.2)
      rw [pair.2]
      exact p.1.1.2
    exact ⟨⟨⟨swapped, Or.inr hliteral⟩, hdifferent⟩,
      p.2, htargetNI⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The oriented part of the trimmed different-component literal layer in
which the first labelled occurrence is literally on the source boundary. -/
abbrev InteriorDifferentOrbitFirstLiteralSourceCommonTargetPair :=
  {p : AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma //
    ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
      p.1.1.1.1}

noncomputable instance
    interiorDifferentOrbitFirstLiteralSourceCommonTargetPairFintype :
    Fintype
      (AR.InteriorDifferentOrbitFirstLiteralSourceCommonTargetPair sigma) :=
  Fintype.ofFinite _

omit [DecidableEq iota] in
include K AR in
/-- Endpoint rotation sends the first-projective-target source coordinate
exactly to the first-literal-source trimmed coordinate. -/
def differentOrbitFirstProjectiveTargetEquivFirstLiteralSource :
    AR.DifferentOrbitFirstProjectiveTargetNoninjectiveCommonSourcePair
        sigma ≃
      AR.InteriorDifferentOrbitFirstLiteralSourceCommonTargetPair sigma := by
  let E :=
    AR.differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivInteriorLiteral
      (K := K) sigma
  apply E.subtypeEquiv
  intro p
  exact
    (AR.differentOrbitProjectiveTargetNoninjectiveCommonSource_first_source_iff
      (K := K) sigma p).symm

omit [DecidableEq iota] in
/-- The first-literal-source different-component layer splits exactly by
whether its common target is injective.  These are, respectively, the
different-component injective-target boundary and the noninjective-target
first-source boundary. -/
def interiorDifferentOrbitFirstLiteralSourceEquivInjectiveSumNoninjective :
    AR.InteriorDifferentOrbitFirstLiteralSourceCommonTargetPair sigma ≃
      AR.DifferentOrbitBoundaryM6InjectiveTargetPair sigma ⊕
        AR.DifferentOrbitFirstSourceNoninjectiveTargetPair sigma where
  toFun p := by
    classical
    by_cases hI : Injective (sigma.obj p.1.1.1.1.2.1.1.2)
    · let q : AR.BoundaryM6InjectiveTargetPair sigma :=
        { pair := p.1.1.1
          first_source := p.2
          target_injective := hI }
      exact Sum.inl ⟨q, p.1.2⟩
    · exact Sum.inr ⟨⟨⟨p.1.1.1, p.2⟩, hI⟩, p.1.2⟩
  invFun p := by
    rcases p with p | p
    · exact ⟨⟨⟨p.1.pair, Or.inl p.1.first_source⟩, p.2⟩,
        p.1.first_source⟩
    · exact ⟨⟨⟨p.1.1.1, Or.inl p.1.1.2⟩, p.2⟩, p.1.1.2⟩
  left_inv p := by
    classical
    by_cases hI : Injective (sigma.obj p.1.1.1.1.2.1.1.2)
    · simp [hI]
    · simp [hI]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.1.target_injective]
    · simp [p.1.2]

noncomputable instance differentOrbitNoProjectiveFirstInjectivePairFintype :
    Fintype (AR.DifferentOrbitNoProjectiveFirstInjectivePair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitNoProjectiveFirstNoninjectivePairFintype :
    Fintype (AR.DifferentOrbitNoProjectiveFirstNoninjectivePair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitNoProjectiveFirstNoninjectiveDeepPairFintype :
    Fintype (AR.DifferentOrbitNoProjectiveFirstNoninjectiveDeepPair
      (K := K) sigma) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitProjectiveTargetNoninjectiveCommonSourcePairFintype :
    Fintype (AR.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair
      sigma) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitFirstProjectiveTargetNoninjectiveCommonSourcePairFintype :
    Fintype
      (AR.DifferentOrbitFirstProjectiveTargetNoninjectiveCommonSourcePair
        sigma) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitFirstNonprojectiveTargetNoninjectiveCommonSourcePairFintype :
    Fintype
      (AR.DifferentOrbitFirstNonprojectiveTargetNoninjectiveCommonSourcePair
        sigma) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitFirstNonprojectiveTargetInverseInjectiveCommonSourcePairFintype :
    Fintype
      (AR.DifferentOrbitFirstNonprojectiveTargetInverseInjectiveCommonSourcePair
        (K := K) sigma) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitFirstNonprojectiveTargetInverseNoninjectiveCommonSourcePairFintype :
    Fintype
      (AR.DifferentOrbitFirstNonprojectiveTargetInverseNoninjectiveCommonSourcePair
        (K := K) sigma) :=
  Fintype.ofFinite _

include K AR in
/-- Exact three-way partition of the full different-component endpoint with
an injective source and no projective source.  The middle summand is the
actual outer `M5` image; the other two summands are its two intrinsic
complements. -/
def differentOrbitInjectiveSourceNoProjectiveEquivFirstInjectiveSumM5SumDeep :
    AR.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
        sigma ≃
      AR.DifferentOrbitNoProjectiveFirstInjectivePair sigma ⊕
        (AR.FirstNISINoProjectiveDifferentOrbitImage sigma ⊕
          AR.DifferentOrbitNoProjectiveFirstNoninjectiveDeepPair
            (K := K) sigma) where
  toFun p := by
    classical
    by_cases hfirstI : Injective (sigma.obj p.1.1.1.1.1.1.1)
    · exact Sum.inl ⟨p, hfirstI⟩
    · have hsecondI : Injective (sigma.obj p.1.1.1.1.2.1.1) :=
        p.1.1.2.resolve_left hfirstI
      by_cases htranslatedP : Projective
          (sigma.obj (AR.arTranslation sigma
            ⟨p.1.1.1.1.1.1.2,
              p.target_nonprojective (K := K) sigma⟩).1)
      · exact Sum.inr (Sum.inl ⟨p,
          (AR.mem_firstNISINoProjectiveDifferentOrbitImage_iff
            (K := K) sigma p).2
              ⟨hfirstI, hsecondI, htranslatedP⟩⟩)
      · exact Sum.inr (Sum.inr ⟨p, hfirstI, htranslatedP⟩)
  invFun p := by
    rcases p with p | p
    · exact p.1
    · rcases p with p | p
      · exact p.1
      · exact p.1
  left_inv p := by
    classical
    by_cases hfirstI : Injective (sigma.obj p.1.1.1.1.1.1.1)
    · simp [hfirstI]
    · by_cases htranslatedP : Projective
          (sigma.obj (AR.arTranslation sigma
            ⟨p.1.1.1.1.1.1.2,
              p.target_nonprojective (K := K) sigma⟩).1)
      · simp [hfirstI, htranslatedP]
      · simp [hfirstI, htranslatedP]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.2]
    · rcases p with p | p
      · have hmem :=
          (AR.mem_firstNISINoProjectiveDifferentOrbitImage_iff
            (K := K) sigma p.1).1 p.2
        simp [hmem.1, hmem.2.2]
      · simp [p.2.1, p.2.2]

omit [DecidableEq iota] in
include K AR in
/-- Cardinal form of the exact three-way full endpoint partition. -/
theorem differentOrbitInjectiveSourceNoProjective_card_eq_firstInjective_add_m5_add_deep :
    Fintype.card
        (AR.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
          sigma) =
      Fintype.card (AR.DifferentOrbitNoProjectiveFirstInjectivePair sigma) +
        Fintype.card (AR.FirstNISINoProjectiveDifferentOrbitImage sigma) +
          Fintype.card
            (AR.DifferentOrbitNoProjectiveFirstNoninjectiveDeepPair
              (K := K) sigma) := by
  rw [Fintype.card_congr
    (AR.differentOrbitInjectiveSourceNoProjectiveEquivFirstInjectiveSumM5SumDeep
      (K := K) sigma)]
  simp only [Fintype.card_sum]
  omega

include K AR in
/-- Reassociate the first-noninjective orientation restricted to the exact
`M5` image with the image subtype itself. -/
def differentOrbitFirstNoninjectiveM5SubtypeEquivImage :
    {p : AR.DifferentOrbitNoProjectiveFirstNoninjectivePair sigma //
      p.1 ∈ AR.FirstNISINoProjectiveDifferentOrbitImage sigma} ≃
      AR.FirstNISINoProjectiveDifferentOrbitImage sigma where
  toFun p := ⟨p.1.1, p.2⟩
  invFun p :=
    ⟨⟨p.1,
      ((AR.mem_firstNISINoProjectiveDifferentOrbitImage_iff
        (K := K) sigma p.1).1 p.2).1⟩, p.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

include K AR in
/-- In the first-noninjective orientation, the complement of the exact
`M5` image is precisely the previously defined deep endpoint. -/
def differentOrbitFirstNoninjectiveNotM5EquivDeep :
    {p : AR.DifferentOrbitNoProjectiveFirstNoninjectivePair sigma //
      p.1 ∉ AR.FirstNISINoProjectiveDifferentOrbitImage sigma} ≃
      AR.DifferentOrbitNoProjectiveFirstNoninjectiveDeepPair
        (K := K) sigma where
  toFun p := by
    refine ⟨p.1.1, p.1.2, ?_⟩
    intro htranslatedP
    apply p.2
    apply (AR.mem_firstNISINoProjectiveDifferentOrbitImage_iff
      (K := K) sigma p.1.1).2
    exact ⟨p.1.2, p.1.1.1.1.2.resolve_left p.1.2,
      htranslatedP⟩
  invFun p := by
    refine ⟨⟨p.1, p.2.1⟩, ?_⟩
    intro hmem
    exact p.2.2
      ((AR.mem_firstNISINoProjectiveDifferentOrbitImage_iff
        (K := K) sigma p.1).1 hmem).2.2
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- The unused injective-first outer `M3` occurrences whose second source is
still noninjective. -/
abbrev HookWallBadBUnrestricted.M6SecondBoundaryComplementSecondNoninjective :=
  {W : HookWallBadBUnrestricted.M6SecondBoundaryComplement
      (K := K) sigma AR //
    ¬ Injective (sigma.obj W.1.1.1.1.triple.u)}

/-- The unused injective-first outer `M3` occurrences whose second source is
injective. -/
abbrev HookWallBadBUnrestricted.M6SecondBoundaryComplementSecondInjective :=
  {W : HookWallBadBUnrestricted.M6SecondBoundaryComplement
      (K := K) sigma AR //
    Injective (sigma.obj W.1.1.1.1.triple.u)}

noncomputable instance
    hookWallBadBM6SecondBoundaryComplementSecondNoninjectiveFintype :
    Fintype
      (HookWallBadBUnrestricted.M6SecondBoundaryComplementSecondNoninjective
        (K := K) sigma AR) :=
  Fintype.ofFinite _

noncomputable instance
    hookWallBadBM6SecondBoundaryComplementSecondInjectiveFintype :
    Fintype
      (HookWallBadBUnrestricted.M6SecondBoundaryComplementSecondInjective
        (K := K) sigma AR) :=
  Fintype.ofFinite _

namespace HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary

variable
  (M : HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary
    sigma AR)

include K AR in
/-- Refine the existing second-boundary `M6`-to-`M3` overlap map by
recording that the reconstructed `M3` second source is noninjective. -/
def toHookWallBadBSecondNoninjective :
    HookWallBadBUnrestricted.InjectiveFirstSecondNoninjective sigma AR := by
  let W := M.toHookWallBadB (K := K) sigma AR
  refine ⟨W, ?_⟩
  have hpair := M.toHookWallBadB_commonTargetPair (K := K) sigma AR
  have hs := congrArg
    (fun p : CommonTargetArrowPair sigma ↦ p.1.2.1.1) hpair
  have hs' : W.1.1.1.triple.u =
      (M.1.1.1.1.triple.hookOrbitAnchor sigma AR).1.1 := by
    simpa [W, HookWallBadBUnrestricted.commonTargetPair,
      StripAdmissibleTriple.secondArrow,
      HookM6Channel.commonTargetPair] using hs
  intro hI
  apply (M.1.1.1.hookOrbitAnchor_isInterior sigma AR).2
  rw [← hs']
  exact hI

end HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary

/-- Exact intrinsic occurrence image of the second-boundary outer `M6`
overlap inside the surviving-second-arrow `M3` stratum. -/
abbrev FirstPISecondInteriorM6Image :=
  Set.range (fun M :
      HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary
        sigma AR ↦
    (M.toHookWallBadBSecondNoninjective (K := K) sigma AR).firstPISecondInteriorTwoSourceOuterPair
      sigma AR)

noncomputable instance firstPISecondInteriorM6ImageFintype :
    Fintype (AR.FirstPISecondInteriorM6Image (K := K) sigma) :=
  Fintype.ofFinite _

/-- Intrinsic surviving-second-arrow `M3` occurrences not used by the exact
second-boundary outer `M6` overlap. -/
abbrev FirstPISecondInteriorM6Complement :=
  {p : AR.FirstPISecondInteriorTwoSourceOuterPair sigma //
    p ∉ AR.FirstPISecondInteriorM6Image (K := K) sigma}

noncomputable instance firstPISecondInteriorM6ComplementFintype :
    Fintype (AR.FirstPISecondInteriorM6Complement (K := K) sigma) :=
  Fintype.ofFinite _

/-- Split the unused outer `M3` complement by survival of its second arrow. -/
def hookWallBadBM6SecondBoundaryComplementEquivSecondNoninjectiveSumInjective :
    HookWallBadBUnrestricted.M6SecondBoundaryComplement
        (K := K) sigma AR ≃
      HookWallBadBUnrestricted.M6SecondBoundaryComplementSecondNoninjective
          (K := K) sigma AR ⊕
        HookWallBadBUnrestricted.M6SecondBoundaryComplementSecondInjective
          (K := K) sigma AR where
  toFun W := by
    classical
    by_cases h : Injective (sigma.obj W.1.1.1.1.triple.u)
    · exact Sum.inr ⟨W, h⟩
    · exact Sum.inl ⟨W, h⟩
  invFun W := by
    rcases W with W | W
    · exact W.1
    · exact W.1
  left_inv W := by
    classical
    by_cases h : Injective (sigma.obj W.1.1.1.1.triple.u)
    · simp [h]
    · simp [h]
  right_inv W := by
    classical
    rcases W with W | W
    · simp [W.2]
    · simp [W.2]

include K AR in
/-- A second-boundary outer `M6` image always has noninjective second
source. -/
theorem hookWallBadBInjectiveFirstSecondInjective_not_mem_M6SecondBoundaryImage
    (W : HookWallBadBUnrestricted.InjectiveFirstSecondInjective sigma AR) :
    W.1 ∉ HookWallBadBUnrestricted.M6SecondBoundaryImage
      (K := K) sigma AR := by
  rintro ⟨M, hM⟩
  have hpair := M.toHookWallBadB_commonTargetPair (K := K) sigma AR
  have hs := congrArg
    (fun p : CommonTargetArrowPair sigma ↦ p.1.2.1.1) hpair
  have hs' :
      (M.toHookWallBadB (K := K) sigma AR).1.1.1.triple.u =
        (M.1.1.1.1.triple.hookOrbitAnchor sigma AR).1.1 := by
    simpa [HookWallBadBUnrestricted.commonTargetPair,
      StripAdmissibleTriple.secondArrow,
      HookM6Channel.commonTargetPair] using hs
  have hanchorNI :=
    (M.1.1.1.hookOrbitAnchor_isInterior sigma AR).2
  have hmapNI : ¬ Injective
      (sigma.obj (M.toHookWallBadB (K := K) sigma AR).1.1.1.triple.u) := by
    intro hI
    apply hanchorNI
    rw [← hs']
    exact hI
  apply hmapNI
  rw [hM]
  exact W.2

include K AR in
/-- The injective-second-source part of the `M3` complement is the entire
injective-second-source branch: it cannot overlap outer `M6`. -/
def hookWallBadBM6SecondBoundaryComplementSecondInjectiveEquiv :
    HookWallBadBUnrestricted.M6SecondBoundaryComplementSecondInjective
        (K := K) sigma AR ≃
      HookWallBadBUnrestricted.InjectiveFirstSecondInjective sigma AR where
  toFun W := ⟨W.1.1, W.2⟩
  invFun W :=
    ⟨⟨W.1,
      hookWallBadBInjectiveFirstSecondInjective_not_mem_M6SecondBoundaryImage
        sigma AR W⟩, W.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

include K AR in
/-- The noninjective-second-source part of the unused outer `M3` complement
is exactly the intrinsic second-boundary stratum outside the actual outer
`M6` overlap image. -/
def hookWallBadBM6SecondBoundaryComplementSecondNoninjectiveEquivIntrinsic :
    HookWallBadBUnrestricted.M6SecondBoundaryComplementSecondNoninjective
        (K := K) sigma AR ≃
      AR.FirstPISecondInteriorM6Complement (K := K) sigma where
  toFun W := by
    let W₀ :
        HookWallBadBUnrestricted.InjectiveFirstSecondNoninjective
          sigma AR := ⟨W.1.1, W.2⟩
    let E :=
      hookWallBadBInjectiveFirstSecondNoninjectiveEquivFirstPISecondInteriorTwoSource
        (K := K) sigma AR
    refine ⟨E W₀, ?_⟩
    rintro ⟨M, hM⟩
    apply W.1.2
    refine ⟨M, ?_⟩
    have hW : M.toHookWallBadBSecondNoninjective
        (K := K) sigma AR = W₀ := E.injective hM
    exact congrArg Subtype.val hW
  invFun p := by
    let E :=
      hookWallBadBInjectiveFirstSecondNoninjectiveEquivFirstPISecondInteriorTwoSource
        (K := K) sigma AR
    let W₀ := E.symm p.1
    refine ⟨⟨W₀.1, ?_⟩, W₀.2⟩
    rintro ⟨M, hM⟩
    apply p.2
    refine ⟨M, ?_⟩
    have hW : M.toHookWallBadBSecondNoninjective
        (K := K) sigma AR = W₀ := by
      apply Subtype.ext
      exact hM
    change E (M.toHookWallBadBSecondNoninjective
      (K := K) sigma AR) = p.1
    rw [hW, E.apply_symm_apply]
  left_inv W := by
    apply Subtype.ext
    apply Subtype.ext
    change
      ((hookWallBadBInjectiveFirstSecondNoninjectiveEquivFirstPISecondInteriorTwoSource
        (K := K) sigma AR).symm
        ((hookWallBadBInjectiveFirstSecondNoninjectiveEquivFirstPISecondInteriorTwoSource
          (K := K) sigma AR) ⟨W.1.1, W.2⟩)).1 = W.1.1
    rw [Equiv.symm_apply_apply]
  right_inv p := by
    apply Subtype.ext
    exact (hookWallBadBInjectiveFirstSecondNoninjectiveEquivFirstPISecondInteriorTwoSource
      (K := K) sigma AR).apply_symm_apply p.1

include K AR in
/-- Complete intrinsic classification of the unused injective-first outer
`M3` complement. -/
def hookWallBadBM6SecondBoundaryComplementEquivIntrinsicSumTranslatedTarget :
    HookWallBadBUnrestricted.M6SecondBoundaryComplement
        (K := K) sigma AR ≃
      AR.FirstPISecondInteriorM6Complement (K := K) sigma ⊕
        AR.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair
          sigma :=
  (hookWallBadBM6SecondBoundaryComplementEquivSecondNoninjectiveSumInjective
      (K := K) sigma AR).trans <|
    Equiv.sumCongr
      (hookWallBadBM6SecondBoundaryComplementSecondNoninjectiveEquivIntrinsic
        (K := K) sigma AR)
      ((hookWallBadBM6SecondBoundaryComplementSecondInjectiveEquiv
          (K := K) sigma AR).trans
        (hookWallBadBInjectiveFirstSecondInjectiveEquivTranslatedTargetProjective
          (K := K) sigma AR))

/-- Exact intrinsic occurrence image of projective-anchor outer `M6` inside
the projective/noninjective-second-source `M2` stratum. -/
abbrev FirstPISecondProjectiveM6Image :=
  Set.range (fun M : HookM6Channel.InjectiveFourthProjectiveAnchor
      sigma AR ↦
    (M.toHookWallBadU (K := K) sigma AR).firstPISecondProjectiveNoninjectiveOuterPair
      sigma AR)

noncomputable instance firstPISecondProjectiveM6ImageFintype :
    Fintype (AR.FirstPISecondProjectiveM6Image (K := K) sigma) :=
  Fintype.ofFinite _

/-- Intrinsic projective/noninjective-second-source occurrences not used by
the exact projective-anchor outer `M6` overlap. -/
abbrev FirstPISecondProjectiveM6Complement :=
  {p : AR.FirstPISecondProjectiveNoninjectiveOuterPair sigma //
    p ∉ AR.FirstPISecondProjectiveM6Image (K := K) sigma}

noncomputable instance firstPISecondProjectiveM6ComplementFintype :
    Fintype (AR.FirstPISecondProjectiveM6Complement (K := K) sigma) :=
  Fintype.ofFinite _

include K AR in
/-- The unused outer `M2` complement is exactly the intrinsic
projective/noninjective-second-source stratum outside the actual outer `M6`
overlap image. -/
def hookWallBadUM6ProjectiveAnchorComplementEquivIntrinsic :
    HookWallBadU.M6ProjectiveAnchorComplement (K := K) sigma AR ≃
      AR.FirstPISecondProjectiveM6Complement (K := K) sigma where
  toFun W := by
    let E :=
      hookWallBadUInjectiveFourthEquivFirstPISecondProjectiveNoninjective
        (K := K) sigma AR
    refine ⟨E W.1, ?_⟩
    rintro ⟨M, hM⟩
    apply W.2
    refine ⟨M, ?_⟩
    exact E.injective hM
  invFun p := by
    let E :=
      hookWallBadUInjectiveFourthEquivFirstPISecondProjectiveNoninjective
        (K := K) sigma AR
    refine ⟨E.symm p.1, ?_⟩
    rintro ⟨M, hM⟩
    apply p.2
    refine ⟨M, ?_⟩
    change E (M.toHookWallBadU (K := K) sigma AR) = p.1
    rw [hM, E.apply_symm_apply]
  left_inv W := by
    apply Subtype.ext
    exact (hookWallBadUInjectiveFourthEquivFirstPISecondProjectiveNoninjective
      (K := K) sigma AR).symm_apply_apply W.1
  right_inv p := by
    apply Subtype.ext
    exact (hookWallBadUInjectiveFourthEquivFirstPISecondProjectiveNoninjective
      (K := K) sigma AR).apply_symm_apply p.1

namespace HookM6Channel.InjectiveFourthDeepAnchor

variable (M : HookM6Channel.InjectiveFourthDeepAnchor sigma AR)

/-- A deep-anchor outer `M6` occurrence in the oriented
projective-injective-first endpoint coordinates. -/
def firstProjectiveInjectiveDifferentOrbitOuterPair :
    AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma :=
  { pair := M.1.1.1.commonTargetPair sigma AR
    target_nonprojective := by
      simpa [HookM6Channel.commonTargetPair,
        HookM6Channel.associatedArrow] using M.1.1.1.2
    first_projective := by
      simpa [HookM6Channel.commonTargetPair,
        HookM6Channel.associatedArrow] using
          (M.1.1.1.z_projective_and_z_to_a sigma AR).1
    first_injective := by
      simpa [HookM6Channel.commonTargetPair,
        HookM6Channel.associatedArrow] using M.1.1.2
    differentOrbit := M.1.1.commonTargetPair_differentOrbit sigma AR }

/-- The oriented endpoint occurrence retains the deep-anchor outer `M6`
term. -/
theorem firstProjectiveInjectiveDifferentOrbitOuterPair_injective :
    Function.Injective
      (firstProjectiveInjectiveDifferentOrbitOuterPair sigma AR) := by
  intro M N h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply HookM6Channel.commonTargetPair_injective sigma AR
  exact congrArg FirstProjectiveInjectiveDifferentOrbitOuterPair.pair h

end HookM6Channel.InjectiveFourthDeepAnchor

/-- Exact oriented occurrence image of deep-anchor outer `M6`. -/
abbrev FirstPIDeepM6Image :=
  Set.range
    (HookM6Channel.InjectiveFourthDeepAnchor.firstProjectiveInjectiveDifferentOrbitOuterPair
      sigma AR)

noncomputable instance firstPIDeepM6ImageFintype :
    Fintype (AR.FirstPIDeepM6Image sigma) := Fintype.ofFinite _

/-- Deep-anchor outer `M6` is exactly equivalent to its intrinsic oriented
labelled-occurrence image. -/
def hookM6DeepAnchorEquivFirstPIImage :
    HookM6Channel.InjectiveFourthDeepAnchor sigma AR ≃
      AR.FirstPIDeepM6Image sigma :=
  Equiv.ofInjective
    (HookM6Channel.InjectiveFourthDeepAnchor.firstProjectiveInjectiveDifferentOrbitOuterPair
      sigma AR)
    (HookM6Channel.InjectiveFourthDeepAnchor.firstProjectiveInjectiveDifferentOrbitOuterPair_injective
      sigma AR)

/-- Fully intrinsic presentation of the surviving outer endpoint family
after the two exact outer `M6` overlaps have been cancelled. -/
abbrev IntrinsicSurvivingOuterEndpointFamily :=
  AR.FirstPIDeepM6Image sigma ⊕
    (AR.FirstPISecondProjectiveM6Complement (K := K) sigma ⊕
      (AR.FirstPISecondInteriorM6Complement (K := K) sigma ⊕
        AR.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair
          sigma))

noncomputable instance intrinsicSurvivingOuterEndpointFamilyFintype :
    Fintype (AR.IntrinsicSurvivingOuterEndpointFamily (K := K) sigma) :=
  inferInstance

include K AR in
/-- The channel-labelled surviving outer family is exactly equivalent to
its four intrinsic endpoint strata. -/
def survivingOuterEndpointFamilyEquivIntrinsic :
    SurvivingOuterEndpointFamily (K := K) sigma AR ≃
      AR.IntrinsicSurvivingOuterEndpointFamily (K := K) sigma :=
  Equiv.sumCongr (hookM6DeepAnchorEquivFirstPIImage sigma AR)
    (Equiv.sumCongr
      (hookWallBadUM6ProjectiveAnchorComplementEquivIntrinsic
        (K := K) sigma AR)
      (hookWallBadBM6SecondBoundaryComplementEquivIntrinsicSumTranslatedTarget
        (K := K) sigma AR))

namespace FirstPIDeepM6Image

variable (p : AR.FirstPIDeepM6Image sigma)

/-- The second source of a deep outer `M6` occurrence is nonprojective. -/
theorem second_nonprojective :
    ¬ Projective (sigma.obj p.1.pair.1.2.1.1) := by
  rcases p with ⟨_, ⟨M, rfl⟩⟩
  simpa [HookM6Channel.InjectiveFourthDeepAnchor.firstProjectiveInjectiveDifferentOrbitOuterPair,
    HookM6Channel.commonTargetPair] using M.1.2

/-- The second source of a deep outer `M6` occurrence is noninjective. -/
theorem second_noninjective :
    ¬ Injective (sigma.obj p.1.pair.1.2.1.1) := by
  rcases p with ⟨_, ⟨M, rfl⟩⟩
  simpa [HookM6Channel.InjectiveFourthDeepAnchor.firstProjectiveInjectiveDifferentOrbitOuterPair,
    HookM6Channel.commonTargetPair] using
      (M.1.1.1.hookOrbitAnchor_isInterior sigma AR).2

/-- The second arrow of a deep outer `M6` occurrence lies beyond the first
two trimmed source layers. -/
theorem second_not_twoSource :
    let H := toInteriorArrow sigma AR p.1.pair.1.2
      ⟨by
        rw [← p.1.pair.2]
        exact p.1.target_nonprojective,
      FirstPIDeepM6Image.second_noninjective sigma AR p⟩
    ¬ ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      H := by
  rcases p with ⟨_, ⟨M, rfl⟩⟩
  simpa [HookM6Channel.InjectiveFourthDeepAnchor.firstProjectiveInjectiveDifferentOrbitOuterPair,
    HookM6Channel.commonTargetPair] using M.2

end FirstPIDeepM6Image

/-- Forget the four intrinsic surviving channel names while retaining the
single oriented common-target occurrence. -/
def intrinsicSurvivingOuterEndpointPair :
    AR.IntrinsicSurvivingOuterEndpointFamily (K := K) sigma →
      AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma
  | Sum.inl M => M.1
  | Sum.inr (Sum.inl W) => W.1.1
  | Sum.inr (Sum.inr (Sum.inl W)) => W.1.outer
  | Sum.inr (Sum.inr (Sum.inr W)) => W.outer

include AR in
/-- The four intrinsic surviving outer strata are pairwise disjoint and
injective in the common oriented endpoint space. -/
theorem intrinsicSurvivingOuterEndpointPair_injective :
    Function.Injective
      (intrinsicSurvivingOuterEndpointPair (K := K) sigma AR) := by
  intro X Y h
  rcases X with M | X
  · rcases Y with N | Y
    · exact congrArg Sum.inl (Subtype.ext h)
    · rcases Y with W | Y
      · exfalso
        change M.1 = W.1.1 at h
        have hs := congrArg
          (fun p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma ↦
            p.pair.1.2.1.1) h
        apply FirstPIDeepM6Image.second_nonprojective sigma AR M
        rw [hs]
        exact W.1.2.1
      · rcases Y with W | W
        · exfalso
          change M.1 = W.1.outer at h
          apply FirstPIDeepM6Image.second_not_twoSource sigma AR M
          convert W.1.second_twoSource using 1
          apply Subtype.ext
          exact congrArg
            (fun p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma ↦
              p.pair.1.2) h
        · exfalso
          change M.1 = W.outer at h
          have hs := congrArg
            (fun p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma ↦
              p.pair.1.2.1.1) h
          apply FirstPIDeepM6Image.second_noninjective sigma AR M
          exact (congrArg sigma.obj hs.symm) ▸ W.second_injective
  · rcases X with W | X
    · rcases Y with M | Y
      · exfalso
        change W.1.1 = M.1 at h
        have hs := congrArg
          (fun p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma ↦
            p.pair.1.2.1.1) h
        apply FirstPIDeepM6Image.second_nonprojective sigma AR M
        rw [← hs]
        exact W.1.2.1
      · rcases Y with Z | Y
        · have hW : W = Z := by
            apply Subtype.ext
            apply Subtype.ext
            exact h
          exact congrArg (fun Q ↦ Sum.inr (Sum.inl Q)) hW
        · rcases Y with Z | Z
          · exfalso
            change W.1.1 = Z.1.outer at h
            have hs := congrArg
              (fun p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma ↦
                p.pair.1.2.1.1) h
            apply Z.1.second_nonprojective
            rw [← hs]
            exact W.1.2.1
          · exfalso
            change W.1.1 = Z.outer at h
            have hs := congrArg
              (fun p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma ↦
                p.pair.1.2.1.1) h
            apply Z.second_nonprojective
            rw [← hs]
            exact W.1.2.1
    · rcases X with W | W
      · rcases Y with M | Y
        · exfalso
          change W.1.outer = M.1 at h
          apply FirstPIDeepM6Image.second_not_twoSource sigma AR M
          convert W.1.second_twoSource using 1
          apply Subtype.ext
          exact congrArg
            (fun p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma ↦
              p.pair.1.2) h.symm
        · rcases Y with Z | Y
          · exfalso
            change W.1.outer = Z.1.1 at h
            have hs := congrArg
              (fun p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma ↦
                p.pair.1.2.1.1) h
            apply W.1.second_nonprojective
            rw [hs]
            exact Z.1.2.1
          · rcases Y with Z | Z
            · have hW : W = Z := by
                apply Subtype.ext
                apply FirstPISecondInteriorTwoSourceOuterPair.ext
                exact h
              exact congrArg
                (fun Q ↦ Sum.inr (Sum.inr (Sum.inl Q))) hW
            · exfalso
              change W.1.outer = Z.outer at h
              have hs := congrArg
                (fun p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma ↦
                  p.pair.1.2.1.1) h
              apply W.1.second_noninjective
              rw [hs]
              exact Z.second_injective
      · rcases Y with M | Y
        · exfalso
          change W.outer = M.1 at h
          have hs := congrArg
            (fun p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma ↦
              p.pair.1.2.1.1) h
          apply FirstPIDeepM6Image.second_noninjective sigma AR M
          exact (congrArg sigma.obj hs) ▸ W.second_injective
        · rcases Y with Z | Y
          · exfalso
            change W.outer = Z.1.1 at h
            have hs := congrArg
              (fun p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma ↦
                p.pair.1.2.1.1) h
            apply W.second_nonprojective
            rw [hs]
            exact Z.1.2.1
          · rcases Y with Z | Z
            · exfalso
              change W.outer = Z.1.outer at h
              have hs := congrArg
                (fun p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma ↦
                  p.pair.1.2.1.1) h
              apply Z.1.second_noninjective
              rw [← hs]
              exact W.second_injective
            · have hW : W = Z :=
                FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair.ext h
              exact congrArg
                (fun Q ↦ Sum.inr (Sum.inr (Sum.inr Q))) hW

/-- Exact oriented common-target image of the four intrinsic surviving outer
endpoint strata. -/
abbrev IntrinsicSurvivingOuterEndpointImage :=
  Set.range (intrinsicSurvivingOuterEndpointPair (K := K) sigma AR)

noncomputable instance intrinsicSurvivingOuterEndpointImageFintype :
    Fintype
      (AR.IntrinsicSurvivingOuterEndpointImage (K := K) sigma) :=
  Fintype.ofFinite _

/-- The intrinsic surviving family is exactly equivalent to its disjoint
oriented occurrence image. -/
def intrinsicSurvivingOuterEndpointEquivImage :
    AR.IntrinsicSurvivingOuterEndpointFamily (K := K) sigma ≃
      AR.IntrinsicSurvivingOuterEndpointImage (K := K) sigma :=
  Equiv.ofInjective
    (intrinsicSurvivingOuterEndpointPair (K := K) sigma AR)
    (intrinsicSurvivingOuterEndpointPair_injective
      (K := K) sigma AR)

include K AR in
omit [DecidableEq iota] in
/-- Cardinal form of the exact intrinsic `M2` endpoint classification. -/
theorem hookWallBadUInjectiveFourth_card_eq_firstPISecondProjectiveNoninjective :
    Fintype.card (HookWallBadU.InjectiveFourthEndpoint sigma AR) =
      Fintype.card
        (AR.FirstPISecondProjectiveNoninjectiveOuterPair sigma) :=
  Fintype.card_congr
    (hookWallBadUInjectiveFourthEquivFirstPISecondProjectiveNoninjective
      (K := K) sigma AR)

include K AR in
omit [DecidableEq iota] in
/-- Cardinal form of the intrinsic surviving-second-arrow `M3`
classification. -/
theorem hookWallBadBInjectiveFirstSecondNoninjective_card_eq_secondInteriorTwoSource :
    Fintype.card
        (HookWallBadBUnrestricted.InjectiveFirstSecondNoninjective
          sigma AR) =
      Fintype.card (AR.FirstPISecondInteriorTwoSourceOuterPair sigma) :=
  Fintype.card_congr
    (hookWallBadBInjectiveFirstSecondNoninjectiveEquivFirstPISecondInteriorTwoSource
      (K := K) sigma AR)

include K AR in
omit [DecidableEq iota] in
/-- Cardinal form of the complete two-stratum intrinsic outer `M3`
classification. -/
theorem hookWallBadBInjectiveFirst_card_eq_intrinsicSecondEndpointSum :
    Fintype.card
        (HookWallBadBUnrestricted.InjectiveEndpointFirstInjective
          sigma AR) =
      Fintype.card (AR.FirstPISecondInteriorTwoSourceOuterPair sigma) +
        Fintype.card
          (AR.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair
            sigma) := by
  rw [Fintype.card_congr
    (hookWallBadBInjectiveFirstEquivIntrinsicSecondEndpointSum
      (K := K) sigma AR)]
  exact Fintype.card_sum

omit [DecidableEq iota] in
/-- Cardinal split of injective-first outer `M3` into its surviving second
arrow and injective-second-source endpoint parts. -/
theorem hookWallBadBInjectiveFirst_card_eq_secondNoninjective_add_secondInjective :
    Fintype.card
        (HookWallBadBUnrestricted.InjectiveEndpointFirstInjective
          sigma AR) =
      Fintype.card
          (HookWallBadBUnrestricted.InjectiveFirstSecondNoninjective
            sigma AR) +
        Fintype.card
          (HookWallBadBUnrestricted.InjectiveFirstSecondInjective
            sigma AR) := by
  rw [Fintype.card_congr
    (hookWallBadBInjectiveFirstEquivSecondNoninjectiveSumInjective
      sigma AR)]
  exact Fintype.card_sum

include K AR in
/-- Cardinal form of the complete intrinsic classification of the unused
outer `M3` complement. -/
theorem hookWallBadBM6SecondBoundaryComplement_card_eq_intrinsic :
    Fintype.card
        (HookWallBadBUnrestricted.M6SecondBoundaryComplement
          (K := K) sigma AR) =
      Fintype.card
          (AR.FirstPISecondInteriorM6Complement (K := K) sigma) +
        Fintype.card
          (AR.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair
            sigma) := by
  rw [Fintype.card_congr
    (hookWallBadBM6SecondBoundaryComplementEquivIntrinsicSumTranslatedTarget
      (K := K) sigma AR)]
  exact Fintype.card_sum

include K AR in
/-- Cardinal form of the exact intrinsic different-component outer `M5`
classification. -/
theorem hookM5NoProjectiveFirst_card_eq_firstNISIDifferentOrbit :
    Fintype.card
        (HookM5Preliminary.InjectiveMiddleNoProjectiveFirst sigma AR) =
      Fintype.card
        (AR.FirstNISINoProjectiveDifferentOrbitOuterPair sigma) :=
  Fintype.card_congr
    (hookM5NoProjectiveFirstEquivDifferentOrbit (K := K) sigma AR)

include K AR in
/-- The actual no-projective outer `M5` family has the cardinality of its
exact image inside the full different-component injective-source endpoint. -/
theorem hookM5NoProjectiveFirst_card_eq_differentOrbitImage :
    Fintype.card
        (HookM5Preliminary.InjectiveMiddleNoProjectiveFirst sigma AR) =
      Fintype.card
        (AR.FirstNISINoProjectiveDifferentOrbitImage sigma) := by
  rw [AR.hookM5NoProjectiveFirst_card_eq_firstNISIDifferentOrbit
    (K := K) sigma]
  exact Fintype.card_congr
    (AR.firstNISINoProjectiveDifferentOrbitEquivImage sigma)

include K AR in
/-- Cardinal form of the four-stratum intrinsic surviving outer endpoint
classification. -/
theorem intrinsicSurvivingOuterEndpointFamily_card_eq :
    Fintype.card
        (SurvivingOuterEndpointFamily (K := K) sigma AR) =
      Fintype.card
          (AR.FirstPIDeepM6Image sigma) +
        Fintype.card
          (AR.FirstPISecondProjectiveM6Complement (K := K) sigma) +
        Fintype.card
          (AR.FirstPISecondInteriorM6Complement (K := K) sigma) +
        Fintype.card
          (AR.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair
            sigma) := by
  rw [Fintype.card_congr
    (survivingOuterEndpointFamilyEquivIntrinsic (K := K) sigma AR)]
  change Fintype.card
      (AR.FirstPIDeepM6Image sigma ⊕
        (AR.FirstPISecondProjectiveM6Complement (K := K) sigma ⊕
          (AR.FirstPISecondInteriorM6Complement (K := K) sigma ⊕
            AR.FirstPISecondInjectiveTranslatedTargetProjectiveOuterPair
              sigma))) = _
  simp only [Fintype.card_sum]
  omega

end OpConjecture.IndecomposableSkeleton.FiniteARTranslationData

namespace OpConjecture.IndecomposableSkeleton.AlignedBiduality

universe u v w

variable {K R S : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [Ring S] [Algebra K S] [FiniteDimensional K S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {iota : Type v} {kappa : Type w} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)
  (tau : IndecomposableSkeleton.{u, w, u} S kappa)
  (D : AlignedBiduality sigma tau)
  (ARsigma : sigma.FiniteARTranslationData)
  (ARtau : tau.FiniteARTranslationData)

/-- Reassociate the different-component and no-projective-source subtype
predicates on the dual injective-source endpoint. -/
def differentOrbitInjectiveSourceNoProjectiveReorder :
    {p : ARtau.DifferentOrbitInjectiveSourceCommonTargetPair tau //
      ¬ (Projective (tau.obj p.1.1.1.1.1.1) ∨
        Projective (tau.obj p.1.1.1.2.1.1))} ≃
      ARtau.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
        tau where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

include D in
/-- Aligned duality identifies the no-projective injective-source endpoint
with the common-source endpoint whose two arrow targets are noninjective.
This is the exact source-coordinate form needed for the remaining endpoint
incidence partition. -/
def differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivNoProjective :
    ARsigma.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair
        sigma ≃
      ARtau.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
        tau := by
  let E :=
    D.differentOrbitProjectiveTargetCommonSourceEquivInjectiveSourceCommonTarget
      sigma tau ARsigma ARtau
  let F :
      ARsigma.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair
          sigma ≃
        {p : ARtau.DifferentOrbitInjectiveSourceCommonTargetPair tau //
          ¬ (Projective (tau.obj p.1.1.1.1.1.1) ∨
            Projective (tau.obj p.1.1.1.2.1.1))} := by
    apply E.subtypeEquiv
    intro p
    have hfirst := D.forward.injective_iff_projective_image sigma tau
      p.1.1.1.1.1.2
    have hsecond := D.forward.injective_iff_projective_image sigma tau
      p.1.1.1.2.1.2
    simpa [E,
      differentOrbitProjectiveTargetCommonSourceEquivInjectiveSourceCommonTarget,
      projectiveTargetCommonSourceEquivInjectiveSourceCommonTarget,
      commonTargetEquivCommonSource, pushforwardIrreduciblePair] using
        and_congr (not_congr hfirst) (not_congr hsecond)
  exact F.trans
    (differentOrbitInjectiveSourceNoProjectiveReorder tau ARtau)

include K D ARsigma ARtau in
/-- The oriented full endpoint transport is pointwise: advancing the dual
projective-target common-source pair identifies the source trimmed literal
boundary with the target injective-source/no-projective-source endpoint. -/
def interiorDifferentOrbitLiteralEquivNoProjective :
    ARsigma.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma ≃
      ARtau.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
        tau :=
  (ARsigma.differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivInteriorLiteral
    (K := K) sigma).symm.trans
      (D.differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivNoProjective
        sigma tau ARsigma ARtau)

omit [Algebra K S] [FiniteDimensional K S] in
include K D ARsigma ARtau in
/-- Cardinal form of the oriented trimmed-literal/full-endpoint
equivalence. -/
theorem interiorDifferentOrbitLiteral_card_eq_noProjective :
    Fintype.card
        (ARsigma.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma) =
      Fintype.card
        (ARtau.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
          tau) :=
  Fintype.card_congr
    (D.interiorDifferentOrbitLiteralEquivNoProjective
      (K := K) sigma tau ARsigma ARtau)

include D in
/-- The first-projective-target source orientation becomes exactly the
first-injective-source target orientation under aligned duality. -/
def differentOrbitFirstProjectiveTargetNoninjectiveCommonSourceEquivFirstInjective :
    ARsigma.DifferentOrbitFirstProjectiveTargetNoninjectiveCommonSourcePair
        sigma ≃
      ARtau.DifferentOrbitNoProjectiveFirstInjectivePair tau := by
  let E :=
    D.differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivNoProjective
      sigma tau ARsigma ARtau
  apply E.subtypeEquiv
  intro p
  have h := D.forward.projective_iff_injective_image sigma tau
    p.1.1.1.1.1.1.2
  simpa [E,
    differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivNoProjective,
    differentOrbitInjectiveSourceNoProjectiveReorder,
    differentOrbitProjectiveTargetCommonSourceEquivInjectiveSourceCommonTarget,
    projectiveTargetCommonSourceEquivInjectiveSourceCommonTarget,
    commonTargetEquivCommonSource, pushforwardIrreduciblePair] using h

include K D ARsigma ARtau in
/-- The first-injective-source part of the target no-projective endpoint is
the crossed first-literal-source boundary.  Splitting its common target by
injectivity gives exactly the injective-target and noninjective-target
different-component first-boundary strata on the source skeleton. -/
def differentOrbitNoProjectiveFirstInjectiveEquivCrossedFirstBoundary :
    ARtau.DifferentOrbitNoProjectiveFirstInjectivePair tau ≃
      ARsigma.DifferentOrbitBoundaryM6InjectiveTargetPair sigma ⊕
        ARsigma.DifferentOrbitFirstSourceNoninjectiveTargetPair sigma :=
  (D.differentOrbitFirstProjectiveTargetNoninjectiveCommonSourceEquivFirstInjective
      sigma tau ARsigma ARtau).symm.trans <|
    (ARsigma.differentOrbitFirstProjectiveTargetEquivFirstLiteralSource
      (K := K) sigma).trans
        (ARsigma.interiorDifferentOrbitFirstLiteralSourceEquivInjectiveSumNoninjective
          sigma)

omit [Algebra K S] [FiniteDimensional K S] in
include K D ARsigma ARtau in
/-- Cardinal form of the crossed first-boundary endpoint split. -/
theorem differentOrbitNoProjectiveFirstInjective_card_eq_crossed_injective_add_noninjective :
    Fintype.card
        (ARtau.DifferentOrbitNoProjectiveFirstInjectivePair tau) =
      Fintype.card
          (ARsigma.DifferentOrbitBoundaryM6InjectiveTargetPair sigma) +
        Fintype.card
          (ARsigma.DifferentOrbitFirstSourceNoninjectiveTargetPair sigma) := by
  rw [Fintype.card_congr
    (D.differentOrbitNoProjectiveFirstInjectiveEquivCrossedFirstBoundary
      (K := K) sigma tau ARsigma ARtau)]
  exact Fintype.card_sum

include D in
/-- The complementary first-nonprojective-target source orientation becomes
the first-noninjective-source target orientation. -/
def differentOrbitFirstNonprojectiveTargetNoninjectiveCommonSourceEquivFirstNoninjective :
    ARsigma.DifferentOrbitFirstNonprojectiveTargetNoninjectiveCommonSourcePair
        sigma ≃
      ARtau.DifferentOrbitNoProjectiveFirstNoninjectivePair tau := by
  let E :=
    D.differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivNoProjective
      sigma tau ARsigma ARtau
  apply E.subtypeEquiv
  intro p
  have h := D.forward.projective_iff_injective_image sigma tau
    p.1.1.1.1.1.1.2
  exact not_congr (by
    simpa [E,
      differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivNoProjective,
      differentOrbitInjectiveSourceNoProjectiveReorder,
      differentOrbitProjectiveTargetCommonSourceEquivInjectiveSourceCommonTarget,
      projectiveTargetCommonSourceEquivInjectiveSourceCommonTarget,
      commonTargetEquivCommonSource, pushforwardIrreduciblePair] using h)

include K D ARsigma ARtau in
/-- Under aligned duality, the `M5` translated-target condition is exactly
injectivity of the inverse translate of the dual common source. -/
theorem inverseCommonSource_injective_iff_mem_firstNISINoProjectiveImage
    (q :
      ARsigma.DifferentOrbitFirstNonprojectiveTargetNoninjectiveCommonSourcePair
        sigma) :
    let E :=
      D.differentOrbitFirstNonprojectiveTargetNoninjectiveCommonSourceEquivFirstNoninjective
        sigma tau ARsigma ARtau
    Injective
        (sigma.obj (q.1.inverseCommonSource (K := K) sigma ARsigma).1) ↔
      (E q).1 ∈
        ARtau.FirstNISINoProjectiveDifferentOrbitImage tau := by
  let E :=
    D.differentOrbitFirstNonprojectiveTargetNoninjectiveCommonSourceEquivFirstNoninjective
      sigma tau ARsigma ARtau
  let inverseLabel : sigma.NonprojectiveLabel :=
    q.1.inverseCommonSource (K := K) sigma ARsigma
  have htargetNP := (E q).1.target_nonprojective (K := K) tau
  let targetLabel : tau.NonprojectiveLabel :=
    ⟨(E q).1.1.1.1.1.1.1.2, htargetNP⟩
  have htranslate :
      D.forward.labelEquiv inverseLabel.1 =
        (ARtau.arTranslation tau targetLabel).1 := by
    apply D.forward.labelEquiv.symm.injective
    have hdual :=
      D.forward_symm_arTranslation_eq_inverse
        sigma tau ARsigma ARtau targetLabel
    simpa [inverseLabel,
      FiniteARTranslationData.DifferentOrbitProjectiveTargetNoninjectiveCommonSourcePair.inverseCommonSource,
      targetLabel, E,
      differentOrbitFirstNonprojectiveTargetNoninjectiveCommonSourceEquivFirstNoninjective,
      differentOrbitProjectiveTargetNoninjectiveCommonSourceEquivNoProjective,
      differentOrbitInjectiveSourceNoProjectiveReorder,
      differentOrbitProjectiveTargetCommonSourceEquivInjectiveSourceCommonTarget,
      projectiveTargetCommonSourceEquivInjectiveSourceCommonTarget,
      commonTargetEquivCommonSource, pushforwardIrreduciblePair] using
        hdual.symm
  change Injective (sigma.obj inverseLabel.1) ↔ _
  rw [ARtau.mem_firstNISINoProjectiveDifferentOrbitImage_iff
    (K := K) tau]
  constructor
  · intro hinvI
    refine ⟨(E q).2, (E q).1.1.1.2.resolve_left (E q).2, ?_⟩
    have hP := (D.forward.injective_iff_projective_image sigma tau
      inverseLabel.1).1 hinvI
    rw [htranslate] at hP
    simpa [targetLabel] using hP
  · rintro ⟨_, _, htranslatedP⟩
    apply (D.forward.injective_iff_projective_image sigma tau
      inverseLabel.1).2
    rw [htranslate]
    simpa [targetLabel] using htranslatedP

include K D ARsigma ARtau in
/-- The source-coordinate endpoint with injective inverse translate is
exactly the outer no-projective `M5` image on the aligned dual skeleton. -/
def differentOrbitInverseInjectiveCommonSourceEquivM5Image :
    ARsigma.DifferentOrbitFirstNonprojectiveTargetInverseInjectiveCommonSourcePair
        (K := K) sigma ≃
      ARtau.FirstNISINoProjectiveDifferentOrbitImage tau := by
  let E :=
    D.differentOrbitFirstNonprojectiveTargetNoninjectiveCommonSourceEquivFirstNoninjective
      sigma tau ARsigma ARtau
  let F :
      ARsigma.DifferentOrbitFirstNonprojectiveTargetInverseInjectiveCommonSourcePair
          (K := K) sigma ≃
        {p : ARtau.DifferentOrbitNoProjectiveFirstNoninjectivePair tau //
          p.1 ∈ ARtau.FirstNISINoProjectiveDifferentOrbitImage tau} := by
    apply E.subtypeEquiv
    intro q
    exact D.inverseCommonSource_injective_iff_mem_firstNISINoProjectiveImage
      (K := K) sigma tau ARsigma ARtau q
  exact F.trans
    (ARtau.differentOrbitFirstNoninjectiveM5SubtypeEquivImage
      (K := K) tau)

omit [DecidableEq iota] in
include K D ARsigma ARtau in
/-- Crossed terminal/outer endpoint transport: the terminal
first-not-source stratum on the source skeleton is exactly the outer `M5`
image on the aligned dual skeleton. -/
def terminalFirstNotSourceEquivM5Image :
    ARsigma.InteriorTerminalFirstNotSourceCommonTargetPair sigma ≃
      ARtau.FirstNISINoProjectiveDifferentOrbitImage tau :=
  (ARsigma.differentOrbitInverseInjectiveCommonSourceEquivTerminalFirstNotSource
    (K := K) sigma).symm.trans
      (D.differentOrbitInverseInjectiveCommonSourceEquivM5Image
        (K := K) sigma tau ARsigma ARtau)

include K D ARsigma ARtau in
/-- Cardinal form of the crossed terminal/outer `M5` endpoint
equivalence. -/
theorem terminalFirstNotSource_card_eq_m5Image :
    Fintype.card
        (ARsigma.InteriorTerminalFirstNotSourceCommonTargetPair sigma) =
      Fintype.card
        (ARtau.FirstNISINoProjectiveDifferentOrbitImage tau) :=
  Fintype.card_congr
    (D.terminalFirstNotSourceEquivM5Image
      (K := K) sigma tau ARsigma ARtau)

include K D ARsigma ARtau in
/-- The complementary source-coordinate endpoint, whose inverse translate
is noninjective, is exactly the deep complement of the outer `M5` image. -/
def differentOrbitInverseNoninjectiveCommonSourceEquivDeep :
    ARsigma.DifferentOrbitFirstNonprojectiveTargetInverseNoninjectiveCommonSourcePair
        (K := K) sigma ≃
      ARtau.DifferentOrbitNoProjectiveFirstNoninjectiveDeepPair
        (K := K) tau := by
  let E :=
    D.differentOrbitFirstNonprojectiveTargetNoninjectiveCommonSourceEquivFirstNoninjective
      sigma tau ARsigma ARtau
  let F :
      ARsigma.DifferentOrbitFirstNonprojectiveTargetInverseNoninjectiveCommonSourcePair
          (K := K) sigma ≃
        {p : ARtau.DifferentOrbitNoProjectiveFirstNoninjectivePair tau //
          p.1 ∉ ARtau.FirstNISINoProjectiveDifferentOrbitImage tau} := by
    apply E.subtypeEquiv
    intro q
    exact not_congr
      (D.inverseCommonSource_injective_iff_mem_firstNISINoProjectiveImage
        (K := K) sigma tau ARsigma ARtau q)
  exact F.trans
    (ARtau.differentOrbitFirstNoninjectiveNotM5EquivDeep
      (K := K) tau)

omit [DecidableEq iota] in
include K D ARsigma ARtau in
/-- Crossed geometric form of the deep no-projective endpoint: it is the
first-not-source, noninjective-target part of the trimmed literal boundary
on the source skeleton. -/
def differentOrbitNoProjectiveDeepEquivCrossedFirstNotSourceNoninjectiveTarget :
    ARtau.DifferentOrbitNoProjectiveFirstNoninjectiveDeepPair
        (K := K) tau ≃
      ARsigma.InteriorDifferentOrbitFirstNotSourceNoninjectiveTargetPair
        sigma :=
  (D.differentOrbitInverseNoninjectiveCommonSourceEquivDeep
      (K := K) sigma tau ARsigma ARtau).symm.trans
    (ARsigma.differentOrbitInverseNoninjectiveCommonSourceEquivFirstNotSourceNoninjectiveTarget
      (K := K) sigma)

omit [DecidableEq iota] in
include K D ARsigma ARtau in
/-- After swapping the two labelled occurrences, the deep endpoint is
exactly the crossed noninjective first-boundary orientation whose second
occurrence is not a source. -/
def differentOrbitNoProjectiveDeepEquivCrossedFirstSourceSecondNotSource :
    ARtau.DifferentOrbitNoProjectiveFirstNoninjectiveDeepPair
        (K := K) tau ≃
      ARsigma.DifferentOrbitFirstSourceNoninjectiveTargetSecondNotSourcePair
        sigma :=
  (D.differentOrbitNoProjectiveDeepEquivCrossedFirstNotSourceNoninjectiveTarget
      (K := K) sigma tau ARsigma ARtau).trans
    (ARsigma.interiorDifferentOrbitFirstNotSourceNoninjectiveTargetEquivFirstSourceSecondNotSource
      sigma)

include K D ARsigma ARtau in
/-- Cardinal form of the crossed geometric description of the deep
no-projective endpoint. -/
theorem differentOrbitNoProjectiveDeep_card_eq_crossed_firstNotSource_noninjectiveTarget :
    Fintype.card
        (ARtau.DifferentOrbitNoProjectiveFirstNoninjectiveDeepPair
          (K := K) tau) =
      Fintype.card
        (ARsigma.InteriorDifferentOrbitFirstNotSourceNoninjectiveTargetPair
          sigma) :=
  Fintype.card_congr
    (D.differentOrbitNoProjectiveDeepEquivCrossedFirstNotSourceNoninjectiveTarget
      (K := K) sigma tau ARsigma ARtau)

include K D ARsigma ARtau in
/-- Cardinal form of the crossed second-not-source description of the deep
endpoint. -/
theorem differentOrbitNoProjectiveDeep_card_eq_crossed_firstSource_secondNotSource :
    Fintype.card
        (ARtau.DifferentOrbitNoProjectiveFirstNoninjectiveDeepPair
          (K := K) tau) =
      Fintype.card
        (ARsigma.DifferentOrbitFirstSourceNoninjectiveTargetSecondNotSourcePair
          sigma) :=
  Fintype.card_congr
    (D.differentOrbitNoProjectiveDeepEquivCrossedFirstSourceSecondNotSource
      (K := K) sigma tau ARsigma ARtau)

end OpConjecture.IndecomposableSkeleton.AlignedBiduality
