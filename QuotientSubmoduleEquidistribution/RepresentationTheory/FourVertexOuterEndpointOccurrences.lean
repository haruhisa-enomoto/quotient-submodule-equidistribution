import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexFullBoundaryEndpointStrata
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexChannelTrimComplements

/-!
# Occurrences carried by the four outer endpoint families

The normalized noninterior `M5` family gives a full common-target pair with
an injective source.  The normalized `M6`, `M2`, and `M3` families give the
outer intersection in which the common target is nonprojective and the
sources include both a projective and an injective.  The occurrence maps are
injective within each channel; cross-channel overlaps are left explicit for
the final endpoint classification.
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

omit [DecidableEq iota] in
/-- If the first arrow in a common-target pair starts at a
projective-injective object and the common target is nonprojective, then a
distinct second occurrence cannot lie in the same full mesh-rotation
component.  Indeed, the predecessor of the first arrow is the source of a
length-one component and the first arrow is already its target. -/
theorem commonTargetPair_differentOrbit_of_firstSource_projective_injective
    (p : CommonTargetArrowPair sigma)
    (ht : ¬ Projective (sigma.obj p.1.1.1.2))
    (hp : Projective (sigma.obj p.1.1.1.1))
    (hi : Injective (sigma.obj p.1.1.1.1))
    (hne : p.1.1 ≠ p.1.2) :
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit p.1.1 p.1.2 := by
  classical
  dsimp only
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let A := p.1.1
  let B := p.1.2
  intro hsame
  let qsub := O.tau ⟨A, ht⟩
  let q := qsub.1
  have hqSource : Projective (sigma.obj q.1.2) := by
    have hval := M.arrowOrbitData_tau_val sigma ⟨A, ht⟩
    rw [show q.1.2 = A.1.1 from congrArg Prod.snd hval]
    exact hp
  have hqSuccessor : O.successor q = A := by
    change (if hx : Injective (sigma.obj q.1.1) then q
      else (O.tau.symm ⟨q, hx⟩).1) = A
    rw [dif_neg qsub.2]
    exact congrArg Subtype.val (O.tau.symm_apply_apply ⟨A, ht⟩)
  have hqA : O.SameSuccessorOrbit q A :=
    ⟨1, 0, by simpa only [Function.iterate_one,
      Function.iterate_zero, id_eq] using hqSuccessor⟩
  have hqB := O.sameSuccessorOrbit_trans hqA hsame
  obtain ⟨r, hr⟩ :=
    O.exists_iterate_eq_of_mem_source_of_sameSuccessorOrbit hqSource hqB
  have hATarget : Injective (sigma.obj A.1.1) := hi
  cases r with
  | zero =>
      apply ht
      rw [p.2]
      have hqeq : q = B := by
        simpa only [Function.iterate_zero, id_eq] using hr
      change Projective (sigma.obj B.1.2)
      rw [← hqeq]
      exact hqSource
  | succ r =>
      apply hne
      have hiter : (O.successor^[Nat.succ r]) q = A := by
        rw [Function.iterate_succ_apply, hqSuccessor]
        exact O.iterate_eq_self_of_mem_target A hATarget r
      exact hiter.symm.trans hr

namespace HookM5Preliminary.InjectiveMiddleEndpoint

variable (M : HookM5Preliminary.InjectiveMiddleEndpoint sigma AR)

/-- The full common-target occurrence of an outer preliminary `M5` term has
an injective second source. -/
def injectiveSourcePair : InjectiveSourceCommonTargetPair sigma := by
  refine ⟨M.1.commonTargetPair sigma AR, Or.inr ?_⟩
  change Injective (sigma.obj (M.1.hookArrow sigma AR).1.1)
  simpa [HookM5Preliminary.hookArrow, M.2.1,
    StripAdmissibleTriple.secondArrow] using M.2.2

/-- The labelled endpoint occurrence retains the entire preliminary term. -/
theorem injectiveSourcePair_injective :
    Function.Injective (injectiveSourcePair sigma AR) := by
  intro M N h
  apply Subtype.ext
  apply HookM5Preliminary.commonTargetPair_injective sigma AR
  exact congrArg Subtype.val h

end HookM5Preliminary.InjectiveMiddleEndpoint

namespace HookM6Channel.InjectiveFourthEndpoint

variable (M : HookM6Channel.InjectiveFourthEndpoint sigma AR)

/-- An outer `M6` endpoint has a nonprojective common target and its first
source is projective-injective. -/
def outerIntersectionPair :
    NonprojectiveTargetProjectiveInjectiveSourcePair sigma := by
  refine ⟨⟨M.1.commonTargetPair sigma AR, ?_, ?_⟩, ?_⟩
  · simpa [HookM6Channel.commonTargetPair,
      HookM6Channel.associatedArrow] using M.1.2
  · left
    simpa [HookM6Channel.commonTargetPair,
      HookM6Channel.associatedArrow] using
        (M.1.z_projective_and_z_to_a sigma AR).1
  · left
    simpa [HookM6Channel.commonTargetPair,
      HookM6Channel.associatedArrow] using M.2

/-- The labelled outer-intersection occurrence retains the `M6` term. -/
theorem outerIntersectionPair_injective :
    Function.Injective (outerIntersectionPair sigma AR) := by
  intro M N h
  apply Subtype.ext
  apply HookM6Channel.commonTargetPair_injective sigma AR
  exact congrArg (fun p ↦ p.1.1) h

/-- The full common-target square shift fixes every outer `M6`
occurrence, since its first source is projective-injective. -/
theorem commonTargetBoundaryEquiv_sourceBoundaryPair :
    (AR.commonTargetBoundaryEquiv sigma
      (M.1.sourceBoundaryPair sigma AR)).1 =
        M.1.commonTargetPair sigma AR := by
  simpa only [HookM6Channel.sourceBoundaryPair] using
    AR.commonTargetBoundaryEquiv_apply_of_firstSource_projective_injective
      sigma (M.1.commonTargetPair sigma AR)
        (by
          simpa [HookM6Channel.commonTargetPair,
            HookM6Channel.associatedArrow] using
              (M.1.z_projective_and_z_to_a sigma AR).1)
        (by
          simpa [HookM6Channel.commonTargetPair,
            HookM6Channel.associatedArrow] using M.2)

/-- Every outer `M6` labelled endpoint pair lies on two different full
arrow components. -/
theorem commonTargetPair_differentOrbit :
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit
      (M.1.commonTargetPair sigma AR).1.1
      (M.1.commonTargetPair sigma AR).1.2 := by
  apply AR.commonTargetPair_differentOrbit_of_firstSource_projective_injective
    sigma (M.1.commonTargetPair sigma AR)
  · simpa [HookM6Channel.commonTargetPair,
      HookM6Channel.associatedArrow] using M.1.2
  · simpa [HookM6Channel.commonTargetPair,
      HookM6Channel.associatedArrow] using
        (M.1.z_projective_and_z_to_a sigma AR).1
  · simpa [HookM6Channel.commonTargetPair,
      HookM6Channel.associatedArrow] using M.2
  · intro hEq
    have hs := congrArg
      (fun q : sigma.IrreduciblePair ↦ q.1.1) hEq
    have hs' : M.1.1.z =
        (M.1.1.triple.hookOrbitAnchor sigma AR).1.1 := by
      simpa [HookM6Channel.commonTargetPair,
        HookM6Channel.associatedArrow] using hs
    have hanchorNI := (M.1.hookOrbitAnchor_isInterior sigma AR).2
    apply hanchorNI
    rw [← hs']
    simpa [HookM6Channel.commonTargetPair,
      HookM6Channel.associatedArrow] using M.2

/-- The outer `M6` occurrence as an element of the intrinsic
different-component projective/injective-source corner. -/
def differentOrbitOuterIntersectionPair :
    AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
      sigma :=
  ⟨M.outerIntersectionPair sigma AR,
    M.commonTargetPair_differentOrbit sigma AR⟩

/-- The different-component endpoint encoding still retains the outer
`M6` term. -/
theorem differentOrbitOuterIntersectionPair_injective :
    Function.Injective (differentOrbitOuterIntersectionPair sigma AR) := by
  intro M N h
  apply HookM6Channel.InjectiveFourthEndpoint.outerIntersectionPair_injective
    sigma AR
  exact congrArg Subtype.val h

end HookM6Channel.InjectiveFourthEndpoint

namespace HookWallBadU.InjectiveFourthEndpoint

variable (W : HookWallBadU.InjectiveFourthEndpoint sigma AR)

/-- An outer `M2` endpoint has a nonprojective common target and its first
source is projective-injective. -/
def outerIntersectionPair :
    NonprojectiveTargetProjectiveInjectiveSourcePair sigma := by
  refine ⟨⟨W.1.commonTargetPair sigma AR, ?_, ?_⟩, ?_⟩
  · simpa [HookWallBadU.commonTargetPair,
      HookWallBadU.associatedArrow] using W.1.1.triple.u_nonprojective
  · left
    simpa [HookWallBadU.commonTargetPair,
      HookWallBadU.associatedArrow] using W.1.1.z_projective
  · left
    simpa [HookWallBadU.commonTargetPair,
      HookWallBadU.associatedArrow] using W.2

omit [Fintype iota] [DecidableEq iota] in
/-- The labelled outer-intersection occurrence retains the `M2` term. -/
theorem outerIntersectionPair_injective :
    Function.Injective (outerIntersectionPair sigma AR) := by
  intro W Z h
  apply Subtype.ext
  apply HookWallBadU.commonTargetPair_injective sigma AR
  exact congrArg (fun p ↦ p.1.1) h

omit [DecidableEq iota] in
/-- The full common-target square shift fixes every outer `M2`
occurrence, since its first source is projective-injective. -/
theorem commonTargetBoundaryEquiv_sourceBoundaryPair :
    (AR.commonTargetBoundaryEquiv sigma
      (W.1.sourceBoundaryPair sigma AR)).1 =
        W.1.commonTargetPair sigma AR := by
  simpa only [HookWallBadU.sourceBoundaryPair] using
    AR.commonTargetBoundaryEquiv_apply_of_firstSource_projective_injective
      sigma (W.1.commonTargetPair sigma AR)
        (by
          simpa [HookWallBadU.commonTargetPair,
            HookWallBadU.associatedArrow] using W.1.1.z_projective)
        (by
          simpa [HookWallBadU.commonTargetPair,
            HookWallBadU.associatedArrow] using W.2)

omit [DecidableEq iota] in
/-- Every outer `M2` labelled endpoint pair lies on two different full
arrow components. -/
theorem commonTargetPair_differentOrbit :
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit
      (W.1.commonTargetPair sigma AR).1.1
      (W.1.commonTargetPair sigma AR).1.2 := by
  apply AR.commonTargetPair_differentOrbit_of_firstSource_projective_injective
    sigma (W.1.commonTargetPair sigma AR)
  · simpa [HookWallBadU.commonTargetPair,
      HookWallBadU.associatedArrow] using W.1.1.triple.u_nonprojective
  · simpa [HookWallBadU.commonTargetPair,
      HookWallBadU.associatedArrow] using W.1.1.z_projective
  · simpa [HookWallBadU.commonTargetPair,
      HookWallBadU.associatedArrow] using W.2
  · intro hEq
    have hs := congrArg
      (fun q : sigma.IrreduciblePair ↦ q.1.1) hEq
    have hs' : W.1.1.z = W.1.1.triple.a := by
      simpa [HookWallBadU.commonTargetPair,
        HookWallBadU.associatedArrow,
        StripAdmissibleTriple.firstArrow] using hs
    apply W.1.1.triple.a_noninjective sigma AR
    rw [← hs']
    simpa [HookWallBadU.commonTargetPair,
      HookWallBadU.associatedArrow] using W.2

/-- The outer `M2` occurrence as an element of the intrinsic
different-component projective/injective-source corner. -/
def differentOrbitOuterIntersectionPair :
    AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
      sigma :=
  ⟨W.outerIntersectionPair sigma AR,
    W.commonTargetPair_differentOrbit sigma AR⟩

omit [DecidableEq iota] in
/-- The different-component endpoint encoding still retains the outer
`M2` term. -/
theorem differentOrbitOuterIntersectionPair_injective :
    Function.Injective (differentOrbitOuterIntersectionPair sigma AR) := by
  intro W Z h
  apply HookWallBadU.InjectiveFourthEndpoint.outerIntersectionPair_injective
    sigma AR
  exact congrArg Subtype.val h

end HookWallBadU.InjectiveFourthEndpoint

namespace HookWallBadBUnrestricted.InjectiveEndpoint

variable (W : HookWallBadBUnrestricted.InjectiveEndpoint sigma AR)

/-- An outer `M3` endpoint has a nonprojective common target, a projective
first source, and an injective source in one of the two coordinates. -/
def outerIntersectionPair :
    NonprojectiveTargetProjectiveInjectiveSourcePair sigma := by
  refine ⟨⟨W.1.commonTargetPair sigma AR, ?_, ?_⟩, ?_⟩
  · simpa [HookWallBadBUnrestricted.commonTargetPair,
      HookWallBadBUnrestricted.associatedArrow] using
        W.1.1.triple.b_nonprojective
  · left
    simpa [HookWallBadBUnrestricted.commonTargetPair,
      HookWallBadBUnrestricted.associatedArrow] using W.1.1.z_projective
  · simpa [HookWallBadBUnrestricted.commonTargetPair,
      HookWallBadBUnrestricted.associatedArrow,
      StripAdmissibleTriple.secondArrow] using W.2

omit [Fintype iota] [DecidableEq iota] in
/-- The labelled outer-intersection occurrence retains the `M3` term. -/
theorem outerIntersectionPair_injective :
    Function.Injective (outerIntersectionPair sigma AR) := by
  intro W Z h
  apply Subtype.ext
  apply HookWallBadBUnrestricted.commonTargetPair_injective sigma AR
  exact congrArg (fun p ↦ p.1.1) h

end HookWallBadBUnrestricted.InjectiveEndpoint

/-- Outer preliminary `M5` terms whose rotated first occurrence starts at
a projective. -/
abbrev HookM5Preliminary.InjectiveMiddleProjectiveFirst :=
  {M : HookM5Preliminary.InjectiveMiddleEndpoint sigma AR //
    Projective
      (sigma.obj (M.1.rotatedAssociatedArrow sigma AR).1.1)}

/-- Outer preliminary `M5` terms whose rotated first occurrence does not
start at a projective. -/
abbrev HookM5Preliminary.InjectiveMiddleNoProjectiveFirst :=
  {M : HookM5Preliminary.InjectiveMiddleEndpoint sigma AR //
    ¬ Projective
      (sigma.obj (M.1.rotatedAssociatedArrow sigma AR).1.1)}

noncomputable instance
    hookM5PreliminaryInjectiveMiddleProjectiveFirstFintype :
    Fintype
      (HookM5Preliminary.InjectiveMiddleProjectiveFirst sigma AR) :=
  Fintype.ofFinite _

noncomputable instance
    hookM5PreliminaryInjectiveMiddleNoProjectiveFirstFintype :
    Fintype
      (HookM5Preliminary.InjectiveMiddleNoProjectiveFirst sigma AR) :=
  Fintype.ofFinite _

/-- Exhaustive split of outer preliminary `M5` at the projective-source
corner. -/
def hookM5PreliminaryInjectiveMiddleEquivProjectiveSumNoProjective :
    HookM5Preliminary.InjectiveMiddleEndpoint sigma AR ≃
      HookM5Preliminary.InjectiveMiddleProjectiveFirst sigma AR ⊕
        HookM5Preliminary.InjectiveMiddleNoProjectiveFirst sigma AR where
  toFun M := by
    classical
    by_cases h : Projective
        (sigma.obj (M.1.rotatedAssociatedArrow sigma AR).1.1)
    · exact Sum.inl ⟨M, h⟩
    · exact Sum.inr ⟨M, h⟩
  invFun M := by
    rcases M with M | M
    · exact M.1
    · exact M.1
  left_inv M := by
    classical
    by_cases h : Projective
        (sigma.obj (M.1.rotatedAssociatedArrow sigma AR).1.1)
    · simp [h]
    · simp [h]
  right_inv M := by
    classical
    rcases M with M | M
    · simp [M.2]
    · simp [M.2]

namespace HookM5Preliminary.InjectiveMiddleNoProjectiveFirst

variable (M : HookM5Preliminary.InjectiveMiddleNoProjectiveFirst sigma AR)

/-- The nonprojective-first part of outer `M5` lands in the residual full
endpoint stratum with an injective source and no projective source. -/
def injectiveSourceNoProjectivePair :
    InjectiveSourceNoProjectiveSourceCommonTargetPair sigma := by
  refine ⟨M.1.injectiveSourcePair sigma AR, ?_⟩
  intro h
  rcases h with hfirst | hsecond
  · exact M.2 hfirst
  · apply M.1.1.triple.u_nonprojective
    change Projective
      (sigma.obj (M.1.1.hookArrow sigma AR).1.1) at hsecond
    simpa [HookM5Preliminary.hookArrow, M.1.2.1,
      StripAdmissibleTriple.secondArrow] using hsecond

/-- The residual endpoint occurrence still retains its outer `M5` term. -/
theorem injectiveSourceNoProjectivePair_injective :
    Function.Injective (injectiveSourceNoProjectivePair sigma AR) := by
  intro M N h
  apply Subtype.ext
  apply Subtype.ext
  apply HookM5Preliminary.commonTargetPair_injective sigma AR
  exact congrArg (fun p ↦ p.1.1) h

end HookM5Preliminary.InjectiveMiddleNoProjectiveFirst

namespace HookM5Preliminary.InjectiveMiddleProjectiveFirst

variable (M : HookM5Preliminary.InjectiveMiddleProjectiveFirst sigma AR)

/-- The projective-first part of outer `M5` lies in the shared
projective/injective-source outer intersection. -/
def outerIntersectionPair :
    NonprojectiveTargetProjectiveInjectiveSourcePair sigma := by
  refine ⟨⟨M.1.1.commonTargetPair sigma AR, ?_, Or.inl M.2⟩, ?_⟩
  · change ¬ Projective
      (sigma.obj (M.1.1.rotatedAssociatedArrow sigma AR).1.2)
    rw [M.1.1.rotatedAssociatedArrow_target_eq_hookArrow_target sigma AR]
    exact M.1.1.hookArrow_target_nonprojective sigma AR
  · right
    simpa [HookM5Preliminary.commonTargetPair,
      HookM5Preliminary.hookArrow, M.1.2.1,
      StripAdmissibleTriple.secondArrow] using M.1.2.2

/-- The projective-corner occurrence still retains its outer `M5` term. -/
theorem outerIntersectionPair_injective :
    Function.Injective (outerIntersectionPair sigma AR) := by
  intro M N h
  apply Subtype.ext
  apply Subtype.ext
  apply HookM5Preliminary.commonTargetPair_injective sigma AR
  exact congrArg (fun p ↦ p.1.1) h

end HookM5Preliminary.InjectiveMiddleProjectiveFirst

/-- Outer `M3` terms whose projective fourth source is noninjective.  The
outer endpoint predicate then forces the hook middle to be injective. -/
abbrev HookWallBadBUnrestricted.InjectiveEndpointFirstNoninjective :=
  {W : HookWallBadBUnrestricted.InjectiveEndpoint sigma AR //
    ¬ Injective (sigma.obj W.1.1.z)}

/-- Outer `M3` terms whose projective fourth source is injective. -/
abbrev HookWallBadBUnrestricted.InjectiveEndpointFirstInjective :=
  {W : HookWallBadBUnrestricted.InjectiveEndpoint sigma AR //
    Injective (sigma.obj W.1.1.z)}

noncomputable instance
    hookWallBadBUnrestrictedInjectiveEndpointFirstNoninjectiveFintype :
    Fintype
      (HookWallBadBUnrestricted.InjectiveEndpointFirstNoninjective
        sigma AR) :=
  Fintype.ofFinite _

noncomputable instance
    hookWallBadBUnrestrictedInjectiveEndpointFirstInjectiveFintype :
    Fintype
      (HookWallBadBUnrestricted.InjectiveEndpointFirstInjective sigma AR) :=
  Fintype.ofFinite _

/-- Exhaustive split of outer `M3` by injectivity of its projective fourth
source. -/
def hookWallBadBInjectiveEndpointEquivFirstInjectiveSumNoninjective :
    HookWallBadBUnrestricted.InjectiveEndpoint sigma AR ≃
      HookWallBadBUnrestricted.InjectiveEndpointFirstInjective sigma AR ⊕
        HookWallBadBUnrestricted.InjectiveEndpointFirstNoninjective sigma AR where
  toFun W := by
    classical
    by_cases h : Injective (sigma.obj W.1.1.z)
    · exact Sum.inl ⟨W, h⟩
    · exact Sum.inr ⟨W, h⟩
  invFun W := by
    rcases W with W | W
    · exact W.1
    · exact W.1
  left_inv W := by
    classical
    by_cases h : Injective (sigma.obj W.1.1.z)
    · simp [h]
    · simp [h]
  right_inv W := by
    classical
    rcases W with W | W
    · simp [W.2]
    · simp [W.2]

namespace HookWallBadBUnrestricted.InjectiveEndpointFirstInjective

variable (W : HookWallBadBUnrestricted.InjectiveEndpointFirstInjective
  sigma AR)

omit [DecidableEq iota] in
/-- The full common-target square shift fixes every injective-first outer
`M3` occurrence. -/
theorem commonTargetBoundaryEquiv_sourceBoundaryPair :
    (AR.commonTargetBoundaryEquiv sigma
      (W.1.1.sourceBoundaryPair sigma AR)).1 =
        W.1.1.commonTargetPair sigma AR := by
  simpa only [HookWallBadBUnrestricted.sourceBoundaryPair] using
    AR.commonTargetBoundaryEquiv_apply_of_firstSource_projective_injective
      sigma (W.1.1.commonTargetPair sigma AR)
        (by
          simpa [HookWallBadBUnrestricted.commonTargetPair,
            HookWallBadBUnrestricted.associatedArrow] using
              W.1.1.1.z_projective)
        (by
          simpa [HookWallBadBUnrestricted.commonTargetPair,
            HookWallBadBUnrestricted.associatedArrow] using W.2)

omit [DecidableEq iota] in
/-- Every injective-first outer `M3` labelled endpoint pair lies on two
different full arrow components. -/
theorem commonTargetPair_differentOrbit :
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit
      (W.1.1.commonTargetPair sigma AR).1.1
      (W.1.1.commonTargetPair sigma AR).1.2 := by
  apply AR.commonTargetPair_differentOrbit_of_firstSource_projective_injective
    sigma (W.1.1.commonTargetPair sigma AR)
  · simpa [HookWallBadBUnrestricted.commonTargetPair,
      HookWallBadBUnrestricted.associatedArrow] using
        W.1.1.1.triple.b_nonprojective
  · simpa [HookWallBadBUnrestricted.commonTargetPair,
      HookWallBadBUnrestricted.associatedArrow] using
        W.1.1.1.z_projective
  · simpa [HookWallBadBUnrestricted.commonTargetPair,
      HookWallBadBUnrestricted.associatedArrow] using W.2
  · intro hEq
    have hs := congrArg
      (fun q : sigma.IrreduciblePair ↦ q.1.1) hEq
    have hs' : W.1.1.1.z = W.1.1.1.triple.u := by
      simpa [HookWallBadBUnrestricted.commonTargetPair,
        HookWallBadBUnrestricted.associatedArrow,
        StripAdmissibleTriple.secondArrow] using hs
    apply W.1.1.1.triple.u_nonprojective
    rw [← hs']
    simpa [HookWallBadBUnrestricted.commonTargetPair,
      HookWallBadBUnrestricted.associatedArrow] using
        W.1.1.1.z_projective

/-- The injective-first outer `M3` occurrence as an element of the
intrinsic different-component projective/injective-source corner. -/
def differentOrbitOuterIntersectionPair :
    AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
      sigma :=
  ⟨W.1.outerIntersectionPair sigma AR,
    W.commonTargetPair_differentOrbit sigma AR⟩

omit [DecidableEq iota] in
/-- The different-component endpoint encoding still retains the
injective-first outer `M3` term. -/
theorem differentOrbitOuterIntersectionPair_injective :
    Function.Injective (differentOrbitOuterIntersectionPair sigma AR) := by
  intro W Z h
  apply Subtype.ext
  apply HookWallBadBUnrestricted.InjectiveEndpoint.outerIntersectionPair_injective
    sigma AR
  exact congrArg Subtype.val h

end HookWallBadBUnrestricted.InjectiveEndpointFirstInjective

/-- Outer `M6` terms whose hook-orbit anchor starts at a projective. -/
abbrev HookM6Channel.InjectiveFourthProjectiveAnchor :=
  {M : HookM6Channel.InjectiveFourthEndpoint sigma AR //
    Projective (sigma.obj
      (M.1.1.triple.hookOrbitAnchor sigma AR).1.1)}

/-- Outer `M6` terms whose hook-orbit anchor starts at a nonprojective. -/
abbrev HookM6Channel.InjectiveFourthNonprojectiveAnchor :=
  {M : HookM6Channel.InjectiveFourthEndpoint sigma AR //
    ¬ Projective (sigma.obj
      (M.1.1.triple.hookOrbitAnchor sigma AR).1.1)}

noncomputable instance hookM6InjectiveFourthProjectiveAnchorFintype :
    Fintype (HookM6Channel.InjectiveFourthProjectiveAnchor sigma AR) :=
  Fintype.ofFinite _

noncomputable instance hookM6InjectiveFourthNonprojectiveAnchorFintype :
    Fintype (HookM6Channel.InjectiveFourthNonprojectiveAnchor sigma AR) :=
  Fintype.ofFinite _

/-- Split outer `M6` by projectivity of its second occurrence source. -/
def hookM6InjectiveFourthEquivProjectiveSumNonprojectiveAnchor :
    HookM6Channel.InjectiveFourthEndpoint sigma AR ≃
      HookM6Channel.InjectiveFourthProjectiveAnchor sigma AR ⊕
        HookM6Channel.InjectiveFourthNonprojectiveAnchor sigma AR where
  toFun M := by
    classical
    by_cases h : Projective (sigma.obj
        (M.1.1.triple.hookOrbitAnchor sigma AR).1.1)
    · exact Sum.inl ⟨M, h⟩
    · exact Sum.inr ⟨M, h⟩
  invFun M := by
    rcases M with M | M
    · exact M.1
    · exact M.1
  left_inv M := by
    classical
    by_cases h : Projective (sigma.obj
        (M.1.1.triple.hookOrbitAnchor sigma AR).1.1)
    · simp [h]
    · simp [h]
  right_inv M := by
    classical
    rcases M with M | M
    · simp [M.2]
    · simp [M.2]

namespace HookM6Channel.InjectiveFourthProjectiveAnchor

variable (M : HookM6Channel.InjectiveFourthProjectiveAnchor sigma AR)

include K AR in
/-- A projective-anchor outer `M6` term determines the coincident outer
`M2` wall term by reconstructing the admissible strip from its anchor
arrow. -/
def toHookWallBadU : HookWallBadU.InjectiveFourthEndpoint sigma AR := by
  let H := M.1.1.1.triple.hookOrbitAnchor sigma AR
  have hH := M.1.1.hookOrbitAnchor_isInterior sigma AR
  let T := stripTripleOfProjectiveArrow (k := K) sigma AR H
    M.2 hH.2 hH.1
  have hfirst : T.firstArrow sigma AR = H :=
    stripTripleOfProjectiveArrow_firstArrow
      (k := K) sigma AR H M.2 hH.2 hH.1
  have hTu : T.u = H.1.2 :=
    congrArg (fun q : sigma.IrreduciblePair ↦ q.1.2) hfirst
  let W₀ : AR.HookWallChoice sigma :=
    { triple := T
      a_projective := M.2
      z := M.1.1.1.z
      z_projective := (M.1.1.z_projective_and_z_to_a sigma AR).1 }
  let W : AR.HookWallBadU sigma := ⟨W₀, by
    change HasIrreducibleMorphism
      (sigma.obj M.1.1.1.z) (sigma.obj T.u)
    rw [hTu, M.1.1.1.triple.hookOrbitAnchor_target sigma AR]
    exact (M.1.1.z_projective_and_z_to_a sigma AR).2⟩
  exact ⟨W, M.1.2⟩

include K AR in
/-- The reconstructed outer `M2` term has exactly the original outer
`M6` labelled common-target occurrence. -/
theorem toHookWallBadU_commonTargetPair :
    (M.toHookWallBadU (K := K) sigma AR).1.commonTargetPair sigma AR =
      M.1.1.commonTargetPair sigma AR := by
  let H := M.1.1.1.triple.hookOrbitAnchor sigma AR
  have hH := M.1.1.hookOrbitAnchor_isInterior sigma AR
  let T := stripTripleOfProjectiveArrow (k := K) sigma AR H
    M.2 hH.2 hH.1
  have hfirst : T.firstArrow sigma AR = H :=
    stripTripleOfProjectiveArrow_firstArrow
      (k := K) sigma AR H M.2 hH.2 hH.1
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · calc
        T.u = H.1.2 := by
          exact congrArg (fun q : sigma.IrreduciblePair ↦ q.1.2) hfirst
        _ = M.1.1.1.triple.a :=
          M.1.1.1.triple.hookOrbitAnchor_target sigma AR
  · exact hfirst

include K AR in
/-- The projective-anchor `M6`-to-`M2` map is injective because it
preserves the already injective labelled occurrence assignment. -/
theorem toHookWallBadU_injective :
    Function.Injective (toHookWallBadU (K := K) sigma AR) := by
  intro M N h
  apply Subtype.ext
  apply Subtype.ext
  apply HookM6Channel.commonTargetPair_injective sigma AR
  rw [← M.toHookWallBadU_commonTargetPair (K := K) sigma AR,
    ← N.toHookWallBadU_commonTargetPair (K := K) sigma AR,
    congrArg Subtype.val h]

end HookM6Channel.InjectiveFourthProjectiveAnchor

/-- The exact image of the projective-anchor outer `M6` branch inside
outer `M2`. -/
abbrev HookWallBadU.M6ProjectiveAnchorImage :=
  Set.range
    (HookM6Channel.InjectiveFourthProjectiveAnchor.toHookWallBadU
      (K := K) sigma AR)

noncomputable instance hookWallBadUM6ProjectiveAnchorImageFintype :
    Fintype (HookWallBadU.M6ProjectiveAnchorImage (K := K) sigma AR) :=
  Fintype.ofFinite _

include K AR in
/-- Projective-anchor outer `M6` is exactly equivalent to its
occurrence-preserving image in outer `M2`. -/
def hookM6ProjectiveAnchorEquivHookWallBadUImage :
    HookM6Channel.InjectiveFourthProjectiveAnchor sigma AR ≃
      HookWallBadU.M6ProjectiveAnchorImage (K := K) sigma AR :=
  Equiv.ofInjective
    (HookM6Channel.InjectiveFourthProjectiveAnchor.toHookWallBadU
      (K := K) sigma AR)
    (HookM6Channel.InjectiveFourthProjectiveAnchor.toHookWallBadU_injective
      (K := K) sigma AR)

/-- If an outer `M6` occurrence coincides with an outer `M2` occurrence,
then the `M6` anchor source is projective. -/
theorem hookM6_anchor_projective_of_pair_eq_hookWallBadU
    (M : HookM6Channel.InjectiveFourthEndpoint sigma AR)
    (W : HookWallBadU.InjectiveFourthEndpoint sigma AR)
    (h : M.1.commonTargetPair sigma AR =
      W.1.commonTargetPair sigma AR) :
    Projective (sigma.obj
      (M.1.1.triple.hookOrbitAnchor sigma AR).1.1) := by
  have hs := congrArg
    (fun p : CommonTargetArrowPair sigma ↦ p.1.2.1.1) h
  change (M.1.1.triple.hookOrbitAnchor sigma AR).1.1 =
    W.1.1.triple.a at hs
  rw [hs]
  exact W.1.1.a_projective

/-- A projective-anchor outer `M6` occurrence cannot coincide with an
outer `M3` occurrence, whose second arrow starts at a nonprojective. -/
theorem hookM6ProjectiveAnchor_pair_ne_hookWallBadB_outer_pair
    (M : HookM6Channel.InjectiveFourthProjectiveAnchor sigma AR)
    (W : HookWallBadBUnrestricted.InjectiveEndpoint sigma AR) :
    M.1.1.commonTargetPair sigma AR ≠ W.1.commonTargetPair sigma AR := by
  intro h
  have hs := congrArg
    (fun p : CommonTargetArrowPair sigma ↦ p.1.2.1.1) h
  change (M.1.1.1.triple.hookOrbitAnchor sigma AR).1.1 =
    W.1.1.triple.u at hs
  apply W.1.1.triple.u_nonprojective
  rw [← hs]
  exact M.2

/-- A nonprojective-anchor outer `M6` occurrence cannot coincide with an
outer `M2` occurrence, whose second arrow starts at a projective. -/
theorem hookM6NonprojectiveAnchor_pair_ne_hookWallBadU_outer_pair
    (M : HookM6Channel.InjectiveFourthNonprojectiveAnchor sigma AR)
    (W : HookWallBadU.InjectiveFourthEndpoint sigma AR) :
    M.1.1.commonTargetPair sigma AR ≠ W.1.commonTargetPair sigma AR := by
  intro h
  have hs := congrArg
    (fun p : CommonTargetArrowPair sigma ↦ p.1.2.1.1) h
  change (M.1.1.1.triple.hookOrbitAnchor sigma AR).1.1 =
    W.1.1.triple.a at hs
  apply M.2
  rw [hs]
  exact W.1.1.a_projective

/-- Nonprojective-anchor outer `M6` terms whose anchor is nevertheless in
the first two layers of the trimmed arrow chain. -/
abbrev HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary :=
  {M : HookM6Channel.InjectiveFourthNonprojectiveAnchor sigma AR //
    ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      (toInteriorArrow sigma AR
        (M.1.1.1.triple.hookOrbitAnchor sigma AR)
        (M.1.1.hookOrbitAnchor_isInterior sigma AR))}

/-- Nonprojective-anchor outer `M6` terms whose anchor lies beyond the
first two trimmed source layers. -/
abbrev HookM6Channel.InjectiveFourthDeepAnchor :=
  {M : HookM6Channel.InjectiveFourthNonprojectiveAnchor sigma AR //
    ¬ ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      (toInteriorArrow sigma AR
        (M.1.1.1.triple.hookOrbitAnchor sigma AR)
        (M.1.1.hookOrbitAnchor_isInterior sigma AR))}

noncomputable instance
    hookM6InjectiveFourthNonprojectiveAnchorSecondBoundaryFintype :
    Fintype
      (HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary
        sigma AR) :=
  Fintype.ofFinite _

noncomputable instance hookM6InjectiveFourthDeepAnchorFintype :
    Fintype (HookM6Channel.InjectiveFourthDeepAnchor sigma AR) :=
  Fintype.ofFinite _

/-- Split the nonprojective-anchor `M6` branch according to whether its
anchor is still on the shifted source boundary. -/
def hookM6NonprojectiveAnchorEquivSecondBoundarySumDeep :
    HookM6Channel.InjectiveFourthNonprojectiveAnchor sigma AR ≃
      HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary sigma AR ⊕
        HookM6Channel.InjectiveFourthDeepAnchor sigma AR where
  toFun M := by
    classical
    by_cases h :
        ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
          (toInteriorArrow sigma AR
            (M.1.1.1.triple.hookOrbitAnchor sigma AR)
            (M.1.1.hookOrbitAnchor_isInterior sigma AR))
    · exact Sum.inl ⟨M, h⟩
    · exact Sum.inr ⟨M, h⟩
  invFun M := by
    rcases M with M | M
    · exact M.1
    · exact M.1
  left_inv M := by
    classical
    by_cases h :
        ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
          (toInteriorArrow sigma AR
            (M.1.1.1.triple.hookOrbitAnchor sigma AR)
            (M.1.1.hookOrbitAnchor_isInterior sigma AR))
    · simp [h]
    · simp [h]
  right_inv M := by
    classical
    rcases M with M | M
    · simp [M.2]
    · simp [M.2]

namespace HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary

variable
  (M : HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary
    sigma AR)

include K AR in
/-- Reconstruct the coincident injective-first outer `M3` term from a
nonprojective `M6` anchor in the second trimmed source boundary. -/
def toHookWallBadB :
    HookWallBadBUnrestricted.InjectiveEndpointFirstInjective sigma AR := by
  let Hraw := M.1.1.1.1.triple.hookOrbitAnchor sigma AR
  let H := toInteriorArrow sigma AR Hraw
    (M.1.1.1.hookOrbitAnchor_isInterior sigma AR)
  let S := AR.sourceBoundaryHook (k := K) sigma H M.2
  have hsecond : Hraw = S.triple.secondArrow sigma AR := by
    rcases S.hookArrow_eq with hfirst | hsecond
    · exfalso
      apply M.1.2
      change Projective (sigma.obj Hraw.1.1)
      change Hraw = S.triple.firstArrow sigma AR at hfirst
      rw [congrArg (fun q : sigma.IrreduciblePair ↦ q.1.1) hfirst]
      exact S.a_projective
    · exact hsecond
  have htarget : Hraw.1.2 = S.triple.b := by
    rw [hsecond]
    rfl
  let W₀ : AR.HookWallChoice sigma :=
    { triple := S.triple
      a_projective := S.a_projective
      z := M.1.1.1.1.z
      z_projective :=
        (M.1.1.1.z_projective_and_z_to_a sigma AR).1 }
  let W : AR.HookWallBadBUnrestricted sigma := ⟨W₀, by
    change HasIrreducibleMorphism
      (sigma.obj M.1.1.1.1.z) (sigma.obj S.triple.b)
    rw [← htarget,
      M.1.1.1.1.triple.hookOrbitAnchor_target sigma AR]
    exact (M.1.1.1.z_projective_and_z_to_a sigma AR).2⟩
  refine ⟨⟨W, Or.inl M.1.1.2⟩, ?_⟩
  exact M.1.1.2

include K AR in
/-- The reconstructed injective-first outer `M3` term has exactly the
original outer `M6` labelled common-target occurrence. -/
theorem toHookWallBadB_commonTargetPair :
    (M.toHookWallBadB (K := K) sigma AR).1.1.commonTargetPair sigma AR =
      M.1.1.1.commonTargetPair sigma AR := by
  let Hraw := M.1.1.1.1.triple.hookOrbitAnchor sigma AR
  let H := toInteriorArrow sigma AR Hraw
    (M.1.1.1.hookOrbitAnchor_isInterior sigma AR)
  let S := AR.sourceBoundaryHook (k := K) sigma H M.2
  have hsecond : Hraw = S.triple.secondArrow sigma AR := by
    rcases S.hookArrow_eq with hfirst | hsecond
    · exfalso
      apply M.1.2
      change Projective (sigma.obj Hraw.1.1)
      change Hraw = S.triple.firstArrow sigma AR at hfirst
      rw [congrArg (fun q : sigma.IrreduciblePair ↦ q.1.1) hfirst]
      exact S.a_projective
    · exact hsecond
  have htarget : Hraw.1.2 = S.triple.b := by
    rw [hsecond]
    rfl
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact htarget.symm.trans
        (M.1.1.1.1.triple.hookOrbitAnchor_target sigma AR)
  · exact hsecond.symm

include K AR in
/-- The second-boundary `M6`-to-`M3` map is injective because it preserves
the labelled occurrence assignment. -/
theorem toHookWallBadB_injective :
    Function.Injective (toHookWallBadB (K := K) sigma AR) := by
  intro M N h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply HookM6Channel.commonTargetPair_injective sigma AR
  rw [← M.toHookWallBadB_commonTargetPair (K := K) sigma AR,
    ← N.toHookWallBadB_commonTargetPair (K := K) sigma AR,
    congrArg (fun W ↦ W.1.1) h]

end HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary

/-- If an outer `M6` occurrence coincides with an outer `M3` occurrence,
then the `M6` anchor source is nonprojective. -/
theorem hookM6_anchor_nonprojective_of_pair_eq_hookWallBadB
    (M : HookM6Channel.InjectiveFourthEndpoint sigma AR)
    (W : HookWallBadBUnrestricted.InjectiveEndpoint sigma AR)
    (h : M.1.commonTargetPair sigma AR =
      W.1.commonTargetPair sigma AR) :
    ¬ Projective (sigma.obj
      (M.1.1.triple.hookOrbitAnchor sigma AR).1.1) := by
  have hs := congrArg
    (fun p : CommonTargetArrowPair sigma ↦ p.1.2.1.1) h
  change (M.1.1.triple.hookOrbitAnchor sigma AR).1.1 =
    W.1.1.triple.u at hs
  intro hP
  apply W.1.1.triple.u_nonprojective
  rw [← hs]
  exact hP

/-- Coincidence with an outer `M6` forces the projective fourth source of
the outer `M3` occurrence to be injective. -/
theorem hookWallBadB_first_injective_of_pair_eq_hookM6
    (M : HookM6Channel.InjectiveFourthEndpoint sigma AR)
    (W : HookWallBadBUnrestricted.InjectiveEndpoint sigma AR)
    (h : M.1.commonTargetPair sigma AR =
      W.1.commonTargetPair sigma AR) :
    Injective (sigma.obj W.1.1.z) := by
  have hs := congrArg
    (fun p : CommonTargetArrowPair sigma ↦ p.1.1.1.1) h
  change M.1.1.z = W.1.1.z at hs
  rw [← hs]
  exact M.2

/-- Coincidence with outer `M3` also forces the nonprojective `M6` anchor
onto the second trimmed source boundary. -/
theorem hookM6_anchor_twoSource_of_pair_eq_hookWallBadB
    (M : HookM6Channel.InjectiveFourthEndpoint sigma AR)
    (W : HookWallBadBUnrestricted.InjectiveEndpoint sigma AR)
    (h : M.1.commonTargetPair sigma AR =
      W.1.commonTargetPair sigma AR) :
    ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      (toInteriorArrow sigma AR
        (M.1.1.triple.hookOrbitAnchor sigma AR)
        (M.1.hookOrbitAnchor_isInterior sigma AR)) := by
  have harrow := congrArg
    (fun p : CommonTargetArrowPair sigma ↦ p.1.2) h
  change M.1.1.triple.hookOrbitAnchor sigma AR =
    W.1.1.triple.secondArrow sigma AR at harrow
  have huNI : ¬ Injective (sigma.obj W.1.1.triple.u) := by
    have hs := congrArg
      (fun q : sigma.IrreduciblePair ↦ q.1.1) harrow
    change (M.1.1.triple.hookOrbitAnchor sigma AR).1.1 =
      W.1.1.triple.u at hs
    rw [← hs]
    exact (M.1.hookOrbitAnchor_isInterior sigma AR).2
  have htwo := W.1.1.triple.secondArrow_interior_twoSource
    sigma AR W.1.1.a_projective huNI
  convert htwo using 1
  apply Subtype.ext
  exact harrow

/-- Thus every actual outer `M6`/`M3` overlap belongs to the
second-boundary branch on the `M6` side. -/
def hookM6SecondBoundaryOfPairEqHookWallBadB
    (M : HookM6Channel.InjectiveFourthEndpoint sigma AR)
    (W : HookWallBadBUnrestricted.InjectiveEndpoint sigma AR)
    (h : M.1.commonTargetPair sigma AR =
      W.1.commonTargetPair sigma AR) :
    HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary
      sigma AR :=
  ⟨⟨M, hookM6_anchor_nonprojective_of_pair_eq_hookWallBadB
      sigma AR M W h⟩,
    hookM6_anchor_twoSource_of_pair_eq_hookWallBadB sigma AR M W h⟩

/-- The exact occurrence-preserving image of second-boundary outer `M6`
inside injective-first outer `M3`. -/
abbrev HookWallBadBUnrestricted.M6SecondBoundaryImage :=
  Set.range
    (HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary.toHookWallBadB
      (K := K) sigma AR)

noncomputable instance hookWallBadBM6SecondBoundaryImageFintype :
    Fintype
      (HookWallBadBUnrestricted.M6SecondBoundaryImage
        (K := K) sigma AR) :=
  Fintype.ofFinite _

include K AR in
/-- Second-boundary outer `M6` is exactly equivalent to its labelled
occurrence image in injective-first outer `M3`. -/
def hookM6SecondBoundaryEquivHookWallBadBImage :
    HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary sigma AR ≃
      HookWallBadBUnrestricted.M6SecondBoundaryImage
        (K := K) sigma AR :=
  Equiv.ofInjective
    (HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary.toHookWallBadB
      (K := K) sigma AR)
    (HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary.toHookWallBadB_injective
      (K := K) sigma AR)

/-- Conversely, every outer `M3` occurrence coinciding with outer `M6`
lies in the preceding exact image. -/
theorem hookWallBadB_mem_M6SecondBoundaryImage_of_pair_eq_hookM6
    (M : HookM6Channel.InjectiveFourthEndpoint sigma AR)
    (W : HookWallBadBUnrestricted.InjectiveEndpoint sigma AR)
    (h : M.1.commonTargetPair sigma AR =
      W.1.commonTargetPair sigma AR) :
    let WI : HookWallBadBUnrestricted.InjectiveEndpointFirstInjective
        sigma AR :=
      ⟨W, hookWallBadB_first_injective_of_pair_eq_hookM6 sigma AR M W h⟩
    WI ∈ HookWallBadBUnrestricted.M6SecondBoundaryImage
      (K := K) sigma AR := by
  dsimp only
  let M₂ := hookM6SecondBoundaryOfPairEqHookWallBadB sigma AR M W h
  refine ⟨M₂, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply HookWallBadBUnrestricted.commonTargetPair_injective sigma AR
  rw [HookM6Channel.InjectiveFourthNonprojectiveAnchorSecondBoundary.toHookWallBadB_commonTargetPair]
  exact h

/-- Outer `M2` occurrences not used by the projective-anchor `M6`
overlap. -/
abbrev HookWallBadU.M6ProjectiveAnchorComplement :=
  {W : HookWallBadU.InjectiveFourthEndpoint sigma AR //
    W ∉ HookWallBadU.M6ProjectiveAnchorImage (K := K) sigma AR}

/-- Injective-first outer `M3` occurrences not used by the
second-boundary `M6` overlap. -/
abbrev HookWallBadBUnrestricted.M6SecondBoundaryComplement :=
  {W : HookWallBadBUnrestricted.InjectiveEndpointFirstInjective sigma AR //
    W ∉ HookWallBadBUnrestricted.M6SecondBoundaryImage
      (K := K) sigma AR}

noncomputable instance hookWallBadUM6ProjectiveAnchorComplementFintype :
    Fintype
      (HookWallBadU.M6ProjectiveAnchorComplement (K := K) sigma AR) :=
  Fintype.ofFinite _

noncomputable instance hookWallBadBM6SecondBoundaryComplementFintype :
    Fintype
      (HookWallBadBUnrestricted.M6SecondBoundaryComplement
        (K := K) sigma AR) :=
  Fintype.ofFinite _

namespace HookM6Channel.InjectiveFourthDeepAnchor

variable (M : HookM6Channel.InjectiveFourthDeepAnchor sigma AR)

/-- A surviving deep-anchor outer `M6` term, viewed in the intrinsic
different-component projective/injective-source corner. -/
def differentOrbitOuterIntersectionPair :
    AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
      sigma :=
  M.1.1.differentOrbitOuterIntersectionPair sigma AR

/-- The intrinsic endpoint occurrence retains the deep-anchor `M6` term. -/
theorem differentOrbitOuterIntersectionPair_injective :
    Function.Injective (differentOrbitOuterIntersectionPair sigma AR) := by
  intro M N h
  apply Subtype.ext
  apply Subtype.ext
  exact HookM6Channel.InjectiveFourthEndpoint.differentOrbitOuterIntersectionPair_injective
    sigma AR h

end HookM6Channel.InjectiveFourthDeepAnchor

namespace HookWallBadU.M6ProjectiveAnchorComplement

variable
  (W : HookWallBadU.M6ProjectiveAnchorComplement (K := K) sigma AR)

/-- A surviving outer `M2` complement, viewed in the intrinsic
different-component projective/injective-source corner. -/
def differentOrbitOuterIntersectionPair :
    AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
      sigma :=
  W.1.differentOrbitOuterIntersectionPair sigma AR

/-- The intrinsic endpoint occurrence retains the outer `M2` complement. -/
theorem differentOrbitOuterIntersectionPair_injective :
    Function.Injective (differentOrbitOuterIntersectionPair
      (K := K) sigma AR) := by
  intro W Z h
  apply Subtype.ext
  exact HookWallBadU.InjectiveFourthEndpoint.differentOrbitOuterIntersectionPair_injective
    sigma AR h

end HookWallBadU.M6ProjectiveAnchorComplement

namespace HookWallBadBUnrestricted.M6SecondBoundaryComplement

variable
  (W : HookWallBadBUnrestricted.M6SecondBoundaryComplement
    (K := K) sigma AR)

/-- A surviving injective-first outer `M3` complement, viewed in the
intrinsic different-component projective/injective-source corner. -/
def differentOrbitOuterIntersectionPair :
    AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
      sigma :=
  W.1.differentOrbitOuterIntersectionPair sigma AR

/-- The intrinsic endpoint occurrence retains the outer `M3` complement. -/
theorem differentOrbitOuterIntersectionPair_injective :
    Function.Injective (differentOrbitOuterIntersectionPair
      (K := K) sigma AR) := by
  intro W Z h
  apply Subtype.ext
  exact HookWallBadBUnrestricted.InjectiveEndpointFirstInjective.differentOrbitOuterIntersectionPair_injective
    sigma AR h

end HookWallBadBUnrestricted.M6SecondBoundaryComplement

/-- Deep-anchor outer `M6` and the surviving outer `M2` complement have
disjoint intrinsic endpoint occurrences. -/
theorem hookM6DeepAnchor_pair_ne_hookWallBadUComplement_pair
    (M : HookM6Channel.InjectiveFourthDeepAnchor sigma AR)
    (W : HookWallBadU.M6ProjectiveAnchorComplement (K := K) sigma AR) :
    M.differentOrbitOuterIntersectionPair sigma AR ≠
      W.differentOrbitOuterIntersectionPair sigma AR := by
  intro h
  apply hookM6NonprojectiveAnchor_pair_ne_hookWallBadU_outer_pair
    sigma AR M.1 W.1
  exact congrArg
    (fun p : AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
      sigma ↦ p.1.1.1) h

/-- Deep-anchor outer `M6` and the surviving injective-first outer `M3`
complement have disjoint intrinsic endpoint occurrences. -/
theorem hookM6DeepAnchor_pair_ne_hookWallBadBComplement_pair
    (M : HookM6Channel.InjectiveFourthDeepAnchor sigma AR)
    (W : HookWallBadBUnrestricted.M6SecondBoundaryComplement
      (K := K) sigma AR) :
    M.differentOrbitOuterIntersectionPair sigma AR ≠
      W.differentOrbitOuterIntersectionPair sigma AR := by
  intro h
  have hpair : M.1.1.1.commonTargetPair sigma AR =
      W.1.1.1.commonTargetPair sigma AR :=
    congrArg
      (fun p : AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
        sigma ↦ p.1.1.1) h
  exact M.2 <|
    hookM6_anchor_twoSource_of_pair_eq_hookWallBadB
      sigma AR M.1.1 W.1.1 hpair

/-- The surviving outer `M2` and injective-first outer `M3` complements
have disjoint intrinsic endpoint occurrences. -/
theorem hookWallBadUComplement_pair_ne_hookWallBadBComplement_pair
    (W : HookWallBadU.M6ProjectiveAnchorComplement (K := K) sigma AR)
    (Z : HookWallBadBUnrestricted.M6SecondBoundaryComplement
      (K := K) sigma AR) :
    W.differentOrbitOuterIntersectionPair sigma AR ≠
      Z.differentOrbitOuterIntersectionPair sigma AR := by
  intro h
  have hpair := congrArg
    (fun p : AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
      sigma ↦ p.1.1.1) h
  have hs := congrArg
    (fun p : CommonTargetArrowPair sigma ↦ p.1.2.1.1) hpair
  change W.1.1.1.triple.a = Z.1.1.1.1.triple.u at hs
  apply Z.1.1.1.1.triple.u_nonprojective
  rw [← hs]
  exact W.1.1.1.a_projective

/-- The three outer endpoint families left after the two exact `M6`
overlap cancellations. -/
abbrev SurvivingOuterEndpointFamily :=
  HookM6Channel.InjectiveFourthDeepAnchor sigma AR ⊕
    (HookWallBadU.M6ProjectiveAnchorComplement (K := K) sigma AR ⊕
      HookWallBadBUnrestricted.M6SecondBoundaryComplement
        (K := K) sigma AR)

/-- Forget the channel name while retaining the ordered labelled occurrence
in the intrinsic different-component outer corner. -/
def survivingOuterEndpointPair :
    SurvivingOuterEndpointFamily (K := K) sigma AR →
      AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
        sigma
  | Sum.inl M => M.differentOrbitOuterIntersectionPair sigma AR
  | Sum.inr (Sum.inl W) =>
      W.differentOrbitOuterIntersectionPair sigma AR
  | Sum.inr (Sum.inr W) =>
      W.differentOrbitOuterIntersectionPair sigma AR

/-- The combined surviving outer endpoint encoding is injective: it is
injective within each channel and the three channel images are pairwise
disjoint. -/
theorem survivingOuterEndpointPair_injective :
    Function.Injective (survivingOuterEndpointPair (K := K) sigma AR) := by
  intro X Y h
  rcases X with M | X
  · rcases Y with N | Y
    · rw [HookM6Channel.InjectiveFourthDeepAnchor.differentOrbitOuterIntersectionPair_injective
        sigma AR h]
    · rcases Y with W | W
      · exact (hookM6DeepAnchor_pair_ne_hookWallBadUComplement_pair
          (K := K) sigma AR M W h).elim
      · exact (hookM6DeepAnchor_pair_ne_hookWallBadBComplement_pair
          (K := K) sigma AR M W h).elim
  · rcases X with W | W
    · rcases Y with N | Y
      · exact (hookM6DeepAnchor_pair_ne_hookWallBadUComplement_pair
          (K := K) sigma AR N W h.symm).elim
      · rcases Y with Z | Z
        · rw [HookWallBadU.M6ProjectiveAnchorComplement.differentOrbitOuterIntersectionPair_injective
            (K := K) sigma AR h]
        · exact (hookWallBadUComplement_pair_ne_hookWallBadBComplement_pair
            (K := K) sigma AR W Z h).elim
    · rcases Y with N | Y
      · exact (hookM6DeepAnchor_pair_ne_hookWallBadBComplement_pair
          (K := K) sigma AR N W h.symm).elim
      · rcases Y with Z | Z
        · exact (hookWallBadUComplement_pair_ne_hookWallBadBComplement_pair
            (K := K) sigma AR Z W h.symm).elim
        · rw [HookWallBadBUnrestricted.M6SecondBoundaryComplement.differentOrbitOuterIntersectionPair_injective
            (K := K) sigma AR h]

/-- Exact image of the three surviving outer channel families inside the
intrinsic different-component corner. -/
abbrev SurvivingOuterEndpointImage :=
  Set.range (survivingOuterEndpointPair (K := K) sigma AR)

noncomputable instance survivingOuterEndpointImageFintype :
    Fintype (SurvivingOuterEndpointImage (K := K) sigma AR) :=
  Fintype.ofFinite _

/-- The disjoint sum of surviving outer channels is equivalent to its exact
labelled occurrence image. -/
def survivingOuterEndpointEquivImage :
    SurvivingOuterEndpointFamily (K := K) sigma AR ≃
      SurvivingOuterEndpointImage (K := K) sigma AR :=
  Equiv.ofInjective
    (survivingOuterEndpointPair (K := K) sigma AR)
    (survivingOuterEndpointPair_injective (K := K) sigma AR)

/-- Cardinality of the exact surviving outer occurrence image. -/
theorem survivingOuterEndpointImage_card_eq :
    Fintype.card (SurvivingOuterEndpointImage (K := K) sigma AR) =
      Fintype.card (HookM6Channel.InjectiveFourthDeepAnchor sigma AR) +
        Fintype.card
          (HookWallBadU.M6ProjectiveAnchorComplement (K := K) sigma AR) +
        Fintype.card
          (HookWallBadBUnrestricted.M6SecondBoundaryComplement
            (K := K) sigma AR) := by
  rw [← Fintype.card_congr
    (survivingOuterEndpointEquivImage (K := K) sigma AR)]
  simp only [SurvivingOuterEndpointFamily, Fintype.card_sum]
  omega

include K AR in
/-- Cancel both occurrence-preserving `M6` overlaps.  What remains of
`M6 - M2 - M3` is precisely deep-anchor `M6` minus the unused `M2` and
injective-first `M3` occurrence complements. -/
theorem hookM6_add_outer_overlap_complements_card_eq :
    Fintype.card (HookM6Channel.InjectiveFourthEndpoint sigma AR) +
        Fintype.card
          (HookWallBadU.M6ProjectiveAnchorComplement
            (K := K) sigma AR) +
      Fintype.card
          (HookWallBadBUnrestricted.M6SecondBoundaryComplement
            (K := K) sigma AR) =
    Fintype.card (HookM6Channel.InjectiveFourthDeepAnchor sigma AR) +
        Fintype.card (HookWallBadU.InjectiveFourthEndpoint sigma AR) +
      Fintype.card
          (HookWallBadBUnrestricted.InjectiveEndpointFirstInjective
            sigma AR) := by
  classical
  have hM6 := Fintype.card_congr
    (hookM6InjectiveFourthEquivProjectiveSumNonprojectiveAnchor sigma AR)
  have hnonprojective := Fintype.card_congr
    (hookM6NonprojectiveAnchorEquivSecondBoundarySumDeep sigma AR)
  have hprojective := Fintype.card_congr
    (hookM6ProjectiveAnchorEquivHookWallBadUImage (K := K) sigma AR)
  have hsecond := Fintype.card_congr
    (hookM6SecondBoundaryEquivHookWallBadBImage (K := K) sigma AR)
  have hM2 := Fintype.card_congr
    (Equiv.sumCompl (fun W : HookWallBadU.InjectiveFourthEndpoint sigma AR ↦
      W ∈ HookWallBadU.M6ProjectiveAnchorImage (K := K) sigma AR))
  have hM3 := Fintype.card_congr
    (Equiv.sumCompl
      (fun W :
          HookWallBadBUnrestricted.InjectiveEndpointFirstInjective sigma AR ↦
        W ∈ HookWallBadBUnrestricted.M6SecondBoundaryImage
          (K := K) sigma AR))
  simp only [Fintype.card_sum] at hM6 hnonprojective hM2 hM3
  change
    Fintype.card
          (HookWallBadU.M6ProjectiveAnchorImage (K := K) sigma AR) +
        Fintype.card
          (HookWallBadU.M6ProjectiveAnchorComplement
            (K := K) sigma AR) =
      Fintype.card (HookWallBadU.InjectiveFourthEndpoint sigma AR) at hM2
  change
    Fintype.card
          (HookWallBadBUnrestricted.M6SecondBoundaryImage
            (K := K) sigma AR) +
        Fintype.card
          (HookWallBadBUnrestricted.M6SecondBoundaryComplement
            (K := K) sigma AR) =
      Fintype.card
        (HookWallBadBUnrestricted.InjectiveEndpointFirstInjective
          sigma AR) at hM3
  omega

namespace HookM5Preliminary.InjectiveMiddleProjectiveFirst

variable (M : HookM5Preliminary.InjectiveMiddleProjectiveFirst sigma AR)

/-- Read a projective-first outer `M5` occurrence as the coincident outer
`M3` wall occurrence. -/
def toHookWallBadB :
    HookWallBadBUnrestricted.InjectiveEndpointFirstNoninjective sigma AR := by
  let T := M.1.1.triple
  let C := M.1.1.rotatedAssociatedArrow sigma AR
  have hhook : M.1.1.hookArrow sigma AR = T.secondArrow sigma AR := by
    simp [HookM5Preliminary.hookArrow, M.1.2.1, T]
  have htarget : C.1.2 = T.b := by
    calc
      C.1.2 = (M.1.1.hookArrow sigma AR).1.2 :=
        M.1.1.rotatedAssociatedArrow_target_eq_hookArrow_target sigma AR
      _ = T.b := by rw [hhook]; rfl
  let W₀ : AR.HookWallChoice sigma :=
    { triple := T
      a_projective := M.1.1.a_projective
      z := C.1.1
      z_projective := M.2 }
  let W : AR.HookWallBadBUnrestricted sigma := ⟨W₀, by
    change HasIrreducibleMorphism (sigma.obj C.1.1) (sigma.obj T.b)
    rw [← htarget]
    exact C.2⟩
  refine ⟨⟨W, Or.inr ?_⟩, ?_⟩
  · simpa [W, W₀, T] using M.1.2.2
  · simpa [W, W₀, C] using
      (M.1.1.rotatedAssociatedArrow_isInterior sigma AR).2

/-- The `M3` occurrence just constructed is literally the original outer
`M5` common-target pair. -/
theorem toHookWallBadB_commonTargetPair :
    (M.toHookWallBadB sigma AR).1.1.commonTargetPair sigma AR =
      M.1.1.commonTargetPair sigma AR := by
  let T := M.1.1.triple
  let C := M.1.1.rotatedAssociatedArrow sigma AR
  have hhook : M.1.1.hookArrow sigma AR = T.secondArrow sigma AR := by
    simp [HookM5Preliminary.hookArrow, M.1.2.1, T]
  have htarget : C.1.2 = T.b := by
    calc
      C.1.2 = (M.1.1.hookArrow sigma AR).1.2 :=
        M.1.1.rotatedAssociatedArrow_target_eq_hookArrow_target sigma AR
      _ = T.b := by rw [hhook]; rfl
  have hfirst :
      (M.toHookWallBadB sigma AR).1.1.associatedArrow sigma AR = C := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact htarget.symm
  have hsecond :
      (M.toHookWallBadB sigma AR).1.1.1.triple.secondArrow sigma AR =
        M.1.1.hookArrow sigma AR := by
    exact hhook.symm
  apply Subtype.ext
  apply Prod.ext
  · exact hfirst
  · exact hsecond

end HookM5Preliminary.InjectiveMiddleProjectiveFirst

namespace HookWallBadBUnrestricted.InjectiveEndpointFirstNoninjective

variable (W : HookWallBadBUnrestricted.InjectiveEndpointFirstNoninjective
  sigma AR)

structure HookM5PreliminaryReconstruction where
  term : HookM5Preliminary.InjectiveMiddleProjectiveFirst sigma AR
  occurrence_eq :
    term.1.1.commonTargetPair sigma AR =
      W.1.1.commonTargetPair sigma AR

include K AR in
/-- Apply one inverse mesh rotation to an outer `M3` wall arrow with
noninjective source, recovering the coincident projective-first outer
preliminary `M5` term. -/
def hookM5PreliminaryReconstruction :
    W.HookM5PreliminaryReconstruction sigma AR := by
  classical
  let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
  let T := W.1.1.1.triple
  let C := W.1.1.associatedArrow sigma AR
  let qsub := O.tau.symm ⟨C, W.2⟩
  let q : sigma.IrreduciblePair := qsub.1
  have hqSource : q.1.1 = T.b := by
    have hval := (AR.arMeshRotationData sigma).arrowOrbitData_tau_symm_val
      sigma ⟨C, W.2⟩
    exact congrArg Prod.fst hval
  have hbq : HasIrreducibleMorphism
      (sigma.obj T.b) (sigma.obj q.1.2) := by
    simpa only [hqSource] using q.2
  have huNot : ¬ HasIrreducibleMorphism
      (sigma.obj T.u) (sigma.obj q.1.2) :=
    AR.no_irreducible_transitiveTriangle (K := K) sigma T.u_to_b hbq
  have hzNot : q.1.2 ∉ T.support := by
    simp only [StripAdmissibleTriple.support, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩
    · intro h
      exact qsub.2 (h ▸ W.1.1.1.a_projective)
    · intro h
      apply T.b_not_to_u
      simpa only [h] using hbq
    · intro h
      exact sigma.hasNoIrreducibleEndomorphism_obj T.b (by
        simpa only [h] using hbq)
  let P : AR.HookM5Preliminary sigma :=
    { triple := T
      a_projective := W.1.1.1.a_projective
      z := q.1.2
      z_not_mem := hzNot
      z_nonprojective := qsub.2
      outgoing_to_z := Or.inr hbq }
  have hassociated : P.associatedArrow sigma AR = q := by
    apply Subtype.ext
    apply Prod.ext
    · simpa [HookM5Preliminary.associatedArrow, P, huNot] using
        hqSource.symm
    · exact P.associatedArrow_target sigma AR
  have hrotated : P.rotatedAssociatedArrow sigma AR = C := by
    change (O.tau ⟨P.associatedArrow sigma AR, ?_⟩).1 = C
    have harg : (⟨P.associatedArrow sigma AR, by
        simpa only [P.associatedArrow_target sigma AR] using
          P.z_nonprojective⟩ : {r : sigma.IrreduciblePair //
            ¬ Projective (sigma.obj r.1.2)}) = qsub := by
      apply Subtype.ext
      exact hassociated
    rw [harg]
    exact congrArg Subtype.val (O.tau.apply_symm_apply ⟨C, W.2⟩)
  have huI : Injective (sigma.obj T.u) :=
    W.1.2.resolve_left W.2
  let X : HookM5Preliminary.InjectiveMiddleProjectiveFirst sigma AR :=
    ⟨⟨P, huNot, huI⟩, by
      rw [hrotated]
      simpa [C, HookWallBadBUnrestricted.associatedArrow] using
        W.1.1.1.z_projective⟩
  have hhook : P.hookArrow sigma AR = T.secondArrow sigma AR := by
    simp [HookM5Preliminary.hookArrow, P, huNot]
  refine ⟨X, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hrotated
  · exact hhook

include K AR in
/-- The term underlying the inverse outer `M3`-to-`M5` reconstruction. -/
def toHookM5Preliminary :
    HookM5Preliminary.InjectiveMiddleProjectiveFirst sigma AR :=
  (W.hookM5PreliminaryReconstruction (K := K) sigma AR).term

include K AR in
/-- The recovered `M5` occurrence is literally the original outer `M3`
common-target pair. -/
theorem toHookM5Preliminary_commonTargetPair :
    (W.toHookM5Preliminary (K := K) sigma AR).1.1.commonTargetPair sigma AR =
      W.1.1.commonTargetPair sigma AR :=
  (W.hookM5PreliminaryReconstruction (K := K) sigma AR).occurrence_eq

end HookWallBadBUnrestricted.InjectiveEndpointFirstNoninjective

include K AR in
/-- The only possible outer `M5`/`M3` overlap is exact: projective-first
outer `M5` terms are equivalent to outer `M3` terms whose fourth source is
noninjective, with the common-target occurrence preserved. -/
def hookM5ProjectiveFirstEquivHookWallBadBFirstNoninjective :
    HookM5Preliminary.InjectiveMiddleProjectiveFirst sigma AR ≃
      HookWallBadBUnrestricted.InjectiveEndpointFirstNoninjective sigma AR where
  toFun M := M.toHookWallBadB sigma AR
  invFun W := W.toHookM5Preliminary (K := K) sigma AR
  left_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    apply HookM5Preliminary.commonTargetPair_injective sigma AR
    rw [HookWallBadBUnrestricted.InjectiveEndpointFirstNoninjective.toHookM5Preliminary_commonTargetPair,
      HookM5Preliminary.InjectiveMiddleProjectiveFirst.toHookWallBadB_commonTargetPair]
  right_inv W := by
    apply Subtype.ext
    apply Subtype.ext
    apply HookWallBadBUnrestricted.commonTargetPair_injective sigma AR
    rw [HookM5Preliminary.InjectiveMiddleProjectiveFirst.toHookWallBadB_commonTargetPair,
      HookWallBadBUnrestricted.InjectiveEndpointFirstNoninjective.toHookM5Preliminary_commonTargetPair]

include K AR in
/-- Signed cancellation of the unique outer `M5`/`M3` overlap.  The
projective-first `M5` summand and noninjective-first `M3` summand are the
same finite type, leaving only no-projective `M5` and injective-first `M3`
at this endpoint. -/
theorem hookM5Outer_add_hookWallBadBFirstInjective_card_eq :
    Fintype.card (HookM5Preliminary.InjectiveMiddleEndpoint sigma AR) +
        Fintype.card
          (HookWallBadBUnrestricted.InjectiveEndpointFirstInjective
            sigma AR) =
      Fintype.card
          (HookM5Preliminary.InjectiveMiddleNoProjectiveFirst sigma AR) +
        Fintype.card
          (HookWallBadBUnrestricted.InjectiveEndpoint sigma AR) := by
  have hM5 := Fintype.card_congr
    (hookM5PreliminaryInjectiveMiddleEquivProjectiveSumNoProjective
      sigma AR)
  have hM3 := Fintype.card_congr
    (hookWallBadBInjectiveEndpointEquivFirstInjectiveSumNoninjective
      sigma AR)
  have hoverlap := Fintype.card_congr
    (hookM5ProjectiveFirstEquivHookWallBadBFirstNoninjective
      (K := K) sigma AR)
  simp only [Fintype.card_sum] at hM5 hM3
  omega

/-- An outer preliminary `M5` occurrence and an outer `M2` occurrence
cannot be the same labelled pair: the first source of the former is
noninjective, whereas the first source of the latter is injective. -/
theorem hookM5Preliminary_outer_pair_ne_hookWallBadU_outer_pair
    (M : HookM5Preliminary.InjectiveMiddleEndpoint sigma AR)
    (W : HookWallBadU.InjectiveFourthEndpoint sigma AR) :
    M.1.commonTargetPair sigma AR ≠ W.1.commonTargetPair sigma AR := by
  intro h
  have hs := congrArg
    (fun p : CommonTargetArrowPair sigma ↦ p.1.1.1.1) h
  change (M.1.rotatedAssociatedArrow sigma AR).1.1 = W.1.1.z at hs
  have hM : ¬ Injective
      (sigma.obj (M.1.rotatedAssociatedArrow sigma AR).1.1) :=
    (M.1.rotatedAssociatedArrow_isInterior sigma AR).2
  apply hM
  rw [hs]
  exact W.2

/-- An outer preliminary `M5` occurrence and an outer `M6` occurrence
cannot be the same labelled pair, by the same first-source endpoint
separation. -/
theorem hookM5Preliminary_outer_pair_ne_hookM6_outer_pair
    (M : HookM5Preliminary.InjectiveMiddleEndpoint sigma AR)
    (N : HookM6Channel.InjectiveFourthEndpoint sigma AR) :
    M.1.commonTargetPair sigma AR ≠ N.1.commonTargetPair sigma AR := by
  intro h
  have hs := congrArg
    (fun p : CommonTargetArrowPair sigma ↦ p.1.1.1.1) h
  change (M.1.rotatedAssociatedArrow sigma AR).1.1 = N.1.1.z at hs
  have hM : ¬ Injective
      (sigma.obj (M.1.rotatedAssociatedArrow sigma AR).1.1) :=
    (M.1.rotatedAssociatedArrow_isInterior sigma AR).2
  apply hM
  rw [hs]
  exact N.2

omit [Fintype iota] [DecidableEq iota] in
/-- Outer `M2` and `M3` occurrences are disjoint: their second sources
are respectively the projective first label and the nonprojective middle
label of an admissible strip. -/
theorem hookWallBadU_outer_pair_ne_hookWallBadB_outer_pair
    (W : HookWallBadU.InjectiveFourthEndpoint sigma AR)
    (Z : HookWallBadBUnrestricted.InjectiveEndpoint sigma AR) :
    W.1.commonTargetPair sigma AR ≠ Z.1.commonTargetPair sigma AR := by
  intro h
  have hs := congrArg
    (fun p : CommonTargetArrowPair sigma ↦ p.1.2.1.1) h
  change W.1.1.triple.a = Z.1.1.triple.u at hs
  apply Z.1.1.triple.u_nonprojective
  rw [← hs]
  simpa [HookWallBadU.commonTargetPair,
    StripAdmissibleTriple.firstArrow] using W.1.1.a_projective

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData
