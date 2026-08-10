import OpConjecture.RepresentationTheory.FourVertexFullBoundaryCorners
import OpConjecture.RepresentationTheory.FourVertexStripReversal

/-!
# One-step incidence on the full four-vertex arrow boundary

The full common-source source boundary splits into a literal projective-target
layer and a genuine second layer.  One mesh rotation identifies that genuine
second layer with the projective-target common-target corner.  In contrast to
the trimmed incidence bridge, there is no terminal correction: an irreducible
arrow ending at a projective cannot start at an injective.
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

/-- Full common-source pairs for which at least one arrow ends at a
projective. -/
abbrev ProjectiveTargetCommonSourcePair :=
  {p : CommonSourceArrowPair sigma //
    Projective (sigma.obj p.1.1.1.2) ∨
      Projective (sigma.obj p.1.2.1.2)}

/-- Full common-source source-boundary pairs for which neither arrow is in
the literal projective-target layer. -/
abbrev SecondOnlySourceCommonSourcePair :=
  {p : AR.SourceBoundaryCommonSourceArrowPair sigma //
    ¬ (Projective (sigma.obj p.1.1.1.1.2) ∨
      Projective (sigma.obj p.1.1.2.1.2))}

noncomputable instance projectiveTargetCommonSourcePairFintype :
    Fintype (ProjectiveTargetCommonSourcePair sigma) := Fintype.ofFinite _

noncomputable instance secondOnlySourceCommonSourcePairFintype :
    Fintype (AR.SecondOnlySourceCommonSourcePair sigma) := Fintype.ofFinite _

/-- Different-component part of the literal projective-target
common-source layer. -/
abbrev DifferentOrbitProjectiveTargetCommonSourcePair :=
  {p : ProjectiveTargetCommonSourcePair sigma //
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2}

/-- Different-component part of the genuine second full common-source
boundary layer. -/
abbrev DifferentOrbitSecondOnlySourceCommonSourcePair :=
  {p : AR.SecondOnlySourceCommonSourcePair sigma //
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit p.1.1.1.1 p.1.1.1.2}

/-- Different-component part of the projective-target common-target
corner. -/
abbrev DifferentOrbitProjectiveTargetCommonTargetPair :=
  {p : ProjectiveTargetCommonTargetPair sigma //
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2}

/-- Different-component part of the nonprojective-target,
projective-source common-target corner. -/
abbrev DifferentOrbitNonprojectiveTargetProjectiveSourcePair :=
  {p : NonprojectiveTargetProjectiveSourcePair sigma //
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2}

noncomputable instance
    differentOrbitProjectiveTargetCommonSourcePairFintype :
    Fintype (AR.DifferentOrbitProjectiveTargetCommonSourcePair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitSecondOnlySourceCommonSourcePairFintype :
    Fintype (AR.DifferentOrbitSecondOnlySourceCommonSourcePair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitProjectiveTargetCommonTargetPairFintype :
    Fintype (AR.DifferentOrbitProjectiveTargetCommonTargetPair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitNonprojectiveTargetProjectiveSourcePairFintype :
    Fintype
      (AR.DifferentOrbitNonprojectiveTargetProjectiveSourcePair sigma) :=
  Fintype.ofFinite _

/-- Split the full common-source source boundary into its literal first
layer and genuine second-layer remainder. -/
def sourceBoundaryCommonSourceEquivProjectiveTargetSumSecondOnly :
    AR.SourceBoundaryCommonSourceArrowPair sigma ≃
      ProjectiveTargetCommonSourcePair sigma ⊕
        AR.SecondOnlySourceCommonSourcePair sigma where
  toFun p := by
    classical
    by_cases h : Projective (sigma.obj p.1.1.1.1.2) ∨
        Projective (sigma.obj p.1.1.2.1.2)
    · exact Sum.inl ⟨p.1, h⟩
    · exact Sum.inr ⟨p, h⟩
  invFun p := by
    rcases p with p | p
    · exact ⟨p.1, by
        rcases p.2 with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)⟩
    · exact p.1
  left_inv p := by
    classical
    by_cases h : Projective (sigma.obj p.1.1.1.1.2) ∨
        Projective (sigma.obj p.1.1.2.1.2)
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.2]
    · simp [p.2]

/-- Rotating both arrows once identifies the genuine second
common-source layer with the projective-target common-target corner. -/
def secondOnlyCommonSourceEquivProjectiveTargetCommonTarget
    (source_noninjective : ∀ a : sigma.IrreduciblePair,
      Projective (sigma.obj a.1.2) → ¬ Injective (sigma.obj a.1.1)) :
    AR.SecondOnlySourceCommonSourcePair sigma ≃
      ProjectiveTargetCommonTargetPair sigma where
  toFun p := by
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    have hA : ¬ Projective (sigma.obj p.1.1.1.1.1.2) :=
      fun h ↦ p.2 (Or.inl h)
    have hB : ¬ Projective (sigma.obj p.1.1.1.2.1.2) :=
      fun h ↦ p.2 (Or.inr h)
    let A := O.tau ⟨p.1.1.1.1, hA⟩
    let B := O.tau ⟨p.1.1.1.2, hB⟩
    have htarget : A.1.1.2 = B.1.1.2 := by
      rw [congrArg Prod.snd
          ((AR.arMeshRotationData sigma).arrowOrbitData_tau_val sigma
            ⟨p.1.1.1.1, hA⟩),
        congrArg Prod.snd
          ((AR.arMeshRotationData sigma).arrowOrbitData_tau_val sigma
            ⟨p.1.1.1.2, hB⟩)]
      exact p.1.1.2
    refine ⟨⟨(A.1, B.1), htarget⟩, ?_⟩
    rcases p.1.2 with h | h
    · rcases h with h | h
      · exact (hA h).elim
      · exact h hA
    · rcases h with h | h
      · exact (hB h).elim
      · rw [htarget]
        exact h hB
  invFun p := by
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    have hA : ¬ Injective (sigma.obj p.1.1.1.1.1) :=
      source_noninjective p.1.1.1 p.2
    have hB : ¬ Injective (sigma.obj p.1.1.2.1.1) := by
      apply source_noninjective p.1.1.2
      rw [← p.1.2]
      exact p.2
    let A := O.tau.symm ⟨p.1.1.1, hA⟩
    let B := O.tau.symm ⟨p.1.1.2, hB⟩
    have hsource : A.1.1.1 = B.1.1.1 := by
      rw [congrArg Prod.fst
          ((AR.arMeshRotationData sigma).arrowOrbitData_tau_symm_val sigma
            ⟨p.1.1.1, hA⟩),
        congrArg Prod.fst
          ((AR.arMeshRotationData sigma).arrowOrbitData_tau_symm_val sigma
            ⟨p.1.1.2, hB⟩)]
      exact p.1.2
    refine ⟨⟨⟨(A.1, B.1), hsource⟩, ?_⟩, ?_⟩
    · left
      right
      intro hnot
      have hinput : (⟨A.1, hnot⟩ : {a : sigma.IrreduciblePair //
          ¬ Projective (sigma.obj a.1.2)}) = O.tau.symm ⟨p.1.1.1, hA⟩ := by
        apply Subtype.ext
        rfl
      have hforward := congrArg O.tau hinput
      have hback := O.tau.apply_symm_apply ⟨p.1.1.1, hA⟩
      rw [congrArg Subtype.val (hforward.trans hback)]
      exact p.2
    · intro h
      rcases h with h | h
      · exact A.2 h
      · exact B.2 h
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        (((AR.arMeshRotationData sigma).arrowOrbitData sigma).tau.symm_apply_apply
          ⟨p.1.1.1.1,
            fun h ↦ p.2 (Or.inl h)⟩)
    · exact congrArg Subtype.val
        (((AR.arMeshRotationData sigma).arrowOrbitData sigma).tau.symm_apply_apply
          ⟨p.1.1.1.2,
            fun h ↦ p.2 (Or.inr h)⟩)
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        (((AR.arMeshRotationData sigma).arrowOrbitData sigma).tau.apply_symm_apply
          ⟨p.1.1.1,
            source_noninjective p.1.1.1 p.2⟩)
    · exact congrArg Subtype.val
        (((AR.arMeshRotationData sigma).arrowOrbitData sigma).tau.apply_symm_apply
          ⟨p.1.1.2, by
            apply source_noninjective p.1.1.2
            rw [← p.1.2]
            exact p.2⟩)

/-- The full common-target corner decomposition restricts to pairs from
different successor components. -/
def differentOrbitSourceBoundaryCommonTargetEquivProjectiveTargetSumProjectiveSource :
    AR.DifferentOrbitSourceBoundaryCommonTargetArrowPair sigma ≃
      AR.DifferentOrbitProjectiveTargetCommonTargetPair sigma ⊕
        AR.DifferentOrbitNonprojectiveTargetProjectiveSourcePair sigma := by
  let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
  let E := sourceBoundaryCommonTargetEquivProjectiveTargetSumProjectiveSource
    sigma AR
  let P : AR.SourceBoundaryCommonTargetArrowPair sigma → Prop :=
    fun p ↦ ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2
  let Q : ProjectiveTargetCommonTargetPair sigma ⊕
      NonprojectiveTargetProjectiveSourcePair sigma → Prop :=
    fun p ↦ P (E.symm p)
  have hPQ : ∀ p, P p ↔ Q (E p) := by
    intro p
    change P p ↔ P (E.symm (E p))
    rw [E.symm_apply_apply]
  let F := (E.subtypeEquiv hPQ).trans (Equiv.subtypeSum (p := Q))
  let L : {p : ProjectiveTargetCommonTargetPair sigma // Q (Sum.inl p)} ≃
      AR.DifferentOrbitProjectiveTargetCommonTargetPair sigma := by
    apply (Equiv.refl _).subtypeEquiv
    intro p
    change P (E.symm (Sum.inl p)) ↔
      ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2
    rfl
  let R : {p : NonprojectiveTargetProjectiveSourcePair sigma //
      Q (Sum.inr p)} ≃
      AR.DifferentOrbitNonprojectiveTargetProjectiveSourcePair sigma := by
    apply (Equiv.refl _).subtypeEquiv
    intro p
    change (¬ O.SameSuccessorOrbit
        (E.symm (Sum.inr p)).1.1.1 (E.symm (Sum.inr p)).1.1.2) ↔
      ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2
    have hval : (E.symm (Sum.inr p)).1 = p.1 := by
      by_cases h : Projective (sigma.obj p.1.1.1.1.1)
      · simp [E,
          sourceBoundaryCommonTargetEquivProjectiveTargetSumProjectiveSource,
          h]
      · simp [E,
          sourceBoundaryCommonTargetEquivProjectiveTargetSumProjectiveSource,
          h]
    rw [hval]
  exact F.trans (Equiv.sumCongr L R)

/-- The full common-source literal/second-layer decomposition restricts to
pairs from different successor components. -/
def differentOrbitSourceBoundaryCommonSourceEquivProjectiveTargetSumSecondOnly :
    AR.DifferentOrbitSourceBoundaryCommonSourceArrowPair sigma ≃
      AR.DifferentOrbitProjectiveTargetCommonSourcePair sigma ⊕
        AR.DifferentOrbitSecondOnlySourceCommonSourcePair sigma := by
  let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
  let E := AR.sourceBoundaryCommonSourceEquivProjectiveTargetSumSecondOnly
    sigma
  let P : AR.SourceBoundaryCommonSourceArrowPair sigma → Prop :=
    fun p ↦ ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2
  let Q : ProjectiveTargetCommonSourcePair sigma ⊕
      AR.SecondOnlySourceCommonSourcePair sigma → Prop :=
    fun p ↦ P (E.symm p)
  have hPQ : ∀ p, P p ↔ Q (E p) := by
    intro p
    change P p ↔ P (E.symm (E p))
    rw [E.symm_apply_apply]
  let F := (E.subtypeEquiv hPQ).trans (Equiv.subtypeSum (p := Q))
  simpa [P, Q, E,
    sourceBoundaryCommonSourceEquivProjectiveTargetSumSecondOnly] using F

omit [DecidableEq iota] in
/-- Rotating the full genuine second common-source layer preserves and
reflects the successor component of its two labelled occurrences. -/
theorem secondOnlyCommonSourceEquiv_sameSuccessorOrbit_iff
    (source_noninjective : ∀ a : sigma.IrreduciblePair,
      Projective (sigma.obj a.1.2) → ¬ Injective (sigma.obj a.1.1))
    (p : AR.SecondOnlySourceCommonSourcePair sigma) :
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    let E := AR.secondOnlyCommonSourceEquivProjectiveTargetCommonTarget
      sigma source_noninjective
    O.SameSuccessorOrbit (E p).1.1.1 (E p).1.1.2 ↔
      O.SameSuccessorOrbit p.1.1.1.1 p.1.1.1.2 := by
  let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
  let E := AR.secondOnlyCommonSourceEquivProjectiveTargetCommonTarget
    sigma source_noninjective
  let A₀ := p.1.1.1.1
  let B₀ := p.1.1.1.2
  have hA : ¬ Projective (sigma.obj A₀.1.2) :=
    fun h ↦ p.2 (Or.inl h)
  have hB : ¬ Projective (sigma.obj B₀.1.2) :=
    fun h ↦ p.2 (Or.inr h)
  let A := (O.tau ⟨A₀, hA⟩).1
  let B := (O.tau ⟨B₀, hB⟩).1
  have hAstep : O.successor A = A₀ := by
    have hnotTarget : ¬ (fun a : sigma.IrreduciblePair ↦
        Injective (sigma.obj a.1.1)) A := by
      exact (O.tau ⟨A₀, hA⟩).2
    rw [show O.successor A = (O.tau.symm ⟨A, hnotTarget⟩).1 by
      simp [OpConjecture.BoundaryTranslationChains.Data.successor,
        hnotTarget]]
    exact congrArg Subtype.val (O.tau.symm_apply_apply ⟨A₀, hA⟩)
  have hBstep : O.successor B = B₀ := by
    have hnotTarget : ¬ (fun a : sigma.IrreduciblePair ↦
        Injective (sigma.obj a.1.1)) B := by
      exact (O.tau ⟨B₀, hB⟩).2
    rw [show O.successor B = (O.tau.symm ⟨B, hnotTarget⟩).1 by
      simp [OpConjecture.BoundaryTranslationChains.Data.successor,
        hnotTarget]]
    exact congrArg Subtype.val (O.tau.symm_apply_apply ⟨B₀, hB⟩)
  have hAorbit : O.SameSuccessorOrbit A A₀ := by
    exact ⟨1, 0, by simpa only [Function.iterate_one,
      Function.iterate_zero, id_eq] using hAstep⟩
  have hBorbit : O.SameSuccessorOrbit B B₀ := by
    exact ⟨1, 0, by simpa only [Function.iterate_one,
      Function.iterate_zero, id_eq] using hBstep⟩
  change O.SameSuccessorOrbit A B ↔
    O.SameSuccessorOrbit A₀ B₀
  exact O.sameSuccessorOrbit_congr_of_related hAorbit hBorbit

/-- The full one-step rotation equivalence restricts exactly to different
successor components. -/
def differentOrbitSecondOnlyCommonSourceEquivProjectiveTargetCommonTarget
    (source_noninjective : ∀ a : sigma.IrreduciblePair,
      Projective (sigma.obj a.1.2) → ¬ Injective (sigma.obj a.1.1)) :
    AR.DifferentOrbitSecondOnlySourceCommonSourcePair sigma ≃
      AR.DifferentOrbitProjectiveTargetCommonTargetPair sigma := by
  let E := AR.secondOnlyCommonSourceEquivProjectiveTargetCommonTarget
    sigma source_noninjective
  apply E.subtypeEquiv
  intro p
  exact not_congr <|
    (AR.secondOnlyCommonSourceEquiv_sameSuccessorOrbit_iff
      sigma source_noninjective p).symm

include K AR in
omit [DecidableEq iota] in
/-- Cardinal one-step incidence identity on the full source boundary,
restricted to two different intrinsic labelled-arrow components. -/
theorem differentOrbitSourceBoundaryCommonTarget_add_projectiveTargetCommonSource_card_eq :
    Fintype.card
          (AR.DifferentOrbitSourceBoundaryCommonTargetArrowPair sigma) +
        Fintype.card
          (AR.DifferentOrbitProjectiveTargetCommonSourcePair sigma) =
      Fintype.card
          (AR.DifferentOrbitSourceBoundaryCommonSourceArrowPair sigma) +
        Fintype.card
          (AR.DifferentOrbitNonprojectiveTargetProjectiveSourcePair
            sigma) := by
  have htarget := Fintype.card_congr
    (AR.differentOrbitSourceBoundaryCommonTargetEquivProjectiveTargetSumProjectiveSource
      sigma)
  have hsource := Fintype.card_congr
    (AR.differentOrbitSourceBoundaryCommonSourceEquivProjectiveTargetSumSecondOnly
      sigma)
  have hrotate := Fintype.card_congr
    (AR.differentOrbitSecondOnlyCommonSourceEquivProjectiveTargetCommonTarget
      sigma (fun a ha ↦ arrowToProjective_source_noninjective
        (K := K) sigma a ha))
  simp only [Fintype.card_sum] at htarget hsource
  omega

omit [DecidableEq iota] in
include K AR in
/-- Cardinal one-step incidence identity on the untrimmed source boundary. -/
theorem sourceBoundaryCommonTarget_add_projectiveTargetCommonSource_card_eq :
    Fintype.card (AR.SourceBoundaryCommonTargetArrowPair sigma) +
        Fintype.card (ProjectiveTargetCommonSourcePair sigma) =
      Fintype.card (AR.SourceBoundaryCommonSourceArrowPair sigma) +
        Fintype.card (NonprojectiveTargetProjectiveSourcePair sigma) := by
  have htarget := Fintype.card_congr
    (sourceBoundaryCommonTargetEquivProjectiveTargetSumProjectiveSource
      sigma AR)
  have hsource := Fintype.card_congr
    (AR.sourceBoundaryCommonSourceEquivProjectiveTargetSumSecondOnly sigma)
  have hrotate := Fintype.card_congr
    (AR.secondOnlyCommonSourceEquivProjectiveTargetCommonTarget sigma
      (fun a ha ↦ arrowToProjective_source_noninjective
        (K := K) sigma a ha))
  simp only [Fintype.card_sum] at htarget hsource
  omega

universe w

variable {S : Type u}
  [Ring S] [Algebra K S] [FiniteDimensional K S]
  [IsNoetherianRing S]
  {kappa : Type w} [Fintype kappa] [DecidableEq kappa]
  (tau : IndecomposableSkeleton.{u, w, u} S kappa)

omit [DecidableEq iota] [DecidableEq kappa] in
include K AR in
/-- Aligned reversal cancels the two full common-target boundaries.  The
remaining full endpoint equation compares the genuine second common-target
layers with the two literal projective-target common-source layers. -/
theorem aligned_fullEndpoint_card_identity
    (ARtau : tau.FiniteARTranslationData)
    (D : AlignedBiduality sigma tau) :
    Fintype.card (NonprojectiveTargetProjectiveSourcePair sigma) +
        Fintype.card (NonprojectiveTargetProjectiveSourcePair tau) =
      Fintype.card (ProjectiveTargetCommonSourcePair sigma) +
        Fintype.card (ProjectiveTargetCommonSourcePair tau) := by
  have hsigma :=
    AR.sourceBoundaryCommonTarget_add_projectiveTargetCommonSource_card_eq
      (K := K) sigma
  have htau :=
    ARtau.sourceBoundaryCommonTarget_add_projectiveTargetCommonSource_card_eq
      (K := K) tau
  have hdualsigma :=
    D.sourceBoundaryCommonTarget_card_eq_sourceBoundaryCommonSource
      sigma tau AR ARtau
  have hdualtau :=
    D.swap.sourceBoundaryCommonTarget_card_eq_sourceBoundaryCommonSource
      tau sigma ARtau AR
  omega

include K AR in
/-- Aligned reversal cancels the two full different-component boundaries.
The surviving endpoint equality is the literal full analogue of the
manuscript's two-different-chain square shift. -/
theorem aligned_differentOrbit_fullEndpoint_card_identity
    (ARtau : tau.FiniteARTranslationData)
    (D : AlignedBiduality sigma tau) :
    Fintype.card
          (AR.DifferentOrbitNonprojectiveTargetProjectiveSourcePair sigma) +
        Fintype.card
          (ARtau.DifferentOrbitNonprojectiveTargetProjectiveSourcePair tau) =
      Fintype.card
          (AR.DifferentOrbitProjectiveTargetCommonSourcePair sigma) +
        Fintype.card
          (ARtau.DifferentOrbitProjectiveTargetCommonSourcePair tau) := by
  have hsigma :=
    AR.differentOrbitSourceBoundaryCommonTarget_add_projectiveTargetCommonSource_card_eq
      (K := K) sigma
  have htau :=
    ARtau.differentOrbitSourceBoundaryCommonTarget_add_projectiveTargetCommonSource_card_eq
      (K := K) tau
  have hdualsigma :=
    D.differentOrbitSourceBoundaryCommonTarget_card_eq_sourceBoundaryCommonSource
      sigma tau AR ARtau
  have hdualtau :=
    D.swap.differentOrbitSourceBoundaryCommonTarget_card_eq_sourceBoundaryCommonSource
      tau sigma ARtau AR
  omega

omit [Algebra K S] [FiniteDimensional K S] in
include K AR in
/-- The oriented form of the aligned full different-component incidence
identity.  Unlike the symmetric endpoint identity above, this retains which
source boundary belongs to each skeleton and is therefore suitable for
matching the signed channel terms occurrence by occurrence. -/
theorem aligned_differentOrbit_fullEndpoint_oneSide_card_identity
    (ARtau : tau.FiniteARTranslationData)
    (D : AlignedBiduality sigma tau) :
    Fintype.card
          (AR.DifferentOrbitNonprojectiveTargetProjectiveSourcePair sigma) +
        Fintype.card
          (ARtau.DifferentOrbitSourceBoundaryCommonTargetArrowPair tau) =
      Fintype.card
          (AR.DifferentOrbitSourceBoundaryCommonTargetArrowPair sigma) +
        Fintype.card
          (AR.DifferentOrbitProjectiveTargetCommonSourcePair sigma) := by
  have hsigma :=
    AR.differentOrbitSourceBoundaryCommonTarget_add_projectiveTargetCommonSource_card_eq
      (K := K) sigma
  have hdual :=
    D.differentOrbitSourceBoundaryCommonTarget_card_eq_sourceBoundaryCommonSource
      sigma tau AR ARtau
  omega

end OpConjecture.IndecomposableSkeleton.FiniteARTranslationData
