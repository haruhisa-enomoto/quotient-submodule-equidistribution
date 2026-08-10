import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexOuterEndpointClassification
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexFullBoundaryEndpointStrata

/-!
# Aligned transport of outer four-vertex endpoints

An oriented outer endpoint consists of two labelled irreducible arrows with
a common nonprojective target, where the first source is
projective-injective and the two arrows lie on different mesh-rotation
chains.  Aligned duality reverses the arrows to a common-source pair; one
simultaneous mesh rotation restores the common-target orientation.  This
file constructs that exact equivalence and records its endpoint-coordinate
formulas.
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

/-- Common-source pairs whose common source can be advanced once toward
the injective end. -/
abbrev NoninjectiveCommonSourceArrowPair
    (_AR : rho.FiniteARTranslationData) :=
  {p : CommonSourceArrowPair rho //
    ¬ Injective (rho.obj p.1.1.1.1)}

/-- Common-target pairs whose common target can be advanced once toward
the projective end. -/
abbrev NonprojectiveCommonTargetArrowPair
    (_AR : rho.FiniteARTranslationData) :=
  {p : CommonTargetArrowPair rho //
    ¬ Projective (rho.obj p.1.1.1.2)}

noncomputable instance noninjectiveCommonSourceArrowPairFintype :
    Fintype (AR.NoninjectiveCommonSourceArrowPair rho) :=
  Fintype.ofFinite _

noncomputable instance nonprojectiveCommonTargetArrowPairFintype :
    Fintype (AR.NonprojectiveCommonTargetArrowPair rho) :=
  Fintype.ofFinite _

/-- Simultaneous one-step mesh rotation turns equality of arrow sources
into equality of arrow targets. -/
def noninjectiveCommonSourceEquivNonprojectiveCommonTarget :
    AR.NoninjectiveCommonSourceArrowPair rho ≃
      AR.NonprojectiveCommonTargetArrowPair rho where
  toFun p := by
    let O := (AR.arMeshRotationData rho).arrowOrbitData rho
    have hsecond : ¬ Injective (rho.obj p.1.1.2.1.1) := by
      rw [← p.1.2]
      exact p.2
    let first := O.tau.symm ⟨p.1.1.1, p.2⟩
    let second := O.tau.symm ⟨p.1.1.2, hsecond⟩
    have htarget : first.1.1.2 = second.1.1.2 := by
      rw [congrArg Prod.snd
          ((AR.arMeshRotationData rho).arrowOrbitData_tau_symm_val rho
            ⟨p.1.1.1, p.2⟩),
        congrArg Prod.snd
          ((AR.arMeshRotationData rho).arrowOrbitData_tau_symm_val rho
            ⟨p.1.1.2, hsecond⟩)]
      have hsource :
          (⟨p.1.1.1.1.1, p.2⟩ : rho.NoninjectiveLabel) =
            ⟨p.1.1.2.1.1, hsecond⟩ := Subtype.ext p.1.2
      exact congrArg
        (fun x ↦ ((AR.arTranslationEquiv rho).symm x).1) hsource
    exact ⟨⟨(first.1, second.1), htarget⟩, first.2⟩
  invFun p := by
    let O := (AR.arMeshRotationData rho).arrowOrbitData rho
    have hsecond : ¬ Projective (rho.obj p.1.1.2.1.2) := by
      rw [← p.1.2]
      exact p.2
    let first := O.tau ⟨p.1.1.1, p.2⟩
    let second := O.tau ⟨p.1.1.2, hsecond⟩
    have hsource : first.1.1.1 = second.1.1.1 := by
      rw [congrArg Prod.fst
          ((AR.arMeshRotationData rho).arrowOrbitData_tau_val rho
            ⟨p.1.1.1, p.2⟩),
        congrArg Prod.fst
          ((AR.arMeshRotationData rho).arrowOrbitData_tau_val rho
            ⟨p.1.1.2, hsecond⟩)]
      have htarget :
          (⟨p.1.1.1.1.2, p.2⟩ : rho.NonprojectiveLabel) =
            ⟨p.1.1.2.1.2, hsecond⟩ := Subtype.ext p.1.2
      exact congrArg (fun x ↦ (AR.arTranslation rho x).1) htarget
    exact ⟨⟨(first.1, second.1), hsource⟩, first.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        (((AR.arMeshRotationData rho).arrowOrbitData rho).tau.apply_symm_apply
          ⟨p.1.1.1, p.2⟩)
    · have hsecond : ¬ Injective (rho.obj p.1.1.2.1.1) := by
        rw [← p.1.2]
        exact p.2
      exact congrArg Subtype.val
        (((AR.arMeshRotationData rho).arrowOrbitData rho).tau.apply_symm_apply
          ⟨p.1.1.2, hsecond⟩)
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        (((AR.arMeshRotationData rho).arrowOrbitData rho).tau.symm_apply_apply
          ⟨p.1.1.1, p.2⟩)
    · have hsecond : ¬ Projective (rho.obj p.1.1.2.1.2) := by
        rw [← p.1.2]
        exact p.2
      exact congrArg Subtype.val
        (((AR.arMeshRotationData rho).arrowOrbitData rho).tau.symm_apply_apply
          ⟨p.1.1.2, hsecond⟩)

/-- The common-source presentation of an outer endpoint whose first arrow
ends at a projective-injective object. -/
abbrev FirstPITargetDifferentOrbitCommonSourcePair :=
  {p : AR.NoninjectiveCommonSourceArrowPair rho //
    Projective (rho.obj p.1.1.1.1.2) ∧
      Injective (rho.obj p.1.1.1.1.2) ∧
      let O := (AR.arMeshRotationData rho).arrowOrbitData rho
      ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2}

/-- The subtype presentation of the existing first-projective-injective
outer common-target structure. -/
abbrev FirstPISourceDifferentOrbitCommonTargetPair :=
  {p : AR.NonprojectiveCommonTargetArrowPair rho //
    Projective (rho.obj p.1.1.1.1.1) ∧
      Injective (rho.obj p.1.1.1.1.1) ∧
      let O := (AR.arMeshRotationData rho).arrowOrbitData rho
      ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2}

noncomputable instance firstPITargetDifferentOrbitCommonSourcePairFintype :
    Fintype (AR.FirstPITargetDifferentOrbitCommonSourcePair rho) :=
  Fintype.ofFinite _

noncomputable instance firstPISourceDifferentOrbitCommonTargetPairFintype :
    Fintype (AR.FirstPISourceDifferentOrbitCommonTargetPair rho) :=
  Fintype.ofFinite _

/-- One mesh step changes the projective-injective first target into a
projective-injective first source, preserving the labelled component
condition. -/
def firstPITargetCommonSourceEquivFirstPISourceCommonTarget :
    AR.FirstPITargetDifferentOrbitCommonSourcePair rho ≃
      AR.FirstPISourceDifferentOrbitCommonTargetPair rho := by
  classical
  let E := AR.noninjectiveCommonSourceEquivNonprojectiveCommonTarget rho
  apply E.subtypeEquiv
  intro p
  let O := (AR.arMeshRotationData rho).arrowOrbitData rho
  have hsecond : ¬ Injective (rho.obj p.1.1.2.1.1) := by
    rw [← p.1.2]
    exact p.2
  have hfirstVal :=
    (AR.arMeshRotationData rho).arrowOrbitData_tau_symm_val rho
      ⟨p.1.1.1, p.2⟩
  have hfirstSource : (E p).1.1.1.1.1 = p.1.1.1.1.2 := by
    exact congrArg Prod.fst hfirstVal
  have hfirstSuccessor : O.successor p.1.1.1 = (E p).1.1.1 := by
    change (if hI : Injective (rho.obj p.1.1.1.1.1) then p.1.1.1
      else (O.tau.symm ⟨p.1.1.1, hI⟩).1) = _
    rw [dif_neg p.2]
    apply congrArg Subtype.val
    apply congrArg O.tau.symm
    apply Subtype.ext
    rfl
  have hsecondSuccessor : O.successor p.1.1.2 = (E p).1.1.2 := by
    change (if hI : Injective (rho.obj p.1.1.2.1.1) then p.1.1.2
      else (O.tau.symm ⟨p.1.1.2, hI⟩).1) = _
    rw [dif_neg hsecond]
    apply congrArg Subtype.val
    apply congrArg O.tau.symm
    apply Subtype.ext
    rfl
  rw [hfirstSource]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  change (¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2) ↔
    ¬ O.SameSuccessorOrbit (E p).1.1.1 (E p).1.1.2
  rw [← hfirstSuccessor, ← hsecondSuccessor,
    O.sameSuccessorOrbit_successor_iff]

/-- Reassociate the subtype presentation with the named oriented outer
endpoint structure. -/
def firstPISourceSubtypeEquivOuter :
    AR.FirstPISourceDifferentOrbitCommonTargetPair rho ≃
      AR.FirstProjectiveInjectiveDifferentOrbitOuterPair rho where
  toFun p :=
    { pair := p.1.1
      target_nonprojective := p.1.2
      first_projective := p.2.1
      first_injective := p.2.2.1
      differentOrbit := p.2.2.2 }
  invFun p :=
    ⟨⟨p.pair, p.target_nonprojective⟩,
      p.first_projective, p.first_injective, p.differentOrbit⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq jota] in
/-- Rotating a noninjective common source once and then applying AR
translation to the new common target recovers the old common source. -/
theorem noninjectiveCommonSourceEquiv_arTranslation_commonTarget
    (p : AR.NoninjectiveCommonSourceArrowPair rho) :
    let E := AR.noninjectiveCommonSourceEquivNonprojectiveCommonTarget rho
    (AR.arTranslation rho
      ⟨(E p).1.1.1.1.2, (E p).2⟩).1 = p.1.1.1.1.1 := by
  let E := AR.noninjectiveCommonSourceEquivNonprojectiveCommonTarget rho
  have h := (AR.arTranslationEquiv rho).apply_symm_apply
    (⟨p.1.1.1.1.1, p.2⟩ : rho.NoninjectiveLabel)
  exact congrArg Subtype.val h

end FiniteARTranslationData

namespace AlignedBiduality

/-- Arrow reversal turns a nonprojective common target into a
noninjective common source. -/
def nonprojectiveCommonTargetEquivNoninjectiveCommonSource
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    ARsigma.NonprojectiveCommonTargetArrowPair sigma ≃
      ARtau.NoninjectiveCommonSourceArrowPair tau where
  toFun p := by
    let first := D.pushforwardIrreduciblePair sigma tau p.1.1.1
    let second := D.pushforwardIrreduciblePair sigma tau p.1.1.2
    have hsource : first.1.1 = second.1.1 := by
      exact congrArg D.forward.labelEquiv p.1.2
    exact ⟨⟨(first, second), hsource⟩,
      D.pushforwardIrreduciblePair_source_noninjective
        sigma tau p.1.1.1 p.2⟩
  invFun p := by
    let first := D.pullbackIrreduciblePair sigma tau p.1.1.1
    let second := D.pullbackIrreduciblePair sigma tau p.1.1.2
    have htarget : first.1.2 = second.1.2 := by
      exact congrArg D.forward.labelEquiv.symm p.1.2
    exact ⟨⟨(first, second), htarget⟩,
      D.pullbackIrreduciblePair_target_nonprojective
        sigma tau p.1.1.1 p.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (D.irreduciblePairEquiv sigma tau).apply_symm_apply p.1.1.1
    · exact (D.irreduciblePairEquiv sigma tau).apply_symm_apply p.1.1.2
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (D.irreduciblePairEquiv sigma tau).symm_apply_apply p.1.1.1
    · exact (D.irreduciblePairEquiv sigma tau).symm_apply_apply p.1.1.2

/-- On the projective-injective first endpoint, arrow reversal exchanges
the first-source and first-target presentations and preserves the two
labelled successor components. -/
def firstPISourceCommonTargetEquivFirstPITargetCommonSource
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    ARsigma.FirstPISourceDifferentOrbitCommonTargetPair sigma ≃
      ARtau.FirstPITargetDifferentOrbitCommonSourcePair tau := by
  let E := D.nonprojectiveCommonTargetEquivNoninjectiveCommonSource
    sigma tau ARsigma ARtau
  apply E.subtypeEquiv
  intro p
  have hProjective :=
    D.forward.injective_iff_projective_image sigma tau p.1.1.1.1.1
  have hInjective :=
    D.forward.projective_iff_injective_image sigma tau p.1.1.1.1.1
  have hOrbit :=
    D.pullback_arrowOrbit_sameSuccessorOrbit_iff sigma tau ARsigma ARtau
      (E p).1.1.1 (E p).1.1.2
  have hfirstTarget :
      (E p).1.1.1.1.2 = D.forward.labelEquiv p.1.1.1.1.1 := by
    rfl
  have hfirstPullback :
      D.pullbackIrreduciblePair sigma tau (E p).1.1.1 = p.1.1.1 := by
    apply Subtype.ext
    apply Prod.ext <;> simp [E,
      nonprojectiveCommonTargetEquivNoninjectiveCommonSource,
      pullbackIrreduciblePair, pushforwardIrreduciblePair]
  have hsecondPullback :
      D.pullbackIrreduciblePair sigma tau (E p).1.1.2 = p.1.1.2 := by
    apply Subtype.ext
    apply Prod.ext <;> simp [E,
      nonprojectiveCommonTargetEquivNoninjectiveCommonSource,
      pullbackIrreduciblePair, pushforwardIrreduciblePair]
  let Oσ := (ARsigma.arMeshRotationData sigma).arrowOrbitData sigma
  let Oτ := (ARtau.arMeshRotationData tau).arrowOrbitData tau
  change
    (Projective (sigma.obj p.1.1.1.1.1) ∧
        Injective (sigma.obj p.1.1.1.1.1) ∧
        ¬ Oσ.SameSuccessorOrbit p.1.1.1 p.1.1.2) ↔
      (Projective (tau.obj (E p).1.1.1.1.2) ∧
        Injective (tau.obj (E p).1.1.1.1.2) ∧
        ¬ Oτ.SameSuccessorOrbit (E p).1.1.1 (E p).1.1.2)
  constructor
  · rintro ⟨hP, hI, hDifferent⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hfirstTarget]
      exact hProjective.1 hI
    · rw [hfirstTarget]
      exact hInjective.1 hP
    · intro hSame
      apply hDifferent
      have := hOrbit.1 hSame
      simpa [hfirstPullback, hsecondPullback] using this
  · rintro ⟨hP, hI, hDifferent⟩
    refine ⟨?_, ?_, ?_⟩
    · apply hInjective.2
      rw [← hfirstTarget]
      exact hI
    · apply hProjective.2
      rw [← hfirstTarget]
      exact hP
    · intro hSame
      apply hDifferent
      apply hOrbit.2
      simpa [hfirstPullback, hsecondPullback] using hSame

/-- Canonical aligned transport of oriented outer endpoints: reverse both
arrows, then rotate the resulting common-source pair once. -/
def firstPIOuterEquivAligned
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma ≃
      ARtau.FirstProjectiveInjectiveDifferentOrbitOuterPair tau :=
  (ARsigma.firstPISourceSubtypeEquivOuter sigma).symm |>.trans
    ((D.firstPISourceCommonTargetEquivFirstPITargetCommonSource
      sigma tau ARsigma ARtau).trans
      ((ARtau.firstPITargetCommonSourceEquivFirstPISourceCommonTarget tau).trans
        (ARtau.firstPISourceSubtypeEquivOuter tau)))

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- The aligned outer transport swaps projectivity of the second source
with injectivity on the transported second source. -/
theorem firstPIOuterEquivAligned_second_source
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma) :
    (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p).pair.1.2.1.1 =
      D.forward.labelEquiv p.pair.1.2.1.1 := by
  let q : ARsigma.FirstPISourceDifferentOrbitCommonTargetPair sigma :=
    (ARsigma.firstPISourceSubtypeEquivOuter sigma).symm p
  let r : ARtau.FirstPITargetDifferentOrbitCommonSourcePair tau :=
    D.firstPISourceCommonTargetEquivFirstPITargetCommonSource
      sigma tau ARsigma ARtau q
  have hsecond : ¬ Injective (tau.obj r.1.1.1.2.1.1) := by
    rw [← r.1.1.2]
    exact r.1.2
  have hval :=
    (ARtau.arMeshRotationData tau).arrowOrbitData_tau_symm_val tau
      ⟨r.1.1.1.2, hsecond⟩
  have hsource := congrArg Prod.fst hval
  simpa [firstPIOuterEquivAligned, q, r,
    FiniteARTranslationData.firstPITargetCommonSourceEquivFirstPISourceCommonTarget,
    FiniteARTranslationData.noninjectiveCommonSourceEquivNonprojectiveCommonTarget,
    firstPISourceCommonTargetEquivFirstPITargetCommonSource,
    nonprojectiveCommonTargetEquivNoninjectiveCommonSource,
    FiniteARTranslationData.firstPISourceSubtypeEquivOuter,
    pushforwardIrreduciblePair] using hsource

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
theorem firstPIOuterEquivAligned_second_projective_iff_injective
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma) :
    Projective (sigma.obj p.pair.1.2.1.1) ↔
      Injective (tau.obj
        (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p).pair.1.2.1.1) := by
  rw [D.firstPIOuterEquivAligned_second_source sigma tau ARsigma ARtau p]
  exact D.forward.projective_iff_injective_image sigma tau p.pair.1.2.1.1

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
theorem firstPIOuterEquivAligned_second_injective_iff_projective
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma) :
    Injective (sigma.obj p.pair.1.2.1.1) ↔
      Projective (tau.obj
        (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p).pair.1.2.1.1) := by
  rw [D.firstPIOuterEquivAligned_second_source sigma tau ARsigma ARtau p]
  exact D.forward.injective_iff_projective_image sigma tau p.pair.1.2.1.1

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- The AR translate of the transported common target is the dual image
of the original common target. -/
theorem firstPIOuterEquivAligned_arTranslation_commonTarget
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma) :
    (ARtau.arTranslation tau
      ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p).pair.1.1.1.2,
        (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p).target_nonprojective⟩).1 =
      D.forward.labelEquiv p.pair.1.1.1.2 := by
  let q : ARsigma.FirstPISourceDifferentOrbitCommonTargetPair sigma :=
    (ARsigma.firstPISourceSubtypeEquivOuter sigma).symm p
  let r : ARtau.FirstPITargetDifferentOrbitCommonSourcePair tau :=
    D.firstPISourceCommonTargetEquivFirstPITargetCommonSource
      sigma tau ARsigma ARtau q
  have h :=
    ARtau.noninjectiveCommonSourceEquiv_arTranslation_commonTarget tau r.1
  simpa [firstPIOuterEquivAligned, q, r,
    FiniteARTranslationData.firstPITargetCommonSourceEquivFirstPISourceCommonTarget,
    FiniteARTranslationData.firstPISourceSubtypeEquivOuter,
    firstPISourceCommonTargetEquivFirstPITargetCommonSource,
    nonprojectiveCommonTargetEquivNoninjectiveCommonSource,
    pushforwardIrreduciblePair] using h

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- Pulling back the transported common target gives the AR translate of
the original common target. -/
theorem firstPIOuterEquivAligned_symm_commonTarget_eq_arTranslation
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma) :
    D.forward.labelEquiv.symm
        (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p).pair.1.1.1.2 =
      (ARsigma.arTranslation sigma
        ⟨p.pair.1.1.1.2, p.target_nonprojective⟩).1 := by
  let Ep := D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p
  let q : tau.NonprojectiveLabel :=
    ⟨Ep.pair.1.1.1.2, Ep.target_nonprojective⟩
  let x : sigma.NoninjectiveLabel :=
    ⟨D.forward.labelEquiv.symm q.1, by
      intro hinj
      apply q.2
      simpa using
        ((D.forward.injective_iff_projective_image sigma tau
          (D.forward.labelEquiv.symm q.1)).1 hinj)⟩
  let t : sigma.NonprojectiveLabel :=
    ⟨p.pair.1.1.1.2, p.target_nonprojective⟩
  have hdual :=
    D.forward_symm_arTranslation_eq_inverse sigma tau ARsigma ARtau q
  have htranslated :=
    D.firstPIOuterEquivAligned_arTranslation_commonTarget
      sigma tau ARsigma ARtau p
  have hinverse : (ARsigma.arTranslationEquiv sigma).symm x = t := by
    apply Subtype.ext
    rw [← hdual]
    simpa [q, Ep] using congrArg D.forward.labelEquiv.symm htranslated
  have hforward := congrArg (ARsigma.arTranslationEquiv sigma) hinverse
  have hx : x = (ARsigma.arTranslationEquiv sigma) t := by
    simpa using hforward
  exact congrArg (fun z : sigma.NoninjectiveLabel ↦ z.1) hx

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- Injectivity of the transported common target is projectivity of the
original translated target. -/
theorem firstPIOuterEquivAligned_target_injective_iff_translatedTarget_projective
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma) :
    Injective (tau.obj
        (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p).pair.1.1.1.2) ↔
      Projective
        (sigma.obj (ARsigma.arTranslation sigma
          ⟨p.pair.1.1.1.2, p.target_nonprojective⟩).1) := by
  let t' :=
    (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p).pair.1.1.1.2
  have h := D.forward.projective_iff_injective_image sigma tau
    (D.forward.labelEquiv.symm t')
  have hsymm :=
    D.firstPIOuterEquivAligned_symm_commonTarget_eq_arTranslation
      sigma tau ARsigma ARtau p
  have himage :
      D.forward.labelEquiv
          (ARsigma.arTranslation sigma
            ⟨p.pair.1.1.1.2, p.target_nonprojective⟩).1 = t' := by
    rw [← hsymm]
    simp [t']
  rw [hsymm, himage] at h
  exact h.symm

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- Projectivity of the transported target translate is exactly
injectivity of the original common target. -/
theorem firstPIOuterEquivAligned_translatedTarget_projective_iff_target_injective
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma) :
    Projective
        (tau.obj (ARtau.arTranslation tau
          ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p).pair.1.1.1.2,
            (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p).target_nonprojective⟩).1) ↔
      Injective (sigma.obj p.pair.1.1.1.2) := by
  rw [D.firstPIOuterEquivAligned_arTranslation_commonTarget
    sigma tau ARsigma ARtau p]
  exact (D.forward.injective_iff_projective_image
    sigma tau p.pair.1.1.1.2).symm

include K in
theorem projectiveTarget_add_literal_boundary_card_eq
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    Fintype.card
          (ARsigma.DifferentOrbitProjectiveTargetCommonTargetPair sigma) +
        Fintype.card
          (ARsigma.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma) =
      Fintype.card
          (ARtau.DifferentOrbitProjectiveTargetCommonTargetPair tau) +
        Fintype.card
          (ARtau.InteriorDifferentOrbitLiteralSourceCommonTargetPair tau) := by
  have hfull := D.differentOrbitFullEndpoint_oneSide_strata_card_identity
    (K := K) sigma tau ARsigma ARtau
  have hsourceSigma := Fintype.card_congr
    (ARsigma.differentOrbitSourceBoundaryCommonTargetEquivProjectiveTargetSumProjectiveSource
      sigma)
  have hsourceTau := Fintype.card_congr
    (ARtau.differentOrbitSourceBoundaryCommonTargetEquivProjectiveTargetSumProjectiveSource
      tau)
  have hcornerSigma :=
    ARsigma.differentOrbitNonprojectiveTargetProjectiveSource_card_eq_interiorLiteral_add_outer
      sigma
  have hcornerTau :=
    ARtau.differentOrbitNonprojectiveTargetProjectiveSource_card_eq_interiorLiteral_add_outer
      tau
  have htrimSigma :=
    ARsigma.fullOrbitDifferentInteriorLiteral_card_eq_interiorDifferentOrbitLiteral
      (K := K) sigma
  have htrimTau :=
    ARtau.fullOrbitDifferentInteriorLiteral_card_eq_interiorDifferentOrbitLiteral
      (K := K) tau
  have hliteral := D.interiorDifferentOrbitLiteral_card_eq_noProjective
    (K := K) sigma tau ARsigma ARtau
  simp only [Fintype.card_sum] at hsourceSigma hsourceTau
  omega

end AlignedBiduality

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
