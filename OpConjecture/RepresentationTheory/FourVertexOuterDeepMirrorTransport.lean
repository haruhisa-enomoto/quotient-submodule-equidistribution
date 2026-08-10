import OpConjecture.RepresentationTheory.FourVertexOuterShortChain

/-!
# Mirror coordinates of the aligned outer transport

Coordinate lemmas for transporting the deep residual fourth-hook-vertex
clauses through the canonical aligned outer transport
`firstPIOuterEquivAligned`: the transported first source is the dual
image of the original first source, and the mesh translate of the
transported second source is the dual image of the reconstructed middle
label.  Together with the compiled target coordinates these express the
mirror form of every residual clause.
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
  {iota : Type v} {kappa : Type w} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)
  (tau : IndecomposableSkeleton.{u, w, u} S kappa)

namespace AlignedBiduality

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- The aligned outer transport carries the first source to its dual
image. -/
theorem firstPIOuterEquivAligned_first_source
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma) :
    (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p).pair.1.1.1.1 =
      D.forward.labelEquiv p.pair.1.1.1.1 := by
  let q : ARsigma.FirstPISourceDifferentOrbitCommonTargetPair sigma :=
    (ARsigma.firstPISourceSubtypeEquivOuter sigma).symm p
  let r : ARtau.FirstPITargetDifferentOrbitCommonSourcePair tau :=
    D.firstPISourceCommonTargetEquivFirstPITargetCommonSource
      sigma tau ARsigma ARtau q
  have hval :=
    (ARtau.arMeshRotationData tau).arrowOrbitData_tau_symm_val tau
      ⟨r.1.1.1.1, r.1.2⟩
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
/-- The mesh translate of the transported second source is the dual image
of the reconstructed middle label. -/
theorem firstPIOuterEquivAligned_arTranslation_second_source
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma)
    (hw : ¬ Injective (sigma.obj p.pair.1.2.1.1))
    (hwNP : ¬ Projective (tau.obj
      (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau p).pair.1.2.1.1)) :
    (ARtau.arTranslation tau
        ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
            p).pair.1.2.1.1, hwNP⟩).1 =
      D.forward.labelEquiv
        ((ARsigma.arTranslationEquiv sigma).symm
          ⟨p.pair.1.2.1.1, hw⟩).1 := by
  have h := D.forward_symm_arTranslation_eq_inverse sigma tau ARsigma ARtau
    ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
        p).pair.1.2.1.1, hwNP⟩
  have hsub : (⟨D.forward.labelEquiv.symm
        (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
          p).pair.1.2.1.1, by
      intro hinj
      apply hwNP
      simpa using
        ((D.forward.injective_iff_projective_image sigma tau
          (D.forward.labelEquiv.symm
            (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
              p).pair.1.2.1.1)).1 hinj)⟩ :
      sigma.NoninjectiveLabel) = ⟨p.pair.1.2.1.1, hw⟩ := by
    apply Subtype.ext
    show D.forward.labelEquiv.symm
        (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
          p).pair.1.2.1.1 =
      p.pair.1.2.1.1
    rw [D.firstPIOuterEquivAligned_second_source sigma tau ARsigma ARtau p]
    exact D.forward.labelEquiv.symm_apply_apply p.pair.1.2.1.1
  exact (Equiv.symm_apply_eq D.forward.labelEquiv).1
    (h.trans (congrArg (fun s : sigma.NoninjectiveLabel ↦
      ((ARsigma.arTranslationEquiv sigma).symm s).1) hsub))

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- The second mesh translate of the transported common target is the
dual image of the reconstructed last label. -/
theorem firstPIOuterEquivAligned_arTranslation_sq_commonTarget
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma)
    (hI : ¬ Injective (sigma.obj p.pair.1.1.1.2))
    (htvNP : ¬ Projective (tau.obj
      (ARtau.arTranslation tau
        ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
            p).pair.1.1.1.2,
          (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
            p).target_nonprojective⟩).1)) :
    (ARtau.arTranslation tau
        ⟨(ARtau.arTranslation tau
          ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
              p).pair.1.1.1.2,
            (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
              p).target_nonprojective⟩).1, htvNP⟩).1 =
      D.forward.labelEquiv
        ((ARsigma.arTranslationEquiv sigma).symm
          ⟨p.pair.1.1.1.2, hI⟩).1 := by
  have h := D.forward_symm_arTranslation_eq_inverse sigma tau ARsigma ARtau
    ⟨(ARtau.arTranslation tau
      ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
          p).pair.1.1.1.2,
        (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
          p).target_nonprojective⟩).1, htvNP⟩
  have hsub : (⟨D.forward.labelEquiv.symm
        (ARtau.arTranslation tau
          ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
              p).pair.1.1.1.2,
            (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
              p).target_nonprojective⟩).1, by
      intro hinj
      apply htvNP
      simpa using
        ((D.forward.injective_iff_projective_image sigma tau
          (D.forward.labelEquiv.symm
            (ARtau.arTranslation tau
              ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
                  p).pair.1.1.1.2,
                (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
                  p).target_nonprojective⟩).1)).1 hinj)⟩ :
      sigma.NoninjectiveLabel) = ⟨p.pair.1.1.1.2, hI⟩ := by
    apply Subtype.ext
    show D.forward.labelEquiv.symm
        (ARtau.arTranslation tau
          ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
              p).pair.1.1.1.2,
            (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
              p).target_nonprojective⟩).1 =
      p.pair.1.1.1.2
    rw [D.firstPIOuterEquivAligned_arTranslation_commonTarget
      sigma tau ARsigma ARtau p]
    exact D.forward.labelEquiv.symm_apply_apply p.pair.1.1.1.2
  exact (Equiv.symm_apply_eq D.forward.labelEquiv).1
    (h.trans (congrArg (fun s : sigma.NoninjectiveLabel ↦
      ((ARsigma.arTranslationEquiv sigma).symm s).1) hsub))

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- Mirror form of the residual clause `a ≠ b`: the transported target
translate differs from its own translate. -/
theorem firstPIOuterEquivAligned_target_ne_last_iff
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma)
    (hI : ¬ Injective (sigma.obj p.pair.1.1.1.2))
    (htvNP : ¬ Projective (tau.obj
      (ARtau.arTranslation tau
        ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
            p).pair.1.1.1.2,
          (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
            p).target_nonprojective⟩).1)) :
    p.pair.1.1.1.2 ≠
        ((ARsigma.arTranslationEquiv sigma).symm
          ⟨p.pair.1.1.1.2, hI⟩).1 ↔
      (ARtau.arTranslation tau
          ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
              p).pair.1.1.1.2,
            (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
              p).target_nonprojective⟩).1 ≠
        (ARtau.arTranslation tau
          ⟨(ARtau.arTranslation tau
            ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
                p).pair.1.1.1.2,
              (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
                p).target_nonprojective⟩).1, htvNP⟩).1 := by
  rw [D.firstPIOuterEquivAligned_arTranslation_sq_commonTarget
      sigma tau ARsigma ARtau p hI htvNP,
    D.firstPIOuterEquivAligned_arTranslation_commonTarget
      sigma tau ARsigma ARtau p]
  exact (Equiv.injective D.forward.labelEquiv).ne_iff.symm

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- Mirror form of the residual clause `¬ b → u`. -/
theorem firstPIOuterEquivAligned_last_to_middle_iff
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma)
    (hw : ¬ Injective (sigma.obj p.pair.1.2.1.1))
    (hI : ¬ Injective (sigma.obj p.pair.1.1.1.2))
    (hwNP : ¬ Projective (tau.obj
      (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
        p).pair.1.2.1.1))
    (htvNP : ¬ Projective (tau.obj
      (ARtau.arTranslation tau
        ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
            p).pair.1.1.1.2,
          (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
            p).target_nonprojective⟩).1)) :
    HasIrreducibleMorphism
        (sigma.obj ((ARsigma.arTranslationEquiv sigma).symm
          ⟨p.pair.1.1.1.2, hI⟩).1)
        (sigma.obj ((ARsigma.arTranslationEquiv sigma).symm
          ⟨p.pair.1.2.1.1, hw⟩).1) ↔
      HasIrreducibleMorphism
        (tau.obj (ARtau.arTranslation tau
          ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
              p).pair.1.2.1.1, hwNP⟩).1)
        (tau.obj (ARtau.arTranslation tau
          ⟨(ARtau.arTranslation tau
            ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
                p).pair.1.1.1.2,
              (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
                p).target_nonprojective⟩).1, htvNP⟩).1) := by
  rw [D.firstPIOuterEquivAligned_arTranslation_second_source
      sigma tau ARsigma ARtau p hw hwNP,
    D.firstPIOuterEquivAligned_arTranslation_sq_commonTarget
      sigma tau ARsigma ARtau p hI htvNP]
  exact (D.hasIrreducibleMorphism_image_iff sigma tau).symm

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- Mirror form of the residual clause `¬ z → u`. -/
theorem firstPIOuterEquivAligned_first_to_middle_iff
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma)
    (hw : ¬ Injective (sigma.obj p.pair.1.2.1.1))
    (hwNP : ¬ Projective (tau.obj
      (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
        p).pair.1.2.1.1)) :
    HasIrreducibleMorphism
        (sigma.obj p.pair.1.1.1.1)
        (sigma.obj ((ARsigma.arTranslationEquiv sigma).symm
          ⟨p.pair.1.2.1.1, hw⟩).1) ↔
      HasIrreducibleMorphism
        (tau.obj (ARtau.arTranslation tau
          ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
              p).pair.1.2.1.1, hwNP⟩).1)
        (tau.obj (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
          p).pair.1.1.1.1) := by
  rw [D.firstPIOuterEquivAligned_arTranslation_second_source
      sigma tau ARsigma ARtau p hw hwNP,
    D.firstPIOuterEquivAligned_first_source sigma tau ARsigma ARtau p]
  exact (D.hasIrreducibleMorphism_image_iff sigma tau).symm

omit [Algebra K R] [FiniteDimensional K R]
  [Algebra K S] [FiniteDimensional K S] in
/-- Mirror form of the residual clause `¬ z → b`. -/
theorem firstPIOuterEquivAligned_first_to_last_iff
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData)
    (p : ARsigma.FirstProjectiveInjectiveDifferentOrbitOuterPair sigma)
    (hI : ¬ Injective (sigma.obj p.pair.1.1.1.2))
    (htvNP : ¬ Projective (tau.obj
      (ARtau.arTranslation tau
        ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
            p).pair.1.1.1.2,
          (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
            p).target_nonprojective⟩).1)) :
    HasIrreducibleMorphism
        (sigma.obj p.pair.1.1.1.1)
        (sigma.obj ((ARsigma.arTranslationEquiv sigma).symm
          ⟨p.pair.1.1.1.2, hI⟩).1) ↔
      HasIrreducibleMorphism
        (tau.obj (ARtau.arTranslation tau
          ⟨(ARtau.arTranslation tau
            ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
                p).pair.1.1.1.2,
              (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
                p).target_nonprojective⟩).1, htvNP⟩).1)
        (tau.obj (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
          p).pair.1.1.1.1) := by
  rw [D.firstPIOuterEquivAligned_arTranslation_sq_commonTarget
      sigma tau ARsigma ARtau p hI htvNP,
    D.firstPIOuterEquivAligned_first_source sigma tau ARsigma ARtau p]
  exact (D.hasIrreducibleMorphism_image_iff sigma tau).symm

end AlignedBiduality

/-- The mirror residual cell: intrinsic-stratum occurrences whose
forward mesh coordinates satisfy the mirrored fourth-hook-vertex
clauses. -/
abbrev MirrorResidualCell (ARtau : tau.FiniteARTranslationData) :=
  {q : ARtau.FirstPISecondNonprojectiveNoninjectiveTargetNoninjectiveOuterPair
      tau //
    ∃ htv : ¬ Projective (tau.obj
      (ARtau.arTranslation tau
        ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1),
      (ARtau.arTranslation tau
          ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1 ≠
        (ARtau.arTranslation tau
          ⟨(ARtau.arTranslation tau
            ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1, htv⟩).1 ∧
      ¬ HasIrreducibleMorphism
        (tau.obj (ARtau.arTranslation tau
          ⟨q.1.pair.1.2.1.1, q.2.1⟩).1)
        (tau.obj (ARtau.arTranslation tau
          ⟨(ARtau.arTranslation tau
            ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1, htv⟩).1) ∧
      ¬ HasIrreducibleMorphism
        (tau.obj (ARtau.arTranslation tau
          ⟨q.1.pair.1.2.1.1, q.2.1⟩).1)
        (tau.obj q.1.pair.1.1.1.1) ∧
      ¬ HasIrreducibleMorphism
        (tau.obj (ARtau.arTranslation tau
          ⟨(ARtau.arTranslation tau
            ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1, htv⟩).1)
        (tau.obj q.1.pair.1.1.1.1)}

omit [DecidableEq kappa] in
/-- Normalized form of the mirror clauses: by mesh incidence they are
the absence of the three forward arrows `z -> w`, `z -> tau t`,
`w -> tau t` together with the translate inequality. -/
theorem mirrorResidualCell_iff_normalized
    (ARtau : tau.FiniteARTranslationData)
    (q : ARtau.FirstPISecondNonprojectiveNoninjectiveTargetNoninjectiveOuterPair
      tau)
    (htv : ¬ Projective (tau.obj
      (ARtau.arTranslation tau
        ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1)) :
    ((ARtau.arTranslation tau
          ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1 ≠
        (ARtau.arTranslation tau
          ⟨(ARtau.arTranslation tau
            ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1, htv⟩).1 ∧
      ¬ HasIrreducibleMorphism
        (tau.obj (ARtau.arTranslation tau
          ⟨q.1.pair.1.2.1.1, q.2.1⟩).1)
        (tau.obj (ARtau.arTranslation tau
          ⟨(ARtau.arTranslation tau
            ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1, htv⟩).1) ∧
      ¬ HasIrreducibleMorphism
        (tau.obj (ARtau.arTranslation tau
          ⟨q.1.pair.1.2.1.1, q.2.1⟩).1)
        (tau.obj q.1.pair.1.1.1.1) ∧
      ¬ HasIrreducibleMorphism
        (tau.obj (ARtau.arTranslation tau
          ⟨(ARtau.arTranslation tau
            ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1, htv⟩).1)
        (tau.obj q.1.pair.1.1.1.1)) ↔
      (q.1.pair.1.1.1.2 ≠
          (ARtau.arTranslation tau
            ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1 ∧
        ¬ HasIrreducibleMorphism
          (tau.obj q.1.pair.1.2.1.1)
          (tau.obj (ARtau.arTranslation tau
            ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1) ∧
        ¬ HasIrreducibleMorphism
          (tau.obj q.1.pair.1.1.1.1) (tau.obj q.1.pair.1.2.1.1) ∧
        ¬ HasIrreducibleMorphism
          (tau.obj q.1.pair.1.1.1.1)
          (tau.obj (ARtau.arTranslation tau
            ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1)) := by
  have h1 : (ARtau.arTranslation tau
        ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1 =
        (ARtau.arTranslation tau
          ⟨(ARtau.arTranslation tau
            ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1, htv⟩).1 ↔
      q.1.pair.1.1.1.2 =
        (ARtau.arTranslation tau
          ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1 := by
    constructor
    · intro h
      exact congrArg (fun s : tau.NonprojectiveLabel ↦ s.1)
        (ARtau.arTranslation_injective tau (Subtype.ext h))
    · intro h
      exact congrArg (fun s : tau.NonprojectiveLabel ↦
        (ARtau.arTranslation tau s).1) (Subtype.ext h)
  have iA := ARtau.arTranslation_incidence tau
    ⟨q.1.pair.1.2.1.1, q.2.1⟩
    (ARtau.arTranslation tau
      ⟨(ARtau.arTranslation tau
        ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1, htv⟩).1
  have iB := ARtau.arTranslation_incidence tau
    ⟨(ARtau.arTranslation tau
      ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1, htv⟩
    q.1.pair.1.2.1.1
  have iC := ARtau.arTranslation_incidence tau
    ⟨q.1.pair.1.2.1.1, q.2.1⟩ q.1.pair.1.1.1.1
  have iD := ARtau.arTranslation_incidence tau
    ⟨(ARtau.arTranslation tau
      ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1, htv⟩
    q.1.pair.1.1.1.1
  exact and_congr (not_congr h1)
    (and_congr (not_congr (iA.symm.trans iB.symm))
      (and_congr (not_congr iC.symm) (not_congr iD.symm)))

namespace AlignedBiduality

/-- The aligned crossing carries the deep `M6` image exactly onto the
mirror residual cell: unit-one image identification. -/
def deepResidualEquivMirror
    (D : AlignedBiduality sigma tau)
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    {p : ARsigma.FirstPISecondInteriorNotTwoSourceOuterPair sigma //
      p.outer ∈ ARsigma.FirstPIDeepM6Image sigma} ≃
      MirrorResidualCell tau ARtau := by
  apply (D.firstPISecondInteriorNotTwoSourceEquivTargetNoninjective
    sigma tau ARsigma ARtau).subtypeEquiv
  intro p
  by_cases hI : Injective (sigma.obj p.outer.pair.1.1.1.2)
  · constructor
    · rintro ⟨M, hM⟩
      exfalso
      apply FiniteARTranslationData.hookM6InjectiveFourthToOuterPair_target_noninjective
        sigma ARsigma M.1.1
      rw [← FiniteARTranslationData.deepAnchor_outerPair_eq sigma ARsigma M,
        hM]
      exact hI
    · rintro ⟨htv, -⟩
      exact (htv
        ((D.firstPIOuterEquivAligned_translatedTarget_projective_iff_target_injective
          sigma tau ARsigma ARtau p.outer).2 hI)).elim
  · rw [FiniteARTranslationData.mem_firstPIDeepM6Image_iff (K := K) sigma
      ARsigma ⟨p.outer, p.second_noninjective, hI⟩
      p.second_nonprojective p.second_not_twoSource]
    simp only [FiniteARTranslationData.outerCellLast,
      FiniteARTranslationData.outerCellMiddle]
    have hwNP : ¬ Projective (tau.obj
        (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
          p.outer).pair.1.2.1.1) :=
      (not_congr (D.firstPIOuterEquivAligned_second_injective_iff_projective
        sigma tau ARsigma ARtau p.outer)).1 p.second_noninjective
    have htvNP : ¬ Projective (tau.obj
        (ARtau.arTranslation tau
          ⟨(D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
              p.outer).pair.1.1.1.2,
            (D.firstPIOuterEquivAligned sigma tau ARsigma ARtau
              p.outer).target_nonprojective⟩).1) :=
      (not_congr
        (D.firstPIOuterEquivAligned_translatedTarget_projective_iff_target_injective
          sigma tau ARsigma ARtau p.outer)).2 hI
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨htvNP, ?_, ?_, ?_, ?_⟩
      · exact (D.firstPIOuterEquivAligned_target_ne_last_iff
          sigma tau ARsigma ARtau p.outer hI htvNP).1 h1
      · exact (not_congr (D.firstPIOuterEquivAligned_last_to_middle_iff
          sigma tau ARsigma ARtau p.outer p.second_noninjective hI
            hwNP htvNP)).1 h2
      · exact (not_congr (D.firstPIOuterEquivAligned_first_to_middle_iff
          sigma tau ARsigma ARtau p.outer p.second_noninjective
            hwNP)).1 h3
      · exact (not_congr (D.firstPIOuterEquivAligned_first_to_last_iff
          sigma tau ARsigma ARtau p.outer hI htvNP)).1 h4
    · rintro ⟨htv, h1, h2, h3, h4⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (D.firstPIOuterEquivAligned_target_ne_last_iff
          sigma tau ARsigma ARtau p.outer hI htvNP).2 h1
      · exact (not_congr (D.firstPIOuterEquivAligned_last_to_middle_iff
          sigma tau ARsigma ARtau p.outer p.second_noninjective hI
            hwNP htvNP)).2 h2
      · exact (not_congr (D.firstPIOuterEquivAligned_first_to_middle_iff
          sigma tau ARsigma ARtau p.outer p.second_noninjective
            hwNP)).2 h3
      · exact (not_congr (D.firstPIOuterEquivAligned_first_to_last_iff
          sigma tau ARsigma ARtau p.outer hI htvNP)).2 h4

end AlignedBiduality

end OpConjecture.IndecomposableSkeleton
