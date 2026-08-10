import OpConjecture.RepresentationTheory.FourVertexReverseLastFan

/-!
# Fan decomposition of the fixed-middle family

A fixed-middle boundary pair consists of a first interior arrow at the
shifted source boundary and a second interior arrow into the same
noninjective target whose source is a translation-fixed label.  The
second arrow is determined by its endpoints, so the family decomposes as
a dependent sum over translation-fixed hub labels of the strict-source
fan cells in collapsed target-attachment form.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton.FiniteARTranslationData

universe u v

variable {K R : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (AR : σ.FiniteARTranslationData)

/-- Translation-fixed hub labels. -/
abbrev FixedHubLabel :=
  {s : σ.NonprojectiveLabel // (AR.arTranslation σ s).1 = s.1}

/-- The strict-source fan cell at a hub, in collapsed target-attachment
form. -/
abbrev FanTargetAttachedSourceCell (u : ι) :=
  {x : (AR.arMeshRotationData σ).InteriorArrow σ //
    ((AR.arMeshRotationData σ).arrowOrbitData σ).InteriorSource x ∧
      ¬ ((AR.arMeshRotationData σ).arrowOrbitData σ).InteriorTarget
        x ∧
      HasIrreducibleMorphism (σ.obj u) (σ.obj x.1.1.2)}

omit [DecidableEq ι] in
/-- On a translation-fixed hub the inverse translation is also fixed. -/
theorem fixedHub_symm_val (s : AR.FixedHubLabel σ)
    (hNI : ¬ Injective (σ.obj s.1.1)) :
    ((AR.arTranslationEquiv σ).symm ⟨s.1.1, hNI⟩).1 = s.1.1 := by
  have hsub : (⟨s.1.1, hNI⟩ : σ.NoninjectiveLabel) =
      (AR.arTranslationEquiv σ) s.1 := Subtype.ext s.2.symm
  rw [hsub]
  exact congrArg Subtype.val
    ((AR.arTranslationEquiv σ).symm_apply_apply s.1)

omit [Fintype ι] [DecidableEq ι] in
/-- A translation-fixed hub is noninjective. -/
theorem fixedHub_noninjective (s : AR.FixedHubLabel σ) :
    ¬ Injective (σ.obj s.1.1) := by
  rw [← s.2]
  exact (AR.arTranslation σ s.1).2

omit [DecidableEq ι] in
/-- The reconstructed middle of an interior common-target pair is the
inverse translate of the second source. -/
theorem boundaryM6FirstArrow_snd
    (p : AR.InteriorCommonTargetArrowPair σ) :
    (AR.boundaryM6FirstArrow σ p).1.2 =
      ((AR.arTranslationEquiv σ).symm ⟨p.1.2.1.1.1, p.1.2.2.2⟩).1 :=
  congrArg Prod.snd
    (ARMeshRotationData.arrowOrbitData_tau_symm_val σ
      (AR.arMeshRotationData σ) ⟨p.1.2.1, p.1.2.2.2⟩)

/-- Build a fixed hub from a fixed point of the inverse translation. -/
def fixedHubOfSymmFixed (x : ι) (hNI : ¬ Injective (σ.obj x))
    (h : ((AR.arTranslationEquiv σ).symm ⟨x, hNI⟩).1 = x) :
    AR.FixedHubLabel σ :=
  ⟨⟨x, h ▸ ((AR.arTranslationEquiv σ).symm ⟨x, hNI⟩).2⟩, by
    have hsub : (⟨x, h ▸ ((AR.arTranslationEquiv σ).symm
        ⟨x, hNI⟩).2⟩ : σ.NonprojectiveLabel) =
        (AR.arTranslationEquiv σ).symm ⟨x, hNI⟩ := Subtype.ext h.symm
    have happ : (AR.arTranslation σ
        ((AR.arTranslationEquiv σ).symm ⟨x, hNI⟩)).1 = x :=
      congrArg Subtype.val
        ((AR.arTranslationEquiv σ).apply_symm_apply ⟨x, hNI⟩)
    rw [hsub, happ, h]⟩

/-- The fixed-middle family decomposes as a dependent sum over
translation-fixed hubs of the collapsed strict-source fan cells. -/
def fixedMiddleEquivSigmaFan :
    AR.FixedMiddleBoundaryPair σ ≃
      (s : AR.FixedHubLabel σ) ×
        AR.FanTargetAttachedSourceCell σ s.1.1 where
  toFun q :=
    have hinvfix : ((AR.arTranslationEquiv σ).symm
        ⟨q.1.1.2.1.1.1, q.1.1.2.2.2⟩).1 = q.1.1.2.1.1.1 :=
      (boundaryM6FirstArrow_snd σ AR q.1).symm.trans q.2.2.2
    have hNP : ¬ Projective (σ.obj q.1.1.2.1.1.1) :=
      hinvfix ▸ ((AR.arTranslationEquiv σ).symm
        ⟨q.1.1.2.1.1.1, q.1.1.2.2.2⟩).2
    have hfwd : (AR.arTranslation σ ⟨q.1.1.2.1.1.1, hNP⟩).1 =
        q.1.1.2.1.1.1 := by
      have hsub : (⟨q.1.1.2.1.1.1, hNP⟩ : σ.NonprojectiveLabel) =
          (AR.arTranslationEquiv σ).symm
            ⟨q.1.1.2.1.1.1, q.1.1.2.2.2⟩ :=
        Subtype.ext hinvfix.symm
      rw [hsub]
      exact congrArg Subtype.val
        ((AR.arTranslationEquiv σ).apply_symm_apply
          ⟨q.1.1.2.1.1.1, q.1.1.2.2.2⟩)
    have hnI : ¬ ((AR.arMeshRotationData σ).arrowOrbitData
        σ).InteriorTarget q.1.1.1 := fun h ↦
      q.2.2.1 (q.1.2 ▸
        (((AR.arMeshRotationData σ).arrowInterior_target_iff σ
          q.1.1.1).1 h))
    have hhom : HasIrreducibleMorphism
        (σ.obj q.1.1.2.1.1.1) (σ.obj q.1.1.1.1.1.2) := by
      have h := q.1.1.2.1.2
      rw [← q.1.2] at h
      exact h
    ⟨⟨⟨q.1.1.2.1.1.1, hNP⟩, hfwd⟩, q.1.1.1, q.2.1, hnI, hhom⟩
  invFun sx :=
    ⟨⟨(sx.2.1,
      ⟨⟨(sx.1.1.1, sx.2.1.1.1.2), sx.2.2.2.2⟩,
        sx.2.1.2.1, fixedHub_noninjective σ AR sx.1⟩), rfl⟩,
      sx.2.2.1,
      (fun h ↦ sx.2.2.2.1
        (((AR.arMeshRotationData σ).arrowInterior_target_iff σ
          sx.2.1).2 h)),
      (boundaryM6FirstArrow_snd σ AR _).trans
        (fixedHub_symm_val σ AR sx.1
          (fixedHub_noninjective σ AR sx.1))⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact q.1.2
  right_inv sx := rfl

end OpConjecture.IndecomposableSkeleton.FiniteARTranslationData
