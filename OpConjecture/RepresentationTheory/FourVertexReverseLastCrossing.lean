import OpConjecture.RepresentationTheory.FourVertexReverseLastFanDecomposition
import OpConjecture.RepresentationTheory.FourVertexDualArrowOccurrences

/-!
# Crossing the fixed-hub fans

Aligned duality reverses irreducible arrows and exchanges the two
boundary statuses, so it exchanges translation-fixed hubs of the two
skeletons and carries the strict-source fan of a dual hub to the
strict-target fan of the corresponding source hub: attachment crosses
because the reversed arrow at a fixed hub can be re-oriented by the
fixed-fan symmetry.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {R S : Type u}
  [Ring R] [IsNoetherianRing R]
  [Ring S] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace AlignedBiduality

variable (D : AlignedBiduality σ τ)
  (ARσ : σ.FiniteARTranslationData)
  (ARτ : τ.FiniteARTranslationData)

omit [Fintype ι] [Fintype κ] in
/-- A dual translation-fixed hub pulls back to a noninjective label. -/
theorem pullback_fixedHub_noninjective
    (t : ARτ.FixedHubLabel τ) :
    ¬ Injective (σ.obj (D.forward.labelEquiv.symm t.1.1)) := by
  intro hinj
  apply t.1.2
  simpa using
    (D.forward.injective_iff_projective_image σ τ
      (D.forward.labelEquiv.symm t.1.1)).1 hinj

omit [Fintype κ] in
/-- A dual translation-fixed hub pulls back to a fixed point of the
inverse source translation. -/
theorem pullback_fixedHub_symm_fixed
    (t : ARτ.FixedHubLabel τ) :
    ((ARσ.arTranslationEquiv σ).symm
        ⟨D.forward.labelEquiv.symm t.1.1,
          D.pullback_fixedHub_noninjective σ τ ARτ t⟩).1 =
      D.forward.labelEquiv.symm t.1.1 := by
  have hd := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ t.1
  rw [t.2] at hd
  exact hd.symm

omit [Fintype ι] [Fintype κ] in
/-- A source translation-fixed hub pushes forward to a nonprojective
label. -/
theorem pushforward_fixedHub_nonprojective
    (s : ARσ.FixedHubLabel σ) :
    ¬ Projective (τ.obj (D.forward.labelEquiv s.1.1)) := by
  intro hproj
  apply ARσ.fixedHub_noninjective σ s
  have h := (D.forward.injective_iff_projective_image σ τ s.1.1).2
  exact h hproj

omit [Fintype κ] in
/-- A source translation-fixed hub pushes forward to a translation-fixed
hub of the dual skeleton. -/
theorem pushforward_fixedHub_fixed
    (s : ARσ.FixedHubLabel σ) :
    (ARτ.arTranslation τ
        ⟨D.forward.labelEquiv s.1.1,
          D.pushforward_fixedHub_nonprojective σ τ ARσ s⟩).1 =
      D.forward.labelEquiv s.1.1 := by
  have hd := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
    ⟨D.forward.labelEquiv s.1.1,
      D.pushforward_fixedHub_nonprojective σ τ ARσ s⟩
  have hNI : ¬ Injective (σ.obj s.1.1) :=
    ARσ.fixedHub_noninjective σ s
  have hsub : (⟨D.forward.labelEquiv.symm
      (D.forward.labelEquiv s.1.1), by
        intro hinj
        apply (D.pushforward_fixedHub_nonprojective σ τ ARσ s)
        simpa using
          (D.forward.injective_iff_projective_image σ τ
            (D.forward.labelEquiv.symm
              (D.forward.labelEquiv s.1.1))).1 hinj⟩ :
      σ.NoninjectiveLabel) = ⟨s.1.1, hNI⟩ :=
    Subtype.ext (D.forward.labelEquiv.symm_apply_apply s.1.1)
  rw [hsub, ARσ.fixedHub_symm_val σ s hNI] at hd
  have hle := congrArg D.forward.labelEquiv hd
  simpa using hle

/-- Aligned duality exchanges the translation-fixed hubs of the two
skeletons. -/
def fixedHubLabelEquiv :
    ARτ.FixedHubLabel τ ≃ ARσ.FixedHubLabel σ where
  toFun t :=
    ARσ.fixedHubOfSymmFixed σ (D.forward.labelEquiv.symm t.1.1)
      (D.pullback_fixedHub_noninjective σ τ ARτ t)
      (D.pullback_fixedHub_symm_fixed σ τ ARσ ARτ t)
  invFun s :=
    ⟨⟨D.forward.labelEquiv s.1.1,
      D.pushforward_fixedHub_nonprojective σ τ ARσ s⟩,
      D.pushforward_fixedHub_fixed σ τ ARσ ARτ s⟩
  left_inv t := Subtype.ext (Subtype.ext
    (D.forward.labelEquiv.apply_symm_apply t.1.1))
  right_inv s := Subtype.ext (Subtype.ext
    (D.forward.labelEquiv.symm_apply_apply s.1.1))

/-- Crossing a fixed hub's strict-source fan cell: the pulled-back
occurrences form the strict-target fan cell of the pulled-back hub. -/
def reverseLastCellCrossEquiv (t : ARτ.FixedHubLabel τ) :
    {y : (ARτ.arMeshRotationData τ).InteriorArrow τ //
      ((ARτ.arMeshRotationData τ).arrowOrbitData τ).InteriorSource
          y ∧
        ¬ ((ARτ.arMeshRotationData τ).arrowOrbitData τ).InteriorTarget
          y ∧
        ARτ.FanAttached τ t.1.1 y} ≃
    {x : (ARσ.arMeshRotationData σ).InteriorArrow σ //
      ((ARσ.arMeshRotationData σ).arrowOrbitData σ).InteriorTarget
          x ∧
        ¬ ((ARσ.arMeshRotationData σ).arrowOrbitData σ).InteriorSource
          x ∧
        ARσ.FanAttached σ (D.forward.labelEquiv.symm t.1.1) x} :=
  (D.interiorArrowEquiv σ τ ARσ ARτ).subtypeEquiv (fun y ↦ by
    apply and_congr (D.pullbackInterior_source_iff_target σ τ ARσ ARτ y)
    apply and_congr
      (not_congr (D.pullbackInterior_target_iff_source σ τ ARσ ARτ y))
    simp only [FiniteARTranslationData.FanAttached, interiorArrowEquiv,
      Equiv.coe_fn_mk, pullbackInteriorArrow, pullbackIrreduciblePair]
    rw [← D.hasIrreducibleMorphism_image_iff σ τ
        (x := D.forward.labelEquiv.symm t.1.1)
        (y := D.forward.labelEquiv.symm y.1.1.2),
      ← D.hasIrreducibleMorphism_image_iff σ τ
        (x := D.forward.labelEquiv.symm t.1.1)
        (y := D.forward.labelEquiv.symm y.1.1.1)]
    simp only [Equiv.apply_symm_apply]
    rw [ARτ.fixed_hom_comm τ t.1.1 y.1.1.2 t.1.2 t.2,
      ARτ.fixed_hom_comm τ t.1.1 y.1.1.1 t.1.2 t.2]
    exact or_comm)

/-- Crossing the whole fan sum: dual strict-source fans over dual fixed
hubs match source strict-target fans over source fixed hubs. -/
def reverseLastSigmaCrossEquiv :
    ((t : ARτ.FixedHubLabel τ) ×
      {y : (ARτ.arMeshRotationData τ).InteriorArrow τ //
        ((ARτ.arMeshRotationData τ).arrowOrbitData τ).InteriorSource
            y ∧
          ¬ ((ARτ.arMeshRotationData τ).arrowOrbitData
            τ).InteriorTarget y ∧
          ARτ.FanAttached τ t.1.1 y}) ≃
    ((s : ARσ.FixedHubLabel σ) ×
      {x : (ARσ.arMeshRotationData σ).InteriorArrow σ //
        ((ARσ.arMeshRotationData σ).arrowOrbitData σ).InteriorTarget
            x ∧
          ¬ ((ARσ.arMeshRotationData σ).arrowOrbitData
            σ).InteriorSource x ∧
          ARσ.FanAttached σ s.1.1 x}) :=
  Equiv.sigmaCongr (D.fixedHubLabelEquiv σ τ ARσ ARτ)
    (fun t ↦ D.reverseLastCellCrossEquiv σ τ ARσ ARτ t)

end AlignedBiduality

end OpConjecture.IndecomposableSkeleton
