import OpConjecture.RepresentationTheory.FourVertexDualArrowOccurrences

/-!
# Corners of the full four-vertex arrow boundary

The untrimmed two-step common-target boundary splits first by the common
target.  On the source side its two strata are a projective common target
and a nonprojective common target with a projective source.  On the target
side they are an injective common target and a noninjective common target
with an injective source.  This is the subtraction-free outer-corner form
of the global square-shift identity.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton.FiniteARTranslationData

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (AR : σ.FiniteARTranslationData)

/-- Full common-target pairs whose common target is projective. -/
abbrev ProjectiveTargetCommonTargetPair :=
  {p : CommonTargetArrowPair σ //
    Projective (σ.obj p.1.1.1.2)}

/-- Full common-target pairs with nonprojective common target and at least
one projective source. -/
abbrev NonprojectiveTargetProjectiveSourcePair :=
  {p : CommonTargetArrowPair σ //
    ¬ Projective (σ.obj p.1.1.1.2) ∧
      (Projective (σ.obj p.1.1.1.1) ∨
        Projective (σ.obj p.1.2.1.1))}

/-- Full common-target pairs whose common target is injective. -/
abbrev InjectiveTargetCommonTargetPair :=
  {p : CommonTargetArrowPair σ //
    Injective (σ.obj p.1.1.1.2)}

/-- Full common-target pairs with noninjective common target and at least
one injective source. -/
abbrev NoninjectiveTargetInjectiveSourcePair :=
  {p : CommonTargetArrowPair σ //
    ¬ Injective (σ.obj p.1.1.1.2) ∧
      (Injective (σ.obj p.1.1.1.1) ∨
        Injective (σ.obj p.1.2.1.1))}

noncomputable instance projectiveTargetCommonTargetPairFintype :
    Fintype (ProjectiveTargetCommonTargetPair σ) := Fintype.ofFinite _

noncomputable instance nonprojectiveTargetProjectiveSourcePairFintype :
    Fintype (NonprojectiveTargetProjectiveSourcePair σ) :=
  Fintype.ofFinite _

noncomputable instance injectiveTargetCommonTargetPairFintype :
    Fintype (InjectiveTargetCommonTargetPair σ) := Fintype.ofFinite _

noncomputable instance noninjectiveTargetInjectiveSourcePairFintype :
    Fintype (NoninjectiveTargetInjectiveSourcePair σ) :=
  Fintype.ofFinite _

omit [DecidableEq ι] in
/-- Split the full two-step source boundary at its common target. -/
def sourceBoundaryCommonTargetEquivProjectiveTargetSumProjectiveSource :
    AR.SourceBoundaryCommonTargetArrowPair σ ≃
      ProjectiveTargetCommonTargetPair σ ⊕
        NonprojectiveTargetProjectiveSourcePair σ where
  toFun p := by
    by_cases ht : Projective (σ.obj p.1.1.1.1.2)
    · exact Sum.inl ⟨p.1, ht⟩
    · apply Sum.inr
      refine ⟨p.1, ht, ?_⟩
      rcases p.2 with h | h
      · rcases ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
          σ p.1.1.1).1 h with htarget | hsource
        · exact (ht htarget).elim
        · exact Or.inl hsource
      · rcases ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
          σ p.1.1.2).1 h with htarget | hsource
        · exfalso
          apply ht
          rw [p.1.2]
          exact htarget
        · exact Or.inr hsource
  invFun p := by
    rcases p with p | p
    · exact ⟨p.1, Or.inl <|
        ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
          σ p.1.1.1).2 (Or.inl p.2)⟩
    · by_cases h : Projective (σ.obj p.1.1.1.1.1)
      · exact ⟨p.1, Or.inl <|
          ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
            σ p.1.1.1).2 (Or.inr h)⟩
      · exact ⟨p.1, Or.inr <|
          ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
            σ p.1.1.2).2 (Or.inr (p.2.2.resolve_left h))⟩
  left_inv p := by
    apply Subtype.ext
    by_cases ht : Projective (σ.obj p.1.1.1.1.2)
    · simp [ht]
    · by_cases hs : Projective (σ.obj p.1.1.1.1.1)
      · simp [ht, hs]
      · simp [ht, hs]
  right_inv p := by
    rcases p with p | p
    · simp [p.2]
    · by_cases h : Projective (σ.obj p.1.1.1.1.1)
      · simp [p.2.1, h]
      · simp [p.2.1, h]

omit [DecidableEq ι] in
/-- Split the full two-step target boundary at its common target. -/
def targetBoundaryCommonTargetEquivInjectiveTargetSumInjectiveSource :
    AR.TargetBoundaryCommonTargetArrowPair σ ≃
      InjectiveTargetCommonTargetPair σ ⊕
        NoninjectiveTargetInjectiveSourcePair σ where
  toFun p := by
    by_cases ht : Injective (σ.obj p.1.1.1.1.2)
    · exact Sum.inl ⟨p.1, ht⟩
    · apply Sum.inr
      refine ⟨p.1, ht, ?_⟩
      rcases p.2 with h | h
      · rcases ((AR.arMeshRotationData σ).arrowOrbit_twoTarget_iff
          σ p.1.1.1).1 h with hsource | htarget
        · exact Or.inl hsource
        · exact (ht htarget).elim
      · rcases ((AR.arMeshRotationData σ).arrowOrbit_twoTarget_iff
          σ p.1.1.2).1 h with hsource | htarget
        · exact Or.inr hsource
        · exfalso
          apply ht
          rw [p.1.2]
          exact htarget
  invFun p := by
    rcases p with p | p
    · exact ⟨p.1, Or.inl <|
        ((AR.arMeshRotationData σ).arrowOrbit_twoTarget_iff
          σ p.1.1.1).2 (Or.inr p.2)⟩
    · by_cases h : Injective (σ.obj p.1.1.1.1.1)
      · exact ⟨p.1, Or.inl <|
          ((AR.arMeshRotationData σ).arrowOrbit_twoTarget_iff
            σ p.1.1.1).2 (Or.inl h)⟩
      · exact ⟨p.1, Or.inr <|
          ((AR.arMeshRotationData σ).arrowOrbit_twoTarget_iff
            σ p.1.1.2).2 (Or.inl (p.2.2.resolve_left h))⟩
  left_inv p := by
    apply Subtype.ext
    by_cases ht : Injective (σ.obj p.1.1.1.1.2)
    · simp [ht]
    · by_cases hs : Injective (σ.obj p.1.1.1.1.1)
      · simp [ht, hs]
      · simp [ht, hs]
  right_inv p := by
    rcases p with p | p
    · simp [p.2]
    · by_cases h : Injective (σ.obj p.1.1.1.1.1)
      · simp [p.2.1, h]
      · simp [p.2.1, h]

/-- Elementwise corner form of full global square-shift conservation.  In
contrast to the cardinal identity below, this equivalence retains the
ordered arrow occurrences and therefore the orientation of endpoint
crossings. -/
def fullCommonTargetBoundaryCornerEquiv :
    ProjectiveTargetCommonTargetPair σ ⊕
        NonprojectiveTargetProjectiveSourcePair σ ≃
      InjectiveTargetCommonTargetPair σ ⊕
        NoninjectiveTargetInjectiveSourcePair σ :=
  (sourceBoundaryCommonTargetEquivProjectiveTargetSumProjectiveSource
      σ AR).symm |>.trans <|
    (AR.commonTargetBoundaryEquiv σ).trans
      (targetBoundaryCommonTargetEquivInjectiveTargetSumInjectiveSource
        σ AR)

/-- Subtraction-free corner form of full global square-shift conservation. -/
theorem fullCommonTargetBoundary_corner_card_identity
    (AR : σ.FiniteARTranslationData) :
    Fintype.card (ProjectiveTargetCommonTargetPair σ) +
        Fintype.card (NonprojectiveTargetProjectiveSourcePair σ) =
      Fintype.card (InjectiveTargetCommonTargetPair σ) +
        Fintype.card (NoninjectiveTargetInjectiveSourcePair σ) := by
  rw [← Fintype.card_sum,
    ← Fintype.card_congr
      (sourceBoundaryCommonTargetEquivProjectiveTargetSumProjectiveSource
        σ AR),
    AR.sourceBoundaryCommonTarget_card_eq_targetBoundary σ,
    Fintype.card_congr
      (targetBoundaryCommonTargetEquivInjectiveTargetSumInjectiveSource
        σ AR),
    Fintype.card_sum]

end OpConjecture.IndecomposableSkeleton.FiniteARTranslationData
