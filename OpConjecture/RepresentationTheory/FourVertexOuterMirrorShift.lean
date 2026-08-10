import OpConjecture.RepresentationTheory.FourVertexOuterShortChain

/-!
# Pointwise mirror shift at a labelled cell

Vertex-level form of the manuscript's boundary-exclusion matching for
length-two chains.  For an arrow `w → t` between nonprojective,
noninjective labels with `t` not fixed by the translation:

- a return arrow `t → w` and a forward arrow `w → τt` are each
  equivalent to `τw = w` (two-cycle dichotomy one way, mesh incidence
  the other), hence equivalent to each other;
- arrows `z → w`, `w → z`, `t → z`, `z → τt` are impossible for any
  projective label `z` with an arrow `z → t` (transitive-triangle and
  projective-two-cycle exclusions).

Together these identify the deep and mirror residual clauses pointwise.
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

omit [DecidableEq ι] in
include K in
/-- A return arrow onto the source of `w → t` forces the source to be
translation-fixed, and conversely. -/
theorem hom_target_source_iff_translation_fixed
    (w t : ι)
    (hwNP : ¬ Projective (σ.obj w))
    (htNP : ¬ Projective (σ.obj t))
    (hne : t ≠ (AR.arTranslation σ ⟨t, htNP⟩).1)
    (hwt : HasIrreducibleMorphism (σ.obj w) (σ.obj t)) :
    HasIrreducibleMorphism (σ.obj t) (σ.obj w) ↔
      (AR.arTranslation σ ⟨w, hwNP⟩).1 = w := by
  constructor
  · intro h
    rcases AR.exists_arTranslation_eq_self_of_two_cycle (K := K) σ w t
        hwt h with ⟨hy, hfix⟩ | ⟨hz, hfix⟩
    · exact hfix
    · exact (hne hfix.symm).elim
  · intro hfix
    apply (AR.arTranslation_incidence σ ⟨w, hwNP⟩ t).2
    rw [hfix]
    exact hwt

omit [DecidableEq ι] in
include K in
/-- A forward arrow from the source of `w → t` to the translate of its
target also forces the source to be translation-fixed, and
conversely. -/
theorem hom_source_translate_iff_translation_fixed
    (w t : ι)
    (hwNP : ¬ Projective (σ.obj w))
    (htNP : ¬ Projective (σ.obj t))
    (hne : t ≠ (AR.arTranslation σ ⟨t, htNP⟩).1)
    (hwt : HasIrreducibleMorphism (σ.obj w) (σ.obj t)) :
    HasIrreducibleMorphism (σ.obj w)
        (σ.obj (AR.arTranslation σ ⟨t, htNP⟩).1) ↔
      (AR.arTranslation σ ⟨w, hwNP⟩).1 = w := by
  have httw : HasIrreducibleMorphism
      (σ.obj (AR.arTranslation σ ⟨t, htNP⟩).1) (σ.obj w) :=
    (AR.arTranslation_incidence σ ⟨t, htNP⟩ w).1 hwt
  constructor
  · intro h
    rcases AR.exists_arTranslation_eq_self_of_two_cycle (K := K) σ w
        (AR.arTranslation σ ⟨t, htNP⟩).1 h httw with
      ⟨hy, hfix⟩ | ⟨hz, hfix⟩
    · exact hfix
    · exfalso
      apply hne
      have hsub : (AR.arTranslation σ
          ⟨(AR.arTranslation σ ⟨t, htNP⟩).1, hz⟩) =
          AR.arTranslation σ ⟨t, htNP⟩ :=
        Subtype.ext hfix
      have := AR.arTranslation_injective σ hsub
      exact (congrArg (fun s : σ.NonprojectiveLabel ↦ s.1) this).symm
  · intro hfix
    have h := (AR.arTranslation_incidence σ ⟨w, hwNP⟩
      (AR.arTranslation σ ⟨t, htNP⟩).1).1 httw
    rw [hfix] at h
    exact h

omit [DecidableEq ι] in
include K in
/-- The pointwise mirror shift: the deep return clause and the mirror
forward clause are equivalent. -/
theorem hom_target_source_iff_hom_source_translate
    (w t : ι)
    (hwNP : ¬ Projective (σ.obj w))
    (htNP : ¬ Projective (σ.obj t))
    (hne : t ≠ (AR.arTranslation σ ⟨t, htNP⟩).1)
    (hwt : HasIrreducibleMorphism (σ.obj w) (σ.obj t)) :
    HasIrreducibleMorphism (σ.obj t) (σ.obj w) ↔
      HasIrreducibleMorphism (σ.obj w)
        (σ.obj (AR.arTranslation σ ⟨t, htNP⟩).1) :=
  (hom_target_source_iff_translation_fixed (K := K) σ AR w t hwNP htNP
      hne hwt).trans
    (hom_source_translate_iff_translation_fixed (K := K) σ AR w t hwNP
      htNP hne hwt).symm

omit [DecidableEq ι] in
include K AR in
/-- No arrow from a projective co-source of `t` to the source of
`w → t`. -/
theorem not_hom_first_source_second_source
    (z w t : ι)
    (hzt : HasIrreducibleMorphism (σ.obj z) (σ.obj t))
    (hwt : HasIrreducibleMorphism (σ.obj w) (σ.obj t)) :
    ¬ HasIrreducibleMorphism (σ.obj z) (σ.obj w) := fun h ↦
  AR.no_irreducible_transitiveTriangle (K := K) σ h hwt hzt

omit [DecidableEq ι] in
include K AR in
/-- No arrow from the source of `w → t` to a co-source of `t`. -/
theorem not_hom_second_source_first_source
    (z w t : ι)
    (hzt : HasIrreducibleMorphism (σ.obj z) (σ.obj t))
    (hwt : HasIrreducibleMorphism (σ.obj w) (σ.obj t)) :
    ¬ HasIrreducibleMorphism (σ.obj w) (σ.obj z) := fun h ↦
  AR.no_irreducible_transitiveTriangle (K := K) σ h hzt hwt

omit [Fintype ι] [DecidableEq ι] in
include K in
/-- No return arrow from an unfixed target onto its projective
co-source. -/
theorem not_hom_target_projective_source
    (z t : ι) (hzP : Projective (σ.obj z))
    (htNP : ¬ Projective (σ.obj t))
    (hne : t ≠ (AR.arTranslation σ ⟨t, htNP⟩).1)
    (hzt : HasIrreducibleMorphism (σ.obj z) (σ.obj t)) :
    ¬ HasIrreducibleMorphism (σ.obj t) (σ.obj z) := by
  intro h
  obtain ⟨ht', hfix⟩ :=
    AR.arTranslation_eq_self_of_projective_two_cycle (K := K) σ z t
      hzP hzt h
  exact hne hfix.symm

omit [Fintype ι] [DecidableEq ι] in
include K in
/-- No arrow from a projective co-source of an unfixed target to the
target's translate. -/
theorem not_hom_projective_source_translate
    (z t : ι) (hzP : Projective (σ.obj z))
    (htNP : ¬ Projective (σ.obj t))
    (hne : t ≠ (AR.arTranslation σ ⟨t, htNP⟩).1)
    (hzt : HasIrreducibleMorphism (σ.obj z) (σ.obj t)) :
    ¬ HasIrreducibleMorphism (σ.obj z)
      (σ.obj (AR.arTranslation σ ⟨t, htNP⟩).1) := by
  intro h
  have httz : HasIrreducibleMorphism
      (σ.obj (AR.arTranslation σ ⟨t, htNP⟩).1) (σ.obj z) :=
    (AR.arTranslation_incidence σ ⟨t, htNP⟩ z).1 hzt
  obtain ⟨ht', hfix⟩ :=
    AR.arTranslation_eq_self_of_projective_two_cycle (K := K) σ z
      (AR.arTranslation σ ⟨t, htNP⟩).1 hzP h httz
  apply hne
  have hsub : (AR.arTranslation σ
      ⟨(AR.arTranslation σ ⟨t, htNP⟩).1, ht'⟩) =
      AR.arTranslation σ ⟨t, htNP⟩ :=
    Subtype.ext hfix
  have := AR.arTranslation_injective σ hsub
  exact (congrArg (fun s : σ.NonprojectiveLabel ↦ s.1) this).symm

end OpConjecture.IndecomposableSkeleton.FiniteARTranslationData
