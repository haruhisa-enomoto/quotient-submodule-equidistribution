import OpConjecture.RepresentationTheory.FourVertexOuterWallReversal

/-!
# Status form of the reverse-last correction family

The reverse arrow from the reconstructed last label to the reconstructed
middle closes a two-cycle against the automatic strip arrow, so the
two-cycle dichotomy applies.  The target-fixed branch is impossible: the
first occurrence starts at a projective, noninjective label
(`InteriorSource` plus interiority), and a translation-fixed common
target would close a two-cycle at that label, making it injective.  This
is the manuscript's own exclusion argument (`four-ladders.tex`, the
`b -> u` analysis in the boundary identification) transposed to these
coordinates.  Hence a reverse-last pair is exactly a first-source
boundary pair with noninjective target whose reconstructed middle equals
the second source — one pure status clause with no arrow condition.
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
/-- The reverse-last arrow of a first-source boundary pair exists exactly
when the reconstructed middle is the second source itself. -/
theorem boundaryM6_last_to_middle_iff_middle_eq_second_source
    (p : AR.InteriorCommonTargetArrowPair σ)
    (hfs : ((AR.arMeshRotationData σ).arrowOrbitData σ).InteriorSource
      p.1.1)
    (htNI : ¬ Injective (σ.obj p.1.2.1.1.2)) :
    HasIrreducibleMorphism
        (σ.obj (AR.boundaryM6Last σ p htNI))
        (σ.obj (AR.boundaryM6FirstArrow σ p).1.2) ↔
      (AR.boundaryM6FirstArrow σ p).1.2 = p.1.2.1.1.1 := by
  have hfa : (AR.boundaryM6FirstArrow σ p).1 =
      (p.1.2.1.1.2,
        ((AR.arTranslationEquiv σ).symm
          ⟨p.1.2.1.1.1, p.1.2.2.2⟩).1) :=
    ARMeshRotationData.arrowOrbitData_tau_symm_val σ
      (AR.arMeshRotationData σ) ⟨p.1.2.1, p.1.2.2.2⟩
  have hfa1 : (AR.boundaryM6FirstArrow σ p).1.1 = p.1.2.1.1.2 :=
    congrArg Prod.fst hfa
  have hfa2 : (AR.boundaryM6FirstArrow σ p).1.2 =
      ((AR.arTranslationEquiv σ).symm ⟨p.1.2.1.1.1, p.1.2.2.2⟩).1 :=
    congrArg Prod.snd hfa
  have htaub : (AR.arTranslation σ
      ((AR.arTranslationEquiv σ).symm ⟨p.1.2.1.1.2, htNI⟩)).1 =
      p.1.2.1.1.2 :=
    congrArg Subtype.val
      ((AR.arTranslationEquiv σ).apply_symm_apply
        ⟨p.1.2.1.1.2, htNI⟩)
  have htm : HasIrreducibleMorphism
      (σ.obj p.1.2.1.1.2)
      (σ.obj ((AR.arTranslationEquiv σ).symm
        ⟨p.1.2.1.1.1, p.1.2.2.2⟩).1) := by
    have h := (AR.boundaryM6FirstArrow σ p).2
    rw [hfa1, hfa2] at h
    exact h
  have hmb : HasIrreducibleMorphism
      (σ.obj ((AR.arTranslationEquiv σ).symm
        ⟨p.1.2.1.1.1, p.1.2.2.2⟩).1)
      (σ.obj ((AR.arTranslationEquiv σ).symm
        ⟨p.1.2.1.1.2, htNI⟩).1) := by
    apply (AR.arTranslation_incidence σ
      ((AR.arTranslationEquiv σ).symm ⟨p.1.2.1.1.2, htNI⟩)
      ((AR.arTranslationEquiv σ).symm
        ⟨p.1.2.1.1.1, p.1.2.2.2⟩).1).2
    rw [htaub]
    exact htm
  constructor
  · intro h
    rw [hfa2] at h ⊢
    rcases AR.exists_arTranslation_eq_self_of_two_cycle (K := K) σ
        ((AR.arTranslationEquiv σ).symm
          ⟨p.1.2.1.1.1, p.1.2.2.2⟩).1
        ((AR.arTranslationEquiv σ).symm ⟨p.1.2.1.1.2, htNI⟩).1
        hmb h with ⟨hm, hfix⟩ | ⟨hb, hfix⟩
    · have hsub : (⟨((AR.arTranslationEquiv σ).symm
          ⟨p.1.2.1.1.1, p.1.2.2.2⟩).1, hm⟩ : σ.NonprojectiveLabel) =
          (AR.arTranslationEquiv σ).symm
            ⟨p.1.2.1.1.1, p.1.2.2.2⟩ := Subtype.ext rfl
      have hval := congrArg
        (fun s : σ.NonprojectiveLabel ↦ (AR.arTranslation σ s).1) hsub
      rw [hfix] at hval
      exact hval.trans
        (congrArg Subtype.val
          ((AR.arTranslationEquiv σ).apply_symm_apply
            ⟨p.1.2.1.1.1, p.1.2.2.2⟩))
    · exfalso
      have hsub : (⟨((AR.arTranslationEquiv σ).symm
          ⟨p.1.2.1.1.2, htNI⟩).1, hb⟩ : σ.NonprojectiveLabel) =
          (AR.arTranslationEquiv σ).symm ⟨p.1.2.1.1.2, htNI⟩ :=
        Subtype.ext rfl
      have htb : p.1.2.1.1.2 =
          ((AR.arTranslationEquiv σ).symm ⟨p.1.2.1.1.2, htNI⟩).1 :=
        htaub.symm.trans
          ((congrArg (fun s : σ.NonprojectiveLabel ↦
            (AR.arTranslation σ s).1) hsub).symm.trans hfix)
      have htfix : (AR.arTranslation σ
          ⟨p.1.2.1.1.2, p.1.2.2.1⟩).1 = p.1.2.1.1.2 := by
        have hsub2 : (⟨p.1.2.1.1.2, p.1.2.2.1⟩ :
            σ.NonprojectiveLabel) =
            (AR.arTranslationEquiv σ).symm ⟨p.1.2.1.1.2, htNI⟩ :=
          Subtype.ext htb
        rw [hsub2]
        exact htaub
      have hzP : Projective (σ.obj p.1.1.1.1.1) :=
        ((AR.arMeshRotationData σ).arrowInterior_source_iff σ
          p.1.1).1 hfs
      have hzt : HasIrreducibleMorphism
          (σ.obj p.1.1.1.1.1) (σ.obj p.1.2.1.1.2) := by
        have h0 := p.1.1.1.2
        rw [p.2] at h0
        exact h0
      have htz : HasIrreducibleMorphism
          (σ.obj p.1.2.1.1.2) (σ.obj p.1.1.1.1.1) := by
        have h1 := (AR.arTranslation_incidence σ
          ⟨p.1.2.1.1.2, p.1.2.2.1⟩ p.1.1.1.1.1).1 hzt
        rw [htfix] at h1
        exact h1
      exact p.1.1.2.2
        (AR.injective_of_projective_two_cycle (K := K) σ
          p.1.1.1.1.1 p.1.2.1.1.2 hzP hzt htz)
  · intro hfix
    have hfix' : ((AR.arTranslationEquiv σ).symm
        ⟨p.1.2.1.1.1, p.1.2.2.2⟩).1 = p.1.2.1.1.1 :=
      hfa2.symm.trans hfix
    have htmfix : (AR.arTranslation σ
        ((AR.arTranslationEquiv σ).symm
          ⟨p.1.2.1.1.1, p.1.2.2.2⟩)).1 =
        ((AR.arTranslationEquiv σ).symm
          ⟨p.1.2.1.1.1, p.1.2.2.2⟩).1 :=
      (congrArg Subtype.val
        ((AR.arTranslationEquiv σ).apply_symm_apply
          ⟨p.1.2.1.1.1, p.1.2.2.2⟩)).trans hfix'.symm
    rw [hfa2]
    apply (AR.arTranslation_incidence σ
      ((AR.arTranslationEquiv σ).symm ⟨p.1.2.1.1.1, p.1.2.2.2⟩)
      (AR.boundaryM6Last σ p htNI)).2
    rw [htmfix]
    exact hmb

/-- Reverse-last boundary pairs in pure status form: first-source
boundary pairs with noninjective target whose reconstructed middle is
the second source. -/
abbrev FixedMiddleBoundaryPair :=
  {p : AR.InteriorCommonTargetArrowPair σ //
    ((AR.arMeshRotationData σ).arrowOrbitData σ).InteriorSource
        p.1.1 ∧
      ¬ Injective (σ.obj p.1.2.1.1.2) ∧
      (AR.boundaryM6FirstArrow σ p).1.2 = p.1.2.1.1.1}

noncomputable instance fixedMiddleBoundaryPairFintype :
    Fintype (AR.FixedMiddleBoundaryPair σ) :=
  Fintype.ofFinite _

/-- The reverse-last correction family is exactly its status form. -/
def boundaryM6ReverseLastPairEquivFixedMiddle :
    AR.BoundaryM6ReverseLastPair σ ≃ AR.FixedMiddleBoundaryPair σ where
  toFun q :=
    ⟨q.pair, q.first_source, q.target_noninjective,
      (boundaryM6_last_to_middle_iff_middle_eq_second_source (K := K)
        σ AR q.pair q.first_source q.target_noninjective).1
        q.last_to_middle⟩
  invFun p :=
    { pair := p.1
      first_source := p.2.1
      target_noninjective := p.2.2.1
      last_to_middle :=
        (boundaryM6_last_to_middle_iff_middle_eq_second_source (K := K)
          σ AR p.1 p.2.1 p.2.2.1).2 p.2.2.2 }
  left_inv _ := BoundaryM6ReverseLastPair.ext σ AR rfl
  right_inv _ := Subtype.ext rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The neighborhood of a translation-fixed label is symmetric. -/
theorem fixed_hom_comm
    (u v : ι) (huNP : ¬ Projective (σ.obj u))
    (hfix : (AR.arTranslation σ ⟨u, huNP⟩).1 = u) :
    HasIrreducibleMorphism (σ.obj v) (σ.obj u) ↔
      HasIrreducibleMorphism (σ.obj u) (σ.obj v) := by
  have h := AR.arTranslation_incidence σ ⟨u, huNP⟩ v
  rw [hfix] at h
  exact h

omit [DecidableEq ι] in
/-- Attachment to a translation-fixed label descends along the inverse
translation of the neighbor. -/
theorem fixed_hom_shift
    (u c : ι) (huNP : ¬ Projective (σ.obj u))
    (hfix : (AR.arTranslation σ ⟨u, huNP⟩).1 = u)
    (hcNI : ¬ Injective (σ.obj c)) :
    HasIrreducibleMorphism (σ.obj u)
        (σ.obj ((AR.arTranslationEquiv σ).symm ⟨c, hcNI⟩).1) ↔
      HasIrreducibleMorphism (σ.obj u) (σ.obj c) := by
  have hshift : (AR.arTranslation σ
      ((AR.arTranslationEquiv σ).symm ⟨c, hcNI⟩)).1 = c :=
    congrArg Subtype.val
      ((AR.arTranslationEquiv σ).apply_symm_apply ⟨c, hcNI⟩)
  have hinc := AR.arTranslation_incidence σ
    ((AR.arTranslationEquiv σ).symm ⟨c, hcNI⟩) u
  rw [hshift] at hinc
  exact hinc.trans (fixed_hom_comm σ AR u c huNP hfix)

end OpConjecture.IndecomposableSkeleton.FiniteARTranslationData
