import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexOuterMirrorShift
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexOuterMirrorReduction

/-!
# Same-side packaging of the mirror residual cell

On a single skeleton, the deep `M6` image clauses and the mirror
residual clauses both reduce — pointwise on the common refined cell —
to the two translate conditions `t ≠ τt` and `τw ≠ w`: the shift
`t → w ⟺ τw = w ⟺ w → τt` converts the one nonautomatic clause,
and the remaining clauses are excluded by transitive-triangle and
projective-two-cycle arguments.  Hence the mirror residual cell is
equivalent to the deep-image subtype of its own skeleton, the
deep-anchor family has reversal-invariant cardinality, and the
remaining crossed obligation shrinks to the wall and reverse-last
terms.
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
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

omit [Field K] [Algebra K R] [FiniteDimensional K R] in
/-- The common target of a deep outer `M6` occurrence is noninjective. -/
theorem target_noninjective_of_mem_firstPIDeepM6Image
    {p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair σ}
    (hp : p ∈ AR.FirstPIDeepM6Image σ) :
    ¬ Injective (σ.obj p.pair.1.1.1.2) := by
  obtain ⟨M, rfl⟩ := hp
  rw [deepAnchor_outerPair_eq σ AR M]
  exact hookM6InjectiveFourthToOuterPair_target_noninjective σ AR M.1.1

include K in
/-- Normalized membership in the deep `M6` image: for a cell element
with nonprojective, deep second arrow, membership is the translate
inequality together with absence of the three return arrows. -/
theorem mem_firstPIDeepM6Image_iff_normalized
    (q : AR.SecondNoninjectiveTargetNoninjectiveOuterPair σ)
    (hP : ¬ Projective (σ.obj q.1.pair.1.2.1.1))
    (hTS : ¬ ((AR.arMeshRotationData σ).arrowInteriorOrbitData
        σ).TwoSource
      (toInteriorArrow σ AR q.1.pair.1.2
        ⟨by
          rw [← q.1.pair.2]
          exact q.1.target_nonprojective,
        q.2.1⟩)) :
    q.1 ∈ AR.FirstPIDeepM6Image σ ↔
      (q.1.pair.1.1.1.2 ≠ outerCellLast σ AR q ∧
        ¬ HasIrreducibleMorphism
          (σ.obj q.1.pair.1.1.1.2) (σ.obj q.1.pair.1.2.1.1) ∧
        ¬ HasIrreducibleMorphism
          (σ.obj q.1.pair.1.2.1.1) (σ.obj q.1.pair.1.1.1.1) ∧
        ¬ HasIrreducibleMorphism
          (σ.obj q.1.pair.1.1.1.2) (σ.obj q.1.pair.1.1.1.1)) :=
  (mem_firstPIDeepM6Image_iff (K := K) σ AR q hP hTS).trans
    ((mem_range_hookM6InjectiveFourthToTargetNoninjectiveCell_iff
      (K := K) σ AR q).symm.trans
      (mem_range_hookM6InjectiveFourthToTargetNoninjectiveCell_iff_normalized
        (K := K) σ AR q))

omit [DecidableEq ι] in
/-- The reconstructed-last inequality of a cell element is the forward
translate inequality of its common target. -/
theorem target_ne_outerCellLast_iff
    (q : AR.SecondNoninjectiveTargetNoninjectiveOuterPair σ) :
    q.1.pair.1.1.1.2 ≠ outerCellLast σ AR q ↔
      q.1.pair.1.1.1.2 ≠
        (AR.arTranslation σ
          ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1 := by
  apply not_congr
  constructor
  · intro h
    have hsub : (⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩ :
        σ.NonprojectiveLabel) =
        (AR.arTranslationEquiv σ).symm ⟨q.1.pair.1.1.1.2, q.2.2⟩ :=
      Subtype.ext h
    rw [hsub]
    exact (congrArg Subtype.val
      ((AR.arTranslationEquiv σ).apply_symm_apply
        ⟨q.1.pair.1.1.1.2, q.2.2⟩)).symm
  · intro h
    have hsub : (AR.arTranslationEquiv σ)
        ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩ =
        ⟨q.1.pair.1.1.1.2, q.2.2⟩ :=
      Subtype.ext h.symm
    have hval := congrArg (fun s : σ.NoninjectiveLabel ↦
      ((AR.arTranslationEquiv σ).symm s).1) hsub
    simp only [Equiv.symm_apply_apply] at hval
    exact hval

omit [DecidableEq ι] in
include K in
/-- On the refined cell the normalized deep clauses reduce to the two
translate inequalities: the return arrow `t → w` is the fixedness of
`w`, and the arrows into the projective first source are excluded. -/
theorem deepClauses_iff_reduced
    (q : AR.SecondNoninjectiveTargetNoninjectiveOuterPair σ)
    (hP : ¬ Projective (σ.obj q.1.pair.1.2.1.1)) :
    (q.1.pair.1.1.1.2 ≠ outerCellLast σ AR q ∧
        ¬ HasIrreducibleMorphism
          (σ.obj q.1.pair.1.1.1.2) (σ.obj q.1.pair.1.2.1.1) ∧
        ¬ HasIrreducibleMorphism
          (σ.obj q.1.pair.1.2.1.1) (σ.obj q.1.pair.1.1.1.1) ∧
        ¬ HasIrreducibleMorphism
          (σ.obj q.1.pair.1.1.1.2) (σ.obj q.1.pair.1.1.1.1)) ↔
      (q.1.pair.1.1.1.2 ≠
          (AR.arTranslation σ
            ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1 ∧
        (AR.arTranslation σ ⟨q.1.pair.1.2.1.1, hP⟩).1 ≠
          q.1.pair.1.2.1.1) := by
  have hzt : HasIrreducibleMorphism
      (σ.obj q.1.pair.1.1.1.1) (σ.obj q.1.pair.1.1.1.2) :=
    q.1.pair.1.1.2
  have hwt : HasIrreducibleMorphism
      (σ.obj q.1.pair.1.2.1.1) (σ.obj q.1.pair.1.1.1.2) := by
    have h := q.1.pair.1.2.2
    rw [← q.1.pair.2] at h
    exact h
  constructor
  · rintro ⟨h1, h2, -, -⟩
    have hne := (target_ne_outerCellLast_iff σ AR q).1 h1
    exact ⟨hne, fun hfix ↦ h2
      ((hom_target_source_iff_translation_fixed (K := K) σ AR
        q.1.pair.1.2.1.1 q.1.pair.1.1.1.2 hP q.1.target_nonprojective
        hne hwt).2 hfix)⟩
  · rintro ⟨hne, hw⟩
    refine ⟨(target_ne_outerCellLast_iff σ AR q).2 hne,
      fun h ↦ hw
        ((hom_target_source_iff_translation_fixed (K := K) σ AR
          q.1.pair.1.2.1.1 q.1.pair.1.1.1.2 hP q.1.target_nonprojective
          hne hwt).1 h),
      ?_, ?_⟩
    · exact not_hom_second_source_first_source (K := K) σ AR
        q.1.pair.1.1.1.1 q.1.pair.1.2.1.1 q.1.pair.1.1.1.2 hzt hwt
    · exact not_hom_target_projective_source (K := K) σ AR
        q.1.pair.1.1.1.1 q.1.pair.1.1.1.2 q.1.first_projective
        q.1.target_nonprojective hne hzt

omit [DecidableEq ι] in
include K in
/-- On the refined cell the normalized mirror clauses reduce to the same
two translate inequalities: the forward arrow `w → τt` is again the
fixedness of `w`, and the arrows out of the projective first source are
excluded. -/
theorem mirrorClauses_iff_reduced
    (q : AR.SecondNoninjectiveTargetNoninjectiveOuterPair σ)
    (hP : ¬ Projective (σ.obj q.1.pair.1.2.1.1)) :
    (q.1.pair.1.1.1.2 ≠
        (AR.arTranslation σ
          ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1 ∧
      ¬ HasIrreducibleMorphism
        (σ.obj q.1.pair.1.2.1.1)
        (σ.obj (AR.arTranslation σ
          ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1) ∧
      ¬ HasIrreducibleMorphism
        (σ.obj q.1.pair.1.1.1.1) (σ.obj q.1.pair.1.2.1.1) ∧
      ¬ HasIrreducibleMorphism
        (σ.obj q.1.pair.1.1.1.1)
        (σ.obj (AR.arTranslation σ
          ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1)) ↔
      (q.1.pair.1.1.1.2 ≠
          (AR.arTranslation σ
            ⟨q.1.pair.1.1.1.2, q.1.target_nonprojective⟩).1 ∧
        (AR.arTranslation σ ⟨q.1.pair.1.2.1.1, hP⟩).1 ≠
          q.1.pair.1.2.1.1) := by
  have hzt : HasIrreducibleMorphism
      (σ.obj q.1.pair.1.1.1.1) (σ.obj q.1.pair.1.1.1.2) :=
    q.1.pair.1.1.2
  have hwt : HasIrreducibleMorphism
      (σ.obj q.1.pair.1.2.1.1) (σ.obj q.1.pair.1.1.1.2) := by
    have h := q.1.pair.1.2.2
    rw [← q.1.pair.2] at h
    exact h
  constructor
  · rintro ⟨hne, h2, -, -⟩
    exact ⟨hne, fun hfix ↦ h2
      ((hom_source_translate_iff_translation_fixed (K := K) σ AR
        q.1.pair.1.2.1.1 q.1.pair.1.1.1.2 hP q.1.target_nonprojective
        hne hwt).2 hfix)⟩
  · rintro ⟨hne, hw⟩
    refine ⟨hne,
      fun h ↦ hw
        ((hom_source_translate_iff_translation_fixed (K := K) σ AR
          q.1.pair.1.2.1.1 q.1.pair.1.1.1.2 hP q.1.target_nonprojective
          hne hwt).1 h),
      ?_, ?_⟩
    · exact not_hom_first_source_second_source (K := K) σ AR
        q.1.pair.1.1.1.1 q.1.pair.1.2.1.1 q.1.pair.1.1.1.2 hzt hwt
    · exact not_hom_projective_source_translate (K := K) σ AR
        q.1.pair.1.1.1.1 q.1.pair.1.1.1.2 q.1.first_projective
        q.1.target_nonprojective hne hzt

end FiniteARTranslationData

/-- Same-side packaging: the mirror residual cell of a skeleton is
exactly the deep-image subtype of its own deep intrinsic stratum. -/
def mirrorResidualCellEquivDeepSubtype
    (AR : σ.FiniteARTranslationData) :
    MirrorResidualCell σ AR ≃
      {p : AR.FirstPISecondInteriorNotTwoSourceOuterPair σ //
        p.outer ∈ AR.FirstPIDeepM6Image σ} where
  toFun m :=
    ⟨{ outer := m.1.1
       second_nonprojective := m.1.2.1
       second_noninjective := m.1.2.2.1
       second_not_twoSource := by
         obtain ⟨htv, -⟩ := m.2
         intro hTS
         exact htv
           ((AR.firstPISecond_twoSource_iff_translatedTarget_projective σ
             m.1.1 m.1.2.1 m.1.2.2.1).1 hTS) },
     by
       obtain ⟨htv, hcl⟩ := m.2
       apply (FiniteARTranslationData.mem_firstPIDeepM6Image_iff_normalized
         (K := K) σ AR ⟨m.1.1, m.1.2.2.1, m.1.2.2.2⟩ m.1.2.1
         (fun hTS ↦ htv
           ((AR.firstPISecond_twoSource_iff_translatedTarget_projective σ
             m.1.1 m.1.2.1 m.1.2.2.1).1 hTS))).2
       apply (FiniteARTranslationData.deepClauses_iff_reduced
         (K := K) σ AR ⟨m.1.1, m.1.2.2.1, m.1.2.2.2⟩ m.1.2.1).2
       apply (FiniteARTranslationData.mirrorClauses_iff_reduced
         (K := K) σ AR ⟨m.1.1, m.1.2.2.1, m.1.2.2.2⟩ m.1.2.1).1
       exact (mirrorResidualCell_iff_normalized σ AR m.1 htv).1 hcl⟩
  invFun d :=
    have htNI : ¬ Injective (σ.obj d.1.outer.pair.1.1.1.2) :=
      FiniteARTranslationData.target_noninjective_of_mem_firstPIDeepM6Image
        σ AR d.2
    have htv : ¬ Projective (σ.obj (AR.arTranslation σ
        ⟨d.1.outer.pair.1.1.1.2, d.1.outer.target_nonprojective⟩).1) :=
      fun hproj ↦ d.1.second_not_twoSource
        ((AR.firstPISecond_twoSource_iff_translatedTarget_projective σ
          d.1.outer d.1.second_nonprojective d.1.second_noninjective).2
          hproj)
    ⟨⟨d.1.outer,
      d.1.second_nonprojective, d.1.second_noninjective, htNI⟩,
     htv,
     (mirrorResidualCell_iff_normalized σ AR
        ⟨d.1.outer,
          d.1.second_nonprojective, d.1.second_noninjective, htNI⟩
        htv).2
       ((FiniteARTranslationData.mirrorClauses_iff_reduced (K := K) σ AR
         ⟨d.1.outer, d.1.second_noninjective, htNI⟩
         d.1.second_nonprojective).2
         ((FiniteARTranslationData.deepClauses_iff_reduced (K := K) σ AR
           ⟨d.1.outer, d.1.second_noninjective, htNI⟩
           d.1.second_nonprojective).1
           ((FiniteARTranslationData.mem_firstPIDeepM6Image_iff_normalized
             (K := K) σ AR
             ⟨d.1.outer, d.1.second_noninjective, htNI⟩
             d.1.second_nonprojective d.1.second_not_twoSource).1
             d.2)))⟩
  left_inv m := Subtype.ext (Subtype.ext rfl)
  right_inv d := Subtype.ext
    (FiniteARTranslationData.FirstPISecondInteriorNotTwoSourceOuterPair.ext
      rfl)

include K in
/-- The mirror residual cell has the size of the deep-anchor outer `M6`
family of the same skeleton. -/
theorem mirrorResidualCell_card_eq_deepAnchor
    (AR : σ.FiniteARTranslationData) :
    Fintype.card (MirrorResidualCell σ AR) =
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthDeepAnchor
          σ AR) :=
  Fintype.card_congr
    ((mirrorResidualCellEquivDeepSubtype (K := K) σ AR).trans
      (FiniteARTranslationData.hookM6DeepAnchorEquivDeepStratumSubtype
        σ AR).symm)

namespace AlignedBiduality

include K in
/-- The deep-anchor outer `M6` family has reversal-invariant
cardinality. -/
theorem deepAnchor_card_reversal_invariant
    (D : AlignedBiduality σ τ)
    (ARsigma : σ.FiniteARTranslationData)
    (ARtau : τ.FiniteARTranslationData) :
    Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthDeepAnchor
          σ ARsigma) =
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InjectiveFourthDeepAnchor
          τ ARtau) :=
  (D.deepAnchor_card_eq_mirror (K := K) σ τ ARsigma ARtau).trans
    (mirrorResidualCell_card_eq_deepAnchor (K := K) τ ARtau)

/-- Conditional closure of the paper's colevel-four balance from wall
invariance alone: after the mirror packaging the deep terms cancel, so
aligned invariance of the two wall complements and the reverse-last
family discharges the terminal crossed obligation. -/
theorem intrinsicOuterLocalStrataReversalBalance_of_wallInvariance
    (D : AlignedBiduality σ τ)
    (h : Fintype.card
            (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
              (K := K) τ (τ.finiteDimensionalARTranslationData K S)) +
          Fintype.card
            (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
              (K := K) τ (τ.finiteDimensionalARTranslationData K S)) +
          Fintype.card
            ((τ.finiteDimensionalARTranslationData K S).BoundaryM6ReverseLastPair
              τ) =
        Fintype.card
            (FiniteARTranslationData.HookWallBadU.M6ProjectiveAnchorComplement
              (K := K) σ (σ.finiteDimensionalARTranslationData K R)) +
          Fintype.card
            (FiniteARTranslationData.HookWallBadBUnrestricted.M6SecondBoundaryComplement
              (K := K) σ (σ.finiteDimensionalARTranslationData K R)) +
          Fintype.card
            ((σ.finiteDimensionalARTranslationData K R).BoundaryM6ReverseLastPair
              σ)) :
    IntrinsicOuterLocalStrataReversalBalance
      (k := K) (R := R) (S := S) σ τ := by
  apply D.intrinsicOuterLocalStrataReversalBalance_of_mirrorInvariance
    (K := K) σ τ
  have hM : Fintype.card
      (MirrorResidualCell σ (σ.finiteDimensionalARTranslationData K R)) =
      Fintype.card
        (MirrorResidualCell τ
          (τ.finiteDimensionalARTranslationData K S)) :=
    (mirrorResidualCell_card_eq_deepAnchor (K := K) σ
      (σ.finiteDimensionalARTranslationData K R)).trans
      (D.deepAnchor_card_eq_mirror (K := K) σ τ
        (σ.finiteDimensionalARTranslationData K R)
        (τ.finiteDimensionalARTranslationData K S))
  omega

end AlignedBiduality

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
