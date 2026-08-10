import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopTableCertificates

/-!
# Exact label tables for the two square-zero lollipops

This file specializes the source-facing trace/reject certificates to the
two finite lists in the paper.  The `deadPath` algebra has five named
indecomposables; the `livePath` algebra has seven.  The conversions below
perform all exhaustion and distinctness bookkeeping and leave only the
actual Hom calculations as fields.

The same structures cover the opposite orientations: the supplied label
equivalence names the right modules in the chosen orientation, while the
quotient and submodule rows are entered in the corresponding slots.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.BottomLevels.LollipopRelationTables

open LollipopTableCertificates

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Finite ι]
  (σ : IndecomposableSkeleton.{u, v, w} R ι)
  {FaithfulQ FaithfulS : Set ι → Prop}
  {QCore : MinimalFaithfulCore.Data σ.qClosure FaithfulQ}
  {SCore : MinimalFaithfulCore.Data σ.sClosure FaithfulS}

/-! ## Dead path: `kQ/(x^2,xa)` -/

/-- The five indecomposable labels in the dead-path table. -/
inductive DeadPathLabel where
  | s1
  | s2
  | x
  | a
  | p
  deriving DecidableEq, Fintype

/-- The actual Hom certificates required for the dead-path table.

The quotient core is `{X,A,S1}`, with good outsiders `P,S2`.  The
submodule core is `{P,S2,S1}`, with good outsiders `X,A`.  Since these are
all the outsiders, there are no bad-row presentation fields. -/
structure DeadPathCertificates where
  label : DeadPathLabel ≃ ι
  faithfulQ_monotone : Monotone FaithfulQ
  faithfulS_monotone : Monotone FaithfulS
  quotient_core :
    (QCore.core : Set ι) =
      label '' ({.x, .a, .s1} : Set DeadPathLabel)
  submodule_core :
    (SCore.core : Set ι) =
      label '' ({.p, .s2, .s1} : Set DeadPathLabel)
  quotient_p_omissions :
    ∀ j : ι,
      j ∉ insert (label .p) (QCore.core : Set ι) →
        Quotient.OmissionCertificate σ
          (insert (label .p) (QCore.core : Set ι)) j
  quotient_s2_omissions :
    ∀ j : ι,
      j ∉ insert (label .s2) (QCore.core : Set ι) →
        Quotient.OmissionCertificate σ
          (insert (label .s2) (QCore.core : Set ι)) j
  submodule_x_omissions :
    ∀ j : ι,
      j ∉ insert (label .x) (SCore.core : Set ι) →
        Submodule.OmissionCertificate σ
          (insert (label .x) (SCore.core : Set ι)) j
  submodule_a_omissions :
    ∀ j : ι,
      j ∉ insert (label .a) (SCore.core : Set ι) →
        Submodule.OmissionCertificate σ
          (insert (label .a) (SCore.core : Set ι)) j

namespace DeadPathCertificates

variable {σ}

omit [Finite ι] in
/-- Exhaustion of the quotient outsiders in the five-label table. -/
theorem quotient_outside
    (T : DeadPathCertificates σ (QCore := QCore) (SCore := SCore))
    {z : ι} (hz : z ∉ (QCore.core : Set ι)) :
    z = T.label .p ∨ z = T.label .s2 := by
  obtain ⟨l, rfl⟩ := T.label.surjective z
  cases l with
  | s1 => exact (hz (by rw [T.quotient_core]; simp)).elim
  | s2 => exact Or.inr rfl
  | x => exact (hz (by rw [T.quotient_core]; simp)).elim
  | a => exact (hz (by rw [T.quotient_core]; simp)).elim
  | p => exact Or.inl rfl

omit [Finite ι] in
/-- Exhaustion of the submodule outsiders in the five-label table. -/
theorem submodule_outside
    (T : DeadPathCertificates σ (QCore := QCore) (SCore := SCore))
    {z : ι} (hz : z ∉ (SCore.core : Set ι)) :
    z = T.label .x ∨ z = T.label .a := by
  obtain ⟨l, rfl⟩ := T.label.surjective z
  cases l with
  | s1 => exact (hz (by rw [T.submodule_core]; simp)).elim
  | s2 => exact (hz (by rw [T.submodule_core]; simp)).elim
  | x => exact Or.inl rfl
  | a => exact Or.inr rfl
  | p => exact (hz (by rw [T.submodule_core]; simp)).elim

/-- The quotient half of the dead-path table. -/
def quotientNamed
    (T : DeadPathCertificates σ (QCore := QCore) (SCore := SCore)) :
    Quotient.NamedTwoExtensionCertificates σ QCore where
  faithful_monotone := T.faithfulQ_monotone
  core_ncard := by
    rw [T.quotient_core, Set.ncard_image_of_injective _ T.label.injective]
    exact Set.ncard_eq_three.mpr
      ⟨.x, .a, .s1, by decide, by decide, by decide, rfl⟩
  good₀ := T.label .p
  good₁ := T.label .s2
  good_ne := by
    intro h
    exact (by decide : DeadPathLabel.p ≠ .s2) (T.label.injective h)
  good₀_not_core := by
    rw [T.quotient_core]
    simp
  good₁_not_core := by
    rw [T.quotient_core]
    simp
  good₀_omissions := T.quotient_p_omissions
  good₁_omissions := T.quotient_s2_omissions
  other_nonclosed := by
    intro z hz hzp hzs
    exact False.elim (by
      rcases T.quotient_outside hz with hz' | hz'
      · exact hzp hz'
      · exact hzs hz')

/-- The submodule half of the dead-path table. -/
def submoduleNamed
    (T : DeadPathCertificates σ (QCore := QCore) (SCore := SCore)) :
    Submodule.NamedTwoExtensionCertificates σ SCore where
  faithful_monotone := T.faithfulS_monotone
  core_ncard := by
    rw [T.submodule_core, Set.ncard_image_of_injective _ T.label.injective]
    exact Set.ncard_eq_three.mpr
      ⟨.p, .s2, .s1, by decide, by decide, by decide, rfl⟩
  good₀ := T.label .x
  good₁ := T.label .a
  good_ne := by
    intro h
    exact (by decide : DeadPathLabel.x ≠ .a) (T.label.injective h)
  good₀_not_core := by
    rw [T.submodule_core]
    simp
  good₁_not_core := by
    rw [T.submodule_core]
    simp
  good₀_omissions := T.submodule_x_omissions
  good₁_omissions := T.submodule_a_omissions
  other_nonclosed := by
    intro z hz hzx hza
    exact False.elim (by
      rcases T.submodule_outside hz with hz' | hz'
      · exact hzx hz'
      · exact hza hz')

/-- The exact paired table consumed by the coefficient endpoint. -/
def paired
    (T : DeadPathCertificates σ (QCore := QCore) (SCore := SCore)) :
    PairedCertificates σ (QCore := QCore) (SCore := SCore) where
  quotient := T.quotientNamed
  submodule := T.submoduleNamed

end DeadPathCertificates

/-! ## Live path: `kQ/(x^2)` -/

/-- The seven indecomposable labels in the live-path table. -/
inductive LivePathLabel where
  | s1
  | s2
  | x
  | a
  | u
  | w
  | p
  deriving DecidableEq, Fintype

/-- The actual Hom certificates required for the live-path table.

The quotient core is `{X,U,S1}`.  Its good outsiders are `A,S2`, while
`P,W` are bad.  The submodule core is `{P,S2,A}`.  Its good outsiders are
`S1,U`, while `X,W` are bad. -/
structure LivePathCertificates where
  label : LivePathLabel ≃ ι
  faithfulQ_monotone : Monotone FaithfulQ
  faithfulS_monotone : Monotone FaithfulS
  quotient_core :
    (QCore.core : Set ι) =
      label '' ({.x, .u, .s1} : Set LivePathLabel)
  submodule_core :
    (SCore.core : Set ι) =
      label '' ({.p, .s2, .a} : Set LivePathLabel)
  quotient_a_omissions :
    ∀ j : ι,
      j ∉ insert (label .a) (QCore.core : Set ι) →
        Quotient.OmissionCertificate σ
          (insert (label .a) (QCore.core : Set ι)) j
  quotient_s2_omissions :
    ∀ j : ι,
      j ∉ insert (label .s2) (QCore.core : Set ι) →
        Quotient.OmissionCertificate σ
          (insert (label .s2) (QCore.core : Set ι)) j
  quotient_p_generates_w :
    σ.FacPresentation
      (insert (label .p) (QCore.core : Set ι)) (σ.obj (label .w))
  quotient_w_generates_a :
    σ.FacPresentation
      (insert (label .w) (QCore.core : Set ι)) (σ.obj (label .a))
  submodule_s1_omissions :
    ∀ j : ι,
      j ∉ insert (label .s1) (SCore.core : Set ι) →
        Submodule.OmissionCertificate σ
          (insert (label .s1) (SCore.core : Set ι)) j
  submodule_u_omissions :
    ∀ j : ι,
      j ∉ insert (label .u) (SCore.core : Set ι) →
        Submodule.OmissionCertificate σ
          (insert (label .u) (SCore.core : Set ι)) j
  submodule_x_generates_w :
    σ.SubPresentation
      (insert (label .x) (SCore.core : Set ι)) (σ.obj (label .w))
  submodule_w_generates_s1 :
    σ.SubPresentation
      (insert (label .w) (SCore.core : Set ι)) (σ.obj (label .s1))

namespace LivePathCertificates

variable {σ}

omit [Finite ι] in
/-- Exhaustion of the quotient outsiders in the seven-label table. -/
theorem quotient_outside
    (T : LivePathCertificates σ (QCore := QCore) (SCore := SCore))
    {z : ι} (hz : z ∉ (QCore.core : Set ι)) :
    z = T.label .a ∨ z = T.label .s2 ∨
      z = T.label .p ∨ z = T.label .w := by
  obtain ⟨l, rfl⟩ := T.label.surjective z
  cases l with
  | s1 => exact (hz (by rw [T.quotient_core]; simp)).elim
  | s2 => exact Or.inr (Or.inl rfl)
  | x => exact (hz (by rw [T.quotient_core]; simp)).elim
  | a => exact Or.inl rfl
  | u => exact (hz (by rw [T.quotient_core]; simp)).elim
  | w => exact Or.inr (Or.inr (Or.inr rfl))
  | p => exact Or.inr (Or.inr (Or.inl rfl))

omit [Finite ι] in
/-- Exhaustion of the submodule outsiders in the seven-label table. -/
theorem submodule_outside
    (T : LivePathCertificates σ (QCore := QCore) (SCore := SCore))
    {z : ι} (hz : z ∉ (SCore.core : Set ι)) :
    z = T.label .s1 ∨ z = T.label .u ∨
      z = T.label .x ∨ z = T.label .w := by
  obtain ⟨l, rfl⟩ := T.label.surjective z
  cases l with
  | s1 => exact Or.inl rfl
  | s2 => exact (hz (by rw [T.submodule_core]; simp)).elim
  | x => exact Or.inr (Or.inr (Or.inl rfl))
  | a => exact (hz (by rw [T.submodule_core]; simp)).elim
  | u => exact Or.inr (Or.inl rfl)
  | w => exact Or.inr (Or.inr (Or.inr rfl))
  | p => exact (hz (by rw [T.submodule_core]; simp)).elim

/-- The quotient half of the live-path table. -/
def quotientNamed
    (T : LivePathCertificates σ (QCore := QCore) (SCore := SCore)) :
    Quotient.NamedTwoExtensionCertificates σ QCore where
  faithful_monotone := T.faithfulQ_monotone
  core_ncard := by
    rw [T.quotient_core, Set.ncard_image_of_injective _ T.label.injective]
    exact Set.ncard_eq_three.mpr
      ⟨.x, .u, .s1, by decide, by decide, by decide, rfl⟩
  good₀ := T.label .a
  good₁ := T.label .s2
  good_ne := by
    intro h
    exact (by decide : LivePathLabel.a ≠ .s2) (T.label.injective h)
  good₀_not_core := by
    rw [T.quotient_core]
    simp
  good₁_not_core := by
    rw [T.quotient_core]
    simp
  good₀_omissions := T.quotient_a_omissions
  good₁_omissions := T.quotient_s2_omissions
  other_nonclosed := by
    intro z hz hza hzs2
    by_cases hzp : z = T.label .p
    · subst z
      exact {
        target := T.label .w
        target_not_mem := by
          rw [T.quotient_core]
          simp
        presentation := T.quotient_p_generates_w }
    by_cases hzw : z = T.label .w
    · subst z
      exact {
        target := T.label .a
        target_not_mem := by
          rw [T.quotient_core]
          simp
        presentation := T.quotient_w_generates_a }
    exact False.elim (by
      rcases T.quotient_outside hz with hz' | hz' | hz' | hz'
      · exact hza hz'
      · exact hzs2 hz'
      · exact hzp hz'
      · exact hzw hz')

/-- The submodule half of the live-path table. -/
def submoduleNamed
    (T : LivePathCertificates σ (QCore := QCore) (SCore := SCore)) :
    Submodule.NamedTwoExtensionCertificates σ SCore where
  faithful_monotone := T.faithfulS_monotone
  core_ncard := by
    rw [T.submodule_core, Set.ncard_image_of_injective _ T.label.injective]
    exact Set.ncard_eq_three.mpr
      ⟨.p, .s2, .a, by decide, by decide, by decide, rfl⟩
  good₀ := T.label .s1
  good₁ := T.label .u
  good_ne := by
    intro h
    exact (by decide : LivePathLabel.s1 ≠ .u) (T.label.injective h)
  good₀_not_core := by
    rw [T.submodule_core]
    simp
  good₁_not_core := by
    rw [T.submodule_core]
    simp
  good₀_omissions := T.submodule_s1_omissions
  good₁_omissions := T.submodule_u_omissions
  other_nonclosed := by
    intro z hz hzs1 hzu
    by_cases hzx : z = T.label .x
    · subst z
      exact {
        target := T.label .w
        target_not_mem := by
          rw [T.submodule_core]
          simp
        presentation := T.submodule_x_generates_w }
    by_cases hzw : z = T.label .w
    · subst z
      exact {
        target := T.label .s1
        target_not_mem := by
          rw [T.submodule_core]
          simp
        presentation := T.submodule_w_generates_s1 }
    exact False.elim (by
      rcases T.submodule_outside hz with hz' | hz' | hz' | hz'
      · exact hzs1 hz'
      · exact hzu hz'
      · exact hzx hz'
      · exact hzw hz')

/-- The exact paired table consumed by the coefficient endpoint. -/
def paired
    (T : LivePathCertificates σ (QCore := QCore) (SCore := SCore)) :
    PairedCertificates σ (QCore := QCore) (SCore := SCore) where
  quotient := T.quotientNamed
  submodule := T.submoduleNamed

end LivePathCertificates

/-! ## Relation-indexed wrapper -/

/-- Either exact relation table, indexed by the paper's relation variant.
Orientation is handled by the label equivalence and the placement of the
quotient/submodule rows. -/
inductive RelationCertificates :
    ConnectedSmallCore.LollipopRelation →
      Type (max (max (max u v) w) 1) where
  | deadPath
      (T : DeadPathCertificates σ (QCore := QCore) (SCore := SCore)) :
      RelationCertificates .deadPath
  | livePath
      (T : LivePathCertificates σ (QCore := QCore) (SCore := SCore)) :
      RelationCertificates .livePath

namespace RelationCertificates

variable {σ}

/-- Every relation-indexed source table yields the exact paired table. -/
def paired {relation : ConnectedSmallCore.LollipopRelation}
    (T : RelationCertificates σ (QCore := QCore) (SCore := SCore) relation) :
    PairedCertificates σ (QCore := QCore) (SCore := SCore) :=
  match T with
  | .deadPath T => T.paired
  | .livePath T => T.paired

/-- Every dead/live relation table, in either orientation, proves equality
of the two faithful degree-four counts. -/
theorem faithfulLevelCount_four_eq
    {relation : ConnectedSmallCore.LollipopRelation}
    (T : RelationCertificates σ (QCore := QCore) (SCore := SCore) relation) :
    MinimalFaithfulCore.faithfulLevelCount σ.qClosure FaithfulQ 4 =
      MinimalFaithfulCore.faithfulLevelCount σ.sClosure FaithfulS 4 :=
  T.paired.faithfulLevelCount_four_eq

end RelationCertificates

end QuotientSubmoduleEquidistribution.BottomLevels.LollipopRelationTables
