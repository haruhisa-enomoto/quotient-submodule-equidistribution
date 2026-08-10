import OpConjecture.RepresentationTheory.FourVertexArrowOrbitBoundaries
import OpConjecture.RepresentationTheory.FourVertexGlobalSquareShift

/-!
# Labelled arrow occurrences for the four signed hook channels

The manuscript assigns every `M₂`, `M₃`, `M₅`, or `M₆` summand to a
pair of mesh-rotation arrow occurrences having a common target.  This file
makes those assignments canonical.  In the `M₅` case the outgoing arrow is
first rotated once, so that its target is the hook label from which it
started.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton.FiniteARTranslationData

universe u v

variable {k R : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (AR : σ.FiniteARTranslationData)

/-- A labelled pair of irreducible-arrow occurrences with a common target. -/
abbrev CommonTargetArrowPair :=
  {p : σ.IrreduciblePair × σ.IrreduciblePair //
    p.1.1.2 = p.2.1.2}

/-- Common-target pairs on the first-two-row-or-column boundary of the
global simultaneous two-step translation. -/
abbrev SourceBoundaryCommonTargetArrowPair :=
  {p : CommonTargetArrowPair σ //
    ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource p.1.1 ∨
      ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource p.1.2}

/-- Common-target pairs on the last-two-row-or-column boundary of the
global simultaneous two-step translation. -/
abbrev TargetBoundaryCommonTargetArrowPair :=
  {p : CommonTargetArrowPair σ //
    ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoTarget p.1.1 ∨
      ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoTarget p.1.2}

noncomputable instance commonTargetArrowPairFintype :
    Fintype (CommonTargetArrowPair σ) := Fintype.ofFinite _

noncomputable instance sourceBoundaryCommonTargetArrowPairFintype :
    Fintype (AR.SourceBoundaryCommonTargetArrowPair σ) :=
  Fintype.ofFinite _

noncomputable instance targetBoundaryCommonTargetArrowPairFintype :
    Fintype (AR.TargetBoundaryCommonTargetArrowPair σ) :=
  Fintype.ofFinite _

private theorem card_subtype_eq_sum_indicator
    {α : Type*} [Fintype α]
    (P : α → Prop) [DecidablePred P] [Fintype {x // P x}] :
    Fintype.card {x // P x} =
      ∑ x : α, (if P x then 1 else 0) := by
  classical
  rw [Fintype.card_subtype]
  symm
  exact (Finset.sum_boole P Finset.univ :
    (∑ x ∈ Finset.univ, if P x then 1 else 0) =
      (Finset.univ.filter P).card)

/-- Reorder the common-target and source-boundary subtype predicates. -/
def sourceBoundaryCommonTargetEquiv :
    AR.SourceBoundaryCommonTargetArrowPair σ ≃
      {p : {p : σ.IrreduciblePair × σ.IrreduciblePair //
          ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource p.1 ∨
            ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource p.2} //
        p.1.1.1.2 = p.1.2.1.2} where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reorder the common-target and target-boundary subtype predicates. -/
def targetBoundaryCommonTargetEquiv :
    AR.TargetBoundaryCommonTargetArrowPair σ ≃
      {p : {p : σ.IrreduciblePair × σ.IrreduciblePair //
          ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoTarget p.1 ∨
            ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoTarget p.2} //
        p.1.1.1.2 = p.1.2.1.2} where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The global square shift is equivalently a cardinality equality between
the common-target pairs on its first-two and last-two boundaries. -/
theorem sourceBoundaryCommonTarget_card_eq_targetBoundary :
    Fintype.card (AR.SourceBoundaryCommonTargetArrowPair σ) =
      Fintype.card (AR.TargetBoundaryCommonTargetArrowPair σ) := by
  classical
  let M := AR.arMeshRotationData σ
  rw [Fintype.card_congr (sourceBoundaryCommonTargetEquiv σ AR),
    card_subtype_eq_sum_indicator]
  rw [Fintype.card_congr (targetBoundaryCommonTargetEquiv σ AR),
    card_subtype_eq_sum_indicator]
  exact M.arrowPairTwoStep_targetEquality_balance σ

/-- Exact endpoint transport of common-target pairs across the full global
square shift. -/
def commonTargetBoundaryEquiv :
    AR.SourceBoundaryCommonTargetArrowPair σ ≃
      AR.TargetBoundaryCommonTargetArrowPair σ := by
  let M := AR.arMeshRotationData σ
  let O := M.arrowOrbitData σ
  let B := O.twoStepProd O
  let Q : σ.IrreduciblePair × σ.IrreduciblePair → Prop :=
    fun p ↦ p.1.1.2 = p.2.1.2
  let E := B.boundaryPredicateEquiv Q (by
    intro p hp
    rw [O.twoStepProd_successor_eq O p hp]
    exact M.two_successor_target_eq_iff σ p.1 p.2
      (fun h ↦ hp (Or.inl h)) (fun h ↦ hp (Or.inr h)))
  exact (sourceBoundaryCommonTargetEquiv σ AR).trans <|
    E.trans (targetBoundaryCommonTargetEquiv σ AR).symm

omit [DecidableEq ι] in
/-- The full common-target transport follows the underlying product chain
to its canonical target endpoint. -/
@[simp]
theorem commonTargetBoundaryEquiv_apply_val
    (p : AR.SourceBoundaryCommonTargetArrowPair σ) :
    (AR.commonTargetBoundaryEquiv σ p).1.1 =
      let O := (AR.arMeshRotationData σ).arrowOrbitData σ
      (O.twoStepProd O).targetEndpoint p.1.1 p.2 := by
  rfl

omit [DecidableEq ι] in
/-- Elementwise full square-shift formula: both labelled arrow occurrences
move through the same even number of mesh-rotation steps. -/
theorem commonTargetBoundaryEquiv_apply_eq_iterate
    (p : AR.SourceBoundaryCommonTargetArrowPair σ) :
    let O := (AR.arMeshRotationData σ).arrowOrbitData σ
    let n := (O.twoStepProd O).firstTargetIndex p.1.1 p.2
    (AR.commonTargetBoundaryEquiv σ p).1.1 =
      ((O.successor^[2 * n]) p.1.1.1,
        (O.successor^[2 * n]) p.1.1.2) := by
  rw [AR.commonTargetBoundaryEquiv_apply_val σ p]
  exact (let O := (AR.arMeshRotationData σ).arrowOrbitData σ
    O.twoStepProd_targetEndpoint_eq O p.1.1 p.2)

/-- Full common-target source-boundary pairs whose two labelled arrow
occurrences belong to different mesh-successor components. -/
abbrev DifferentOrbitSourceBoundaryCommonTargetArrowPair :=
  {p : AR.SourceBoundaryCommonTargetArrowPair σ //
    let O := (AR.arMeshRotationData σ).arrowOrbitData σ
    ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2}

/-- Full common-target target-boundary pairs whose two labelled arrow
occurrences belong to different mesh-successor components. -/
abbrev DifferentOrbitTargetBoundaryCommonTargetArrowPair :=
  {p : AR.TargetBoundaryCommonTargetArrowPair σ //
    let O := (AR.arMeshRotationData σ).arrowOrbitData σ
    ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2}

noncomputable instance
    differentOrbitSourceBoundaryCommonTargetArrowPairFintype :
    Fintype (AR.DifferentOrbitSourceBoundaryCommonTargetArrowPair σ) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitTargetBoundaryCommonTargetArrowPairFintype :
    Fintype (AR.DifferentOrbitTargetBoundaryCommonTargetArrowPair σ) :=
  Fintype.ofFinite _

/-- Exact full square-shift transport for the manuscript's
different-arrow-orbit part.  Occurrence labels are retained, and periodic
components require no separate case. -/
def differentOrbitCommonTargetBoundaryEquiv :
    AR.DifferentOrbitSourceBoundaryCommonTargetArrowPair σ ≃
      AR.DifferentOrbitTargetBoundaryCommonTargetArrowPair σ := by
  let O := (AR.arMeshRotationData σ).arrowOrbitData σ
  let E := AR.commonTargetBoundaryEquiv σ
  apply E.subtypeEquiv
  intro p
  change (¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2) ↔
    ¬ O.SameSuccessorOrbit (E p).1.1.1 (E p).1.1.2
  rw [AR.commonTargetBoundaryEquiv_apply_eq_iterate σ p]
  exact (not_congr <|
    O.sameSuccessorOrbit_iterate_iff p.1.1.1 p.1.1.2
      (2 * (O.twoStepProd O).firstTargetIndex p.1.1 p.2)).symm

omit [DecidableEq ι] in
/-- Cardinal form of the full different-orbit square-shift transport. -/
theorem differentOrbitSourceBoundaryCommonTarget_card_eq_targetBoundary :
    Fintype.card
        (AR.DifferentOrbitSourceBoundaryCommonTargetArrowPair σ) =
      Fintype.card
        (AR.DifferentOrbitTargetBoundaryCommonTargetArrowPair σ) :=
  Fintype.card_congr (AR.differentOrbitCommonTargetBoundaryEquiv σ)

omit [DecidableEq ι] in
/-- A common-target pair whose first arrow starts at a
projective-injective label lies on both full boundaries, so the global
square-shift endpoint transport fixes its ordered labelled occurrence. -/
theorem commonTargetBoundaryEquiv_apply_of_firstSource_projective_injective
    (p : CommonTargetArrowPair σ)
    (hp : Projective (σ.obj p.1.1.1.1))
    (hi : Injective (σ.obj p.1.1.1.1)) :
    (AR.commonTargetBoundaryEquiv σ
      ⟨p, Or.inl <|
        ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
          σ p.1.1).2 (Or.inr hp)⟩).1 = p := by
  let O := (AR.arMeshRotationData σ).arrowOrbitData σ
  let B := O.twoStepProd O
  apply Subtype.ext
  rw [AR.commonTargetBoundaryEquiv_apply_val σ]
  apply B.targetEndpoint_eq_self_of_mem_target
  exact Or.inl <|
    ((AR.arMeshRotationData σ).arrowOrbit_twoTarget_iff
      σ p.1.1).2 (Or.inl hi)

/-- A labelled pair of irreducible-arrow occurrences with a common source. -/
abbrev CommonSourceArrowPair :=
  {p : σ.IrreduciblePair × σ.IrreduciblePair //
    p.1.1.1 = p.2.1.1}

/-- Common-source pairs on the first-two-row-or-column boundary of the
global simultaneous two-step translation. -/
abbrev SourceBoundaryCommonSourceArrowPair :=
  {p : CommonSourceArrowPair σ //
    ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource p.1.1 ∨
      ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource p.1.2}

/-- Common-source pairs on the last-two-row-or-column boundary of the
global simultaneous two-step translation. -/
abbrev TargetBoundaryCommonSourceArrowPair :=
  {p : CommonSourceArrowPair σ //
    ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoTarget p.1.1 ∨
      ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoTarget p.1.2}

noncomputable instance commonSourceArrowPairFintype :
    Fintype (CommonSourceArrowPair σ) := Fintype.ofFinite _

noncomputable instance sourceBoundaryCommonSourceArrowPairFintype :
    Fintype (AR.SourceBoundaryCommonSourceArrowPair σ) :=
  Fintype.ofFinite _

noncomputable instance targetBoundaryCommonSourceArrowPairFintype :
    Fintype (AR.TargetBoundaryCommonSourceArrowPair σ) :=
  Fintype.ofFinite _

/-- Reorder the common-source and source-boundary subtype predicates. -/
def sourceBoundaryCommonSourceEquiv :
    AR.SourceBoundaryCommonSourceArrowPair σ ≃
      {p : {p : σ.IrreduciblePair × σ.IrreduciblePair //
          ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource p.1 ∨
            ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource p.2} //
        p.1.1.1.1 = p.1.2.1.1} where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reorder the common-source and target-boundary subtype predicates. -/
def targetBoundaryCommonSourceEquiv :
    AR.TargetBoundaryCommonSourceArrowPair σ ≃
      {p : {p : σ.IrreduciblePair × σ.IrreduciblePair //
          ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoTarget p.1 ∨
            ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoTarget p.2} //
        p.1.1.1.1 = p.1.2.1.1} where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The global square shift preserves the number of common-source pairs on
its first-two and last-two boundaries. -/
theorem sourceBoundaryCommonSource_card_eq_targetBoundary :
    Fintype.card (AR.SourceBoundaryCommonSourceArrowPair σ) =
      Fintype.card (AR.TargetBoundaryCommonSourceArrowPair σ) := by
  classical
  let M := AR.arMeshRotationData σ
  rw [Fintype.card_congr (sourceBoundaryCommonSourceEquiv σ AR),
    card_subtype_eq_sum_indicator]
  rw [Fintype.card_congr (targetBoundaryCommonSourceEquiv σ AR),
    card_subtype_eq_sum_indicator]
  exact M.arrowPairTwoStep_sourceEquality_balance σ

/-- Exact endpoint transport of common-source pairs across the full global
square shift. -/
def commonSourceBoundaryEquiv :
    AR.SourceBoundaryCommonSourceArrowPair σ ≃
      AR.TargetBoundaryCommonSourceArrowPair σ := by
  let M := AR.arMeshRotationData σ
  let O := M.arrowOrbitData σ
  let B := O.twoStepProd O
  let Q : σ.IrreduciblePair × σ.IrreduciblePair → Prop :=
    fun p ↦ p.1.1.1 = p.2.1.1
  let E := B.boundaryPredicateEquiv Q (by
    intro p hp
    rw [O.twoStepProd_successor_eq O p hp]
    exact M.two_successor_source_eq_iff σ p.1 p.2
      (fun h ↦ hp (Or.inl h)) (fun h ↦ hp (Or.inr h)))
  exact (sourceBoundaryCommonSourceEquiv σ AR).trans <|
    E.trans (targetBoundaryCommonSourceEquiv σ AR).symm

omit [DecidableEq ι] in
/-- The full common-source transport follows the same product-chain
endpoint map as the common-target transport. -/
@[simp]
theorem commonSourceBoundaryEquiv_apply_val
    (p : AR.SourceBoundaryCommonSourceArrowPair σ) :
    (AR.commonSourceBoundaryEquiv σ p).1.1 =
      let O := (AR.arMeshRotationData σ).arrowOrbitData σ
      (O.twoStepProd O).targetEndpoint p.1.1 p.2 := by
  rfl

omit [DecidableEq ι] in
/-- Elementwise full square-shift formula for common-source pairs. -/
theorem commonSourceBoundaryEquiv_apply_eq_iterate
    (p : AR.SourceBoundaryCommonSourceArrowPair σ) :
    let O := (AR.arMeshRotationData σ).arrowOrbitData σ
    let n := (O.twoStepProd O).firstTargetIndex p.1.1 p.2
    (AR.commonSourceBoundaryEquiv σ p).1.1 =
      ((O.successor^[2 * n]) p.1.1.1,
        (O.successor^[2 * n]) p.1.1.2) := by
  rw [AR.commonSourceBoundaryEquiv_apply_val σ p]
  exact (let O := (AR.arMeshRotationData σ).arrowOrbitData σ
    O.twoStepProd_targetEndpoint_eq O p.1.1 p.2)

/-- Full common-source source-boundary pairs from different intrinsic
arrow-orbit components. -/
abbrev DifferentOrbitSourceBoundaryCommonSourceArrowPair :=
  {p : AR.SourceBoundaryCommonSourceArrowPair σ //
    let O := (AR.arMeshRotationData σ).arrowOrbitData σ
    ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2}

/-- Full common-source target-boundary pairs from different intrinsic
arrow-orbit components. -/
abbrev DifferentOrbitTargetBoundaryCommonSourceArrowPair :=
  {p : AR.TargetBoundaryCommonSourceArrowPair σ //
    let O := (AR.arMeshRotationData σ).arrowOrbitData σ
    ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2}

noncomputable instance
    differentOrbitSourceBoundaryCommonSourceArrowPairFintype :
    Fintype (AR.DifferentOrbitSourceBoundaryCommonSourceArrowPair σ) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitTargetBoundaryCommonSourceArrowPairFintype :
    Fintype (AR.DifferentOrbitTargetBoundaryCommonSourceArrowPair σ) :=
  Fintype.ofFinite _

/-- Exact full common-source square shift restricted to different arrow
orbits. -/
def differentOrbitCommonSourceBoundaryEquiv :
    AR.DifferentOrbitSourceBoundaryCommonSourceArrowPair σ ≃
      AR.DifferentOrbitTargetBoundaryCommonSourceArrowPair σ := by
  let O := (AR.arMeshRotationData σ).arrowOrbitData σ
  let E := AR.commonSourceBoundaryEquiv σ
  apply E.subtypeEquiv
  intro p
  change (¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2) ↔
    ¬ O.SameSuccessorOrbit (E p).1.1.1 (E p).1.1.2
  rw [AR.commonSourceBoundaryEquiv_apply_eq_iterate σ p]
  exact (not_congr <|
    O.sameSuccessorOrbit_iterate_iff p.1.1.1 p.1.1.2
      (2 * (O.twoStepProd O).firstTargetIndex p.1.1 p.2)).symm

/-- Common-target pairs of arrow occurrences after deleting the outermost
occurrence of every chain orbit. -/
abbrev InteriorCommonTargetArrowPair :=
  {p : (AR.arMeshRotationData σ).InteriorArrow σ ×
      (AR.arMeshRotationData σ).InteriorArrow σ //
    p.1.1.1.2 = p.2.1.1.2}

/-- Intrinsic different-component predicate on a trimmed common-target
labelled occurrence pair. -/
def InteriorCommonTargetArrowPair.DifferentOrbit
    (p : AR.InteriorCommonTargetArrowPair σ) : Prop :=
  let U := (AR.arMeshRotationData σ).arrowInteriorOrbitData σ
  ¬ U.SameSuccessorOrbit p.1.1 p.1.2

/-- Common-target interior pairs on the first two shifted boundary
layers. -/
abbrev InteriorSourceBoundaryCommonTargetArrowPair :=
  {p : AR.InteriorCommonTargetArrowPair σ //
    ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoSource p.1.1 ∨
      ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoSource p.1.2}

/-- Common-target interior pairs on the last two shifted boundary
layers. -/
abbrev InteriorTargetBoundaryCommonTargetArrowPair :=
  {p : AR.InteriorCommonTargetArrowPair σ //
    ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoTarget p.1.1 ∨
      ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoTarget p.1.2}

noncomputable instance interiorCommonTargetArrowPairFintype :
    Fintype (AR.InteriorCommonTargetArrowPair σ) := Fintype.ofFinite _

noncomputable instance interiorSourceBoundaryCommonTargetArrowPairFintype :
    Fintype (AR.InteriorSourceBoundaryCommonTargetArrowPair σ) :=
  Fintype.ofFinite _

noncomputable instance interiorTargetBoundaryCommonTargetArrowPairFintype :
    Fintype (AR.InteriorTargetBoundaryCommonTargetArrowPair σ) :=
  Fintype.ofFinite _

/-- Reorder the common-target and shifted source-boundary predicates. -/
def interiorSourceBoundaryCommonTargetEquiv :
    AR.InteriorSourceBoundaryCommonTargetArrowPair σ ≃
      {p : {p : (AR.arMeshRotationData σ).InteriorArrow σ ×
          (AR.arMeshRotationData σ).InteriorArrow σ //
          ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoSource p.1 ∨
            ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoSource p.2} //
        p.1.1.1.1.2 = p.1.2.1.1.2} where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reorder the common-target and shifted target-boundary predicates. -/
def interiorTargetBoundaryCommonTargetEquiv :
    AR.InteriorTargetBoundaryCommonTargetArrowPair σ ≃
      {p : {p : (AR.arMeshRotationData σ).InteriorArrow σ ×
          (AR.arMeshRotationData σ).InteriorArrow σ //
          ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoTarget p.1 ∨
            ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoTarget p.2} //
        p.1.1.1.1.2 = p.1.2.1.1.2} where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact cardinal form of the manuscript's raw shifted rectangle
identity, with the outermost chain occurrences deleted. -/
theorem interiorSourceBoundaryCommonTarget_card_eq_targetBoundary :
    Fintype.card (AR.InteriorSourceBoundaryCommonTargetArrowPair σ) =
      Fintype.card (AR.InteriorTargetBoundaryCommonTargetArrowPair σ) := by
  classical
  let M := AR.arMeshRotationData σ
  rw [Fintype.card_congr
      (interiorSourceBoundaryCommonTargetEquiv σ AR),
    card_subtype_eq_sum_indicator]
  rw [Fintype.card_congr
      (interiorTargetBoundaryCommonTargetEquiv σ AR),
    card_subtype_eq_sum_indicator]
  exact M.arrowInteriorPairTwoStep_targetEquality_balance σ

/-- Exact endpoint transport of common-target pairs across the global
trimmed square shift. -/
def interiorCommonTargetBoundaryEquiv :
    AR.InteriorSourceBoundaryCommonTargetArrowPair σ ≃
      AR.InteriorTargetBoundaryCommonTargetArrowPair σ := by
  let M := AR.arMeshRotationData σ
  let U := M.arrowInteriorOrbitData σ
  let B := U.twoStepProd U
  let Q : M.InteriorArrow σ × M.InteriorArrow σ → Prop :=
    fun p ↦ p.1.1.1.2 = p.2.1.1.2
  let E := B.boundaryPredicateEquiv Q (by
    intro p hp
    rw [U.twoStepProd_successor_eq U p hp]
    exact M.interior_two_successor_target_eq_iff σ p.1 p.2
      (fun h ↦ hp (Or.inl h)) (fun h ↦ hp (Or.inr h)))
  exact (interiorSourceBoundaryCommonTargetEquiv σ AR).trans <|
    E.trans (interiorTargetBoundaryCommonTargetEquiv σ AR).symm

omit [DecidableEq ι] in
/-- The exact common-target transport follows the underlying product chain
all the way to its canonical target endpoint. -/
@[simp]
theorem interiorCommonTargetBoundaryEquiv_apply_val
    (p : AR.InteriorSourceBoundaryCommonTargetArrowPair σ) :
    (AR.interiorCommonTargetBoundaryEquiv σ p).1.1 =
      let U := (AR.arMeshRotationData σ).arrowInteriorOrbitData σ
      (U.twoStepProd U).targetEndpoint p.1.1 p.2 := by
  rfl

omit [DecidableEq ι] in
/-- Elementwise square-shift formula: both labelled arrow occurrences move
through the same even number of trimmed mesh-rotation steps. -/
theorem interiorCommonTargetBoundaryEquiv_apply_eq_iterate
    (p : AR.InteriorSourceBoundaryCommonTargetArrowPair σ) :
    let U := (AR.arMeshRotationData σ).arrowInteriorOrbitData σ
    let n := (U.twoStepProd U).firstTargetIndex p.1.1 p.2
    (AR.interiorCommonTargetBoundaryEquiv σ p).1.1 =
      ((U.successor^[2 * n]) p.1.1.1,
        (U.successor^[2 * n]) p.1.1.2) := by
  rw [AR.interiorCommonTargetBoundaryEquiv_apply_val σ p]
  exact (let U := (AR.arMeshRotationData σ).arrowInteriorOrbitData σ
    U.twoStepProd_targetEndpoint_eq U p.1.1 p.2)

/-- Trimmed common-target source-boundary pairs whose two labelled interior
arrow occurrences belong to different mesh-successor components. -/
abbrev InteriorDifferentOrbitSourceBoundaryCommonTargetArrowPair :=
  {p : AR.InteriorSourceBoundaryCommonTargetArrowPair σ //
    InteriorCommonTargetArrowPair.DifferentOrbit σ AR p.1}

/-- Trimmed common-target target-boundary pairs whose two labelled interior
arrow occurrences belong to different mesh-successor components. -/
abbrev InteriorDifferentOrbitTargetBoundaryCommonTargetArrowPair :=
  {p : AR.InteriorTargetBoundaryCommonTargetArrowPair σ //
    InteriorCommonTargetArrowPair.DifferentOrbit σ AR p.1}

noncomputable instance
    interiorDifferentOrbitSourceBoundaryCommonTargetArrowPairFintype :
    Fintype
      (AR.InteriorDifferentOrbitSourceBoundaryCommonTargetArrowPair σ) :=
  Fintype.ofFinite _

noncomputable instance
    interiorDifferentOrbitTargetBoundaryCommonTargetArrowPairFintype :
    Fintype
      (AR.InteriorDifferentOrbitTargetBoundaryCommonTargetArrowPair σ) :=
  Fintype.ofFinite _

/-- Exact trimmed square-shift transport for pairs of different labelled
arrow orbits.  This is the occurrence-level bijection underlying
`(f,e) ↦ (f+2,e+2)` in the manuscript. -/
def interiorDifferentOrbitCommonTargetBoundaryEquiv :
    AR.InteriorDifferentOrbitSourceBoundaryCommonTargetArrowPair σ ≃
      AR.InteriorDifferentOrbitTargetBoundaryCommonTargetArrowPair σ := by
  let U := (AR.arMeshRotationData σ).arrowInteriorOrbitData σ
  let E := AR.interiorCommonTargetBoundaryEquiv σ
  apply E.subtypeEquiv
  intro p
  change (¬ U.SameSuccessorOrbit p.1.1.1 p.1.1.2) ↔
    ¬ U.SameSuccessorOrbit (E p).1.1.1 (E p).1.1.2
  rw [AR.interiorCommonTargetBoundaryEquiv_apply_eq_iterate σ p]
  exact (not_congr <|
    U.sameSuccessorOrbit_iterate_iff p.1.1.1 p.1.1.2
      (2 * (U.twoStepProd U).firstTargetIndex p.1.1 p.2)).symm

omit [DecidableEq ι] in
/-- Cardinal form of the trimmed different-orbit square-shift transport. -/
theorem interiorDifferentOrbitSourceBoundaryCommonTarget_card_eq_targetBoundary :
    Fintype.card
        (AR.InteriorDifferentOrbitSourceBoundaryCommonTargetArrowPair σ) =
      Fintype.card
        (AR.InteriorDifferentOrbitTargetBoundaryCommonTargetArrowPair σ) :=
  Fintype.card_congr (AR.interiorDifferentOrbitCommonTargetBoundaryEquiv σ)

/-- Common-source pairs of interior arrow occurrences. -/
abbrev InteriorCommonSourceArrowPair :=
  {p : (AR.arMeshRotationData σ).InteriorArrow σ ×
      (AR.arMeshRotationData σ).InteriorArrow σ //
    p.1.1.1.1 = p.2.1.1.1}

/-- Intrinsic different-component predicate on a trimmed common-source
labelled occurrence pair. -/
def InteriorCommonSourceArrowPair.DifferentOrbit
    (p : AR.InteriorCommonSourceArrowPair σ) : Prop :=
  let U := (AR.arMeshRotationData σ).arrowInteriorOrbitData σ
  ¬ U.SameSuccessorOrbit p.1.1 p.1.2

/-- Common-source interior pairs on the shifted source boundary. -/
abbrev InteriorSourceBoundaryCommonSourceArrowPair :=
  {p : AR.InteriorCommonSourceArrowPair σ //
    ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoSource p.1.1 ∨
      ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoSource p.1.2}

/-- Common-source interior pairs on the shifted target boundary. -/
abbrev InteriorTargetBoundaryCommonSourceArrowPair :=
  {p : AR.InteriorCommonSourceArrowPair σ //
    ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoTarget p.1.1 ∨
      ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoTarget p.1.2}

noncomputable instance interiorCommonSourceArrowPairFintype :
    Fintype (AR.InteriorCommonSourceArrowPair σ) := Fintype.ofFinite _

noncomputable instance interiorSourceBoundaryCommonSourceArrowPairFintype :
    Fintype (AR.InteriorSourceBoundaryCommonSourceArrowPair σ) :=
  Fintype.ofFinite _

noncomputable instance interiorTargetBoundaryCommonSourceArrowPairFintype :
    Fintype (AR.InteriorTargetBoundaryCommonSourceArrowPair σ) :=
  Fintype.ofFinite _

def interiorSourceBoundaryCommonSourceEquiv :
    AR.InteriorSourceBoundaryCommonSourceArrowPair σ ≃
      {p : {p : (AR.arMeshRotationData σ).InteriorArrow σ ×
          (AR.arMeshRotationData σ).InteriorArrow σ //
          ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoSource p.1 ∨
            ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoSource p.2} //
        p.1.1.1.1.1 = p.1.2.1.1.1} where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def interiorTargetBoundaryCommonSourceEquiv :
    AR.InteriorTargetBoundaryCommonSourceArrowPair σ ≃
      {p : {p : (AR.arMeshRotationData σ).InteriorArrow σ ×
          (AR.arMeshRotationData σ).InteriorArrow σ //
          ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoTarget p.1 ∨
            ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoTarget p.2} //
        p.1.1.1.1.1 = p.1.2.1.1.1} where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact cardinal form of the source-equality trimmed square shift. -/
theorem interiorSourceBoundaryCommonSource_card_eq_targetBoundary :
    Fintype.card (AR.InteriorSourceBoundaryCommonSourceArrowPair σ) =
      Fintype.card (AR.InteriorTargetBoundaryCommonSourceArrowPair σ) := by
  classical
  let M := AR.arMeshRotationData σ
  rw [Fintype.card_congr
      (interiorSourceBoundaryCommonSourceEquiv σ AR),
    card_subtype_eq_sum_indicator]
  rw [Fintype.card_congr
      (interiorTargetBoundaryCommonSourceEquiv σ AR),
    card_subtype_eq_sum_indicator]
  exact M.arrowInteriorPairTwoStep_sourceEquality_balance σ

/-- Exact endpoint transport of common-source pairs across the global
trimmed square shift. -/
def interiorCommonSourceBoundaryEquiv :
    AR.InteriorSourceBoundaryCommonSourceArrowPair σ ≃
      AR.InteriorTargetBoundaryCommonSourceArrowPair σ := by
  let M := AR.arMeshRotationData σ
  let U := M.arrowInteriorOrbitData σ
  let B := U.twoStepProd U
  let Q : M.InteriorArrow σ × M.InteriorArrow σ → Prop :=
    fun p ↦ p.1.1.1.1 = p.2.1.1.1
  let E := B.boundaryPredicateEquiv Q (by
    intro p hp
    rw [U.twoStepProd_successor_eq U p hp]
    exact M.interior_two_successor_source_eq_iff σ p.1 p.2
      (fun h ↦ hp (Or.inl h)) (fun h ↦ hp (Or.inr h)))
  exact (interiorSourceBoundaryCommonSourceEquiv σ AR).trans <|
    E.trans (interiorTargetBoundaryCommonSourceEquiv σ AR).symm

omit [DecidableEq ι] in
/-- The exact common-source transport has the same underlying product
endpoint map. -/
@[simp]
theorem interiorCommonSourceBoundaryEquiv_apply_val
    (p : AR.InteriorSourceBoundaryCommonSourceArrowPair σ) :
    (AR.interiorCommonSourceBoundaryEquiv σ p).1.1 =
      let U := (AR.arMeshRotationData σ).arrowInteriorOrbitData σ
      (U.twoStepProd U).targetEndpoint p.1.1 p.2 := by
  rfl

omit [DecidableEq ι] in
/-- The same elementwise square-shift formula for common-source pairs. -/
theorem interiorCommonSourceBoundaryEquiv_apply_eq_iterate
    (p : AR.InteriorSourceBoundaryCommonSourceArrowPair σ) :
    let U := (AR.arMeshRotationData σ).arrowInteriorOrbitData σ
    let n := (U.twoStepProd U).firstTargetIndex p.1.1 p.2
    (AR.interiorCommonSourceBoundaryEquiv σ p).1.1 =
      ((U.successor^[2 * n]) p.1.1.1,
        (U.successor^[2 * n]) p.1.1.2) := by
  rw [AR.interiorCommonSourceBoundaryEquiv_apply_val σ p]
  exact (let U := (AR.arMeshRotationData σ).arrowInteriorOrbitData σ
    U.twoStepProd_targetEndpoint_eq U p.1.1 p.2)

/-- Trimmed common-source source-boundary pairs from different intrinsic
arrow-orbit components. -/
abbrev InteriorDifferentOrbitSourceBoundaryCommonSourceArrowPair :=
  {p : AR.InteriorSourceBoundaryCommonSourceArrowPair σ //
    InteriorCommonSourceArrowPair.DifferentOrbit σ AR p.1}

/-- Trimmed common-source target-boundary pairs from different intrinsic
arrow-orbit components. -/
abbrev InteriorDifferentOrbitTargetBoundaryCommonSourceArrowPair :=
  {p : AR.InteriorTargetBoundaryCommonSourceArrowPair σ //
    InteriorCommonSourceArrowPair.DifferentOrbit σ AR p.1}

noncomputable instance
    interiorDifferentOrbitSourceBoundaryCommonSourceArrowPairFintype :
    Fintype
      (AR.InteriorDifferentOrbitSourceBoundaryCommonSourceArrowPair σ) :=
  Fintype.ofFinite _

noncomputable instance
    interiorDifferentOrbitTargetBoundaryCommonSourceArrowPairFintype :
    Fintype
      (AR.InteriorDifferentOrbitTargetBoundaryCommonSourceArrowPair σ) :=
  Fintype.ofFinite _

/-- Exact trimmed common-source square shift restricted to different
labelled arrow orbits. -/
def interiorDifferentOrbitCommonSourceBoundaryEquiv :
    AR.InteriorDifferentOrbitSourceBoundaryCommonSourceArrowPair σ ≃
      AR.InteriorDifferentOrbitTargetBoundaryCommonSourceArrowPair σ := by
  let U := (AR.arMeshRotationData σ).arrowInteriorOrbitData σ
  let E := AR.interiorCommonSourceBoundaryEquiv σ
  apply E.subtypeEquiv
  intro p
  change (¬ U.SameSuccessorOrbit p.1.1.1 p.1.1.2) ↔
    ¬ U.SameSuccessorOrbit (E p).1.1.1 (E p).1.1.2
  rw [AR.interiorCommonSourceBoundaryEquiv_apply_eq_iterate σ p]
  exact (not_congr <|
    U.sameSuccessorOrbit_iterate_iff p.1.1.1 p.1.1.2
      (2 * (U.twoStepProd U).firstTargetIndex p.1.1 p.2)).symm

/-- Predicate saying that an actual labelled arrow survives deletion of the
outermost projective-target and injective-source chain occurrences. -/
def IsInteriorArrow (q : σ.IrreduciblePair) : Prop :=
  ¬ Projective (σ.obj q.1.2) ∧ ¬ Injective (σ.obj q.1.1)

/-- Regard an actual labelled arrow satisfying the interior predicate as a
vertex of the trimmed arrow translation. -/
def toInteriorArrow (q : σ.IrreduciblePair) (hq : IsInteriorArrow σ q) :
    (AR.arMeshRotationData σ).InteriorArrow σ :=
  ⟨q, hq⟩

namespace StripAdmissibleTriple

omit [DecidableEq ι] in
/-- If the first label of an admissible strip is projective and its middle
label is noninjective, then the second displayed arrow is in the first two
layers of the trimmed arrow-chain source boundary. -/
theorem secondArrow_interior_twoSource
    (T : AR.StripAdmissibleTriple σ)
    (haP : Projective (σ.obj T.a))
    (huNI : ¬ Injective (σ.obj T.u)) :
    ((AR.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoSource
      (toInteriorArrow σ AR (T.secondArrow σ AR)
        ⟨T.b_nonprojective, by
          simpa [StripAdmissibleTriple.secondArrow] using huNI⟩) := by
  classical
  let N := AR.arMeshRotationData σ
  let O := N.arrowOrbitData σ
  let U := N.arrowInteriorOrbitData σ
  let H := toInteriorArrow σ AR (T.secondArrow σ AR)
    ⟨T.b_nonprojective, by
      simpa [StripAdmissibleTriple.secondArrow] using huNI⟩
  change U.TwoSource H
  right
  intro hnot
  apply (N.arrowInterior_source_iff σ (U.tau ⟨H, hnot⟩).1).2
  have hval : (U.tau ⟨H, hnot⟩).1.1 =
      T.firstArrow σ AR := by
    have hpred := congrArg Subtype.val (T.secondArrow_predecessor σ AR)
    simpa [U, N, O, H, ARMeshRotationData.arrowInteriorOrbitData,
      OpConjecture.BoundaryTranslationChains.Data.interior,
      toInteriorArrow] using hpred
  rw [hval]
  simpa [StripAdmissibleTriple.firstArrow] using haP

end StripAdmissibleTriple

/-- Forget that both occurrences of a trimmed common-target pair are
interior. -/
def forgetInteriorCommonTarget
    (p : AR.InteriorCommonTargetArrowPair σ) :
    CommonTargetArrowPair σ :=
  ⟨(p.1.1.1, p.1.2.1), p.2⟩

omit [DecidableEq ι] in
theorem forgetInteriorCommonTarget_injective :
    Function.Injective (forgetInteriorCommonTarget σ AR) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg
      (fun r : CommonTargetArrowPair σ ↦ r.1.1) h
  · exact congrArg
      (fun r : CommonTargetArrowPair σ ↦ r.1.2) h

namespace HookWallBadU

variable (W : AR.HookWallBadU σ)

/-- The projective predecessor arrow `z → u` represented by an `M₂`
wall term. -/
def associatedArrow : σ.IrreduciblePair :=
  ⟨(W.1.z, W.1.triple.u), W.2⟩

/-- `M₂` terms whose two assigned arrow occurrences survive the trimming
of their mesh-rotation chains. -/
abbrev InteriorChannel :=
  {W : AR.HookWallBadU σ //
    IsInteriorArrow σ (W.associatedArrow σ AR) ∧
      IsInteriorArrow σ (W.1.triple.firstArrow σ AR)}

omit [Fintype ι] [DecidableEq ι] in
theorem associatedArrow_isInterior_iff :
    IsInteriorArrow σ (W.associatedArrow σ AR) ↔
      ¬ Injective (σ.obj W.1.z) := by
  simp [IsInteriorArrow, associatedArrow, W.1.triple.u_nonprojective]

omit [Fintype ι] [DecidableEq ι] in
theorem firstArrow_isInterior :
    IsInteriorArrow σ (W.1.triple.firstArrow σ AR) := by
  exact ⟨by
      simpa [StripAdmissibleTriple.firstArrow] using
        W.1.triple.u_nonprojective,
    by
      simpa [StripAdmissibleTriple.firstArrow] using
        W.1.triple.a_noninjective σ AR⟩

omit [Fintype ι] [DecidableEq ι] in
theorem interiorChannel_iff :
    (IsInteriorArrow σ (W.associatedArrow σ AR) ∧
      IsInteriorArrow σ (W.1.triple.firstArrow σ AR)) ↔
        ¬ Injective (σ.obj W.1.z) := by
  rw [W.associatedArrow_isInterior_iff σ AR]
  simp only [W.firstArrow_isInterior σ AR, and_true]

/-- The common-target pair assigned to an `M₂` term. -/
def commonTargetPair : CommonTargetArrowPair σ :=
  ⟨(W.associatedArrow σ AR, W.1.triple.firstArrow σ AR), rfl⟩

/-- `M₂` terms lie on the global first-two boundary because their
associated arrow starts at the projective label `z`. -/
def sourceBoundaryPair : AR.SourceBoundaryCommonTargetArrowPair σ :=
  ⟨W.commonTargetPair σ AR, Or.inl <|
    ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff σ
      (W.associatedArrow σ AR)).2 (Or.inr W.1.z_projective)⟩

omit [Fintype ι] [DecidableEq ι] in
theorem commonTargetPair_injective :
    Function.Injective (commonTargetPair σ AR) := by
  intro W₁ W₂ h
  have hassociated := congrArg
    (fun p : CommonTargetArrowPair σ ↦ p.1.1) h
  have hhook := congrArg
    (fun p : CommonTargetArrowPair σ ↦ p.1.2) h
  apply Subtype.ext
  apply HookWallChoice.ext
  · exact StripAdmissibleTriple.firstArrow_injective σ AR hhook
  · exact congrArg
      (fun q : σ.IrreduciblePair ↦ q.1.1) hassociated

/-- The trimmed common-target occurrence assigned to an interior `M₂`
term. -/
def interiorCommonTargetPair (X : HookWallBadU.InteriorChannel σ AR) :
    AR.InteriorCommonTargetArrowPair σ :=
  ⟨(toInteriorArrow σ AR (X.1.associatedArrow σ AR) X.2.1,
    toInteriorArrow σ AR (X.1.1.triple.firstArrow σ AR) X.2.2), rfl⟩

/-- Every interior `M₂` occurrence lies on the shifted source boundary. -/
def interiorSourceBoundaryPair (X : HookWallBadU.InteriorChannel σ AR) :
    AR.InteriorSourceBoundaryCommonTargetArrowPair σ :=
  ⟨HookWallBadU.interiorCommonTargetPair σ AR X, Or.inl <| Or.inl <|
    ((AR.arMeshRotationData σ).arrowInterior_source_iff σ
      (toInteriorArrow σ AR (X.1.associatedArrow σ AR) X.2.1)).2
        X.1.1.z_projective⟩

omit [DecidableEq ι] in
theorem interiorCommonTargetPair_injective :
    Function.Injective (interiorCommonTargetPair σ AR) := by
  intro X Y h
  apply Subtype.ext
  apply commonTargetPair_injective σ AR
  have hf := congrArg (forgetInteriorCommonTarget σ AR) h
  simpa [interiorCommonTargetPair, forgetInteriorCommonTarget,
    toInteriorArrow, commonTargetPair] using hf

end HookWallBadU

namespace HookWallBadBUnrestricted

variable (W : AR.HookWallBadBUnrestricted σ)

/-- The projective predecessor arrow `z → b` represented by an `M₃`
wall term. -/
def associatedArrow : σ.IrreduciblePair :=
  ⟨(W.1.z, W.1.triple.b), W.2⟩

/-- `M₃` terms whose two assigned arrow occurrences survive trimming. -/
abbrev InteriorChannel :=
  {W : AR.HookWallBadBUnrestricted σ //
    IsInteriorArrow σ (W.associatedArrow σ AR) ∧
      IsInteriorArrow σ (W.1.triple.secondArrow σ AR)}

omit [Fintype ι] [DecidableEq ι] in
theorem associatedArrow_isInterior_iff :
    IsInteriorArrow σ (W.associatedArrow σ AR) ↔
      ¬ Injective (σ.obj W.1.z) := by
  simp [IsInteriorArrow, associatedArrow, W.1.triple.b_nonprojective]

omit [Fintype ι] [DecidableEq ι] in
theorem secondArrow_isInterior_iff :
    IsInteriorArrow σ (W.1.triple.secondArrow σ AR) ↔
      ¬ Injective (σ.obj W.1.triple.u) := by
  simp [IsInteriorArrow, StripAdmissibleTriple.secondArrow,
    W.1.triple.b_nonprojective]

omit [Fintype ι] [DecidableEq ι] in
theorem interiorChannel_iff :
    (IsInteriorArrow σ (W.associatedArrow σ AR) ∧
      IsInteriorArrow σ (W.1.triple.secondArrow σ AR)) ↔
        ¬ Injective (σ.obj W.1.z) ∧
          ¬ Injective (σ.obj W.1.triple.u) := by
  rw [W.associatedArrow_isInterior_iff σ AR,
    W.secondArrow_isInterior_iff σ AR]

/-- The common-target pair assigned to an `M₃` term. -/
def commonTargetPair : CommonTargetArrowPair σ :=
  ⟨(W.associatedArrow σ AR, W.1.triple.secondArrow σ AR), rfl⟩

/-- `M₃` terms lie on the global first-two boundary because their
associated arrow starts at the projective label `z`. -/
def sourceBoundaryPair : AR.SourceBoundaryCommonTargetArrowPair σ :=
  ⟨W.commonTargetPair σ AR, Or.inl <|
    ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff σ
      (W.associatedArrow σ AR)).2 (Or.inr W.1.z_projective)⟩

omit [Fintype ι] [DecidableEq ι] in
theorem commonTargetPair_injective :
    Function.Injective (commonTargetPair σ AR) := by
  intro W₁ W₂ h
  have hassociated := congrArg
    (fun p : CommonTargetArrowPair σ ↦ p.1.1) h
  have hhook := congrArg
    (fun p : CommonTargetArrowPair σ ↦ p.1.2) h
  apply Subtype.ext
  apply HookWallChoice.ext
  · exact StripAdmissibleTriple.secondArrow_injective σ AR hhook
  · exact congrArg
      (fun q : σ.IrreduciblePair ↦ q.1.1) hassociated

/-- The trimmed common-target occurrence assigned to an interior `M₃`
term. -/
def interiorCommonTargetPair
    (X : HookWallBadBUnrestricted.InteriorChannel σ AR) :
    AR.InteriorCommonTargetArrowPair σ :=
  ⟨(toInteriorArrow σ AR (X.1.associatedArrow σ AR) X.2.1,
    toInteriorArrow σ AR (X.1.1.triple.secondArrow σ AR) X.2.2), rfl⟩

/-- Every interior `M₃` occurrence lies on the shifted source boundary. -/
def interiorSourceBoundaryPair
    (X : HookWallBadBUnrestricted.InteriorChannel σ AR) :
    AR.InteriorSourceBoundaryCommonTargetArrowPair σ :=
  ⟨HookWallBadBUnrestricted.interiorCommonTargetPair σ AR X,
    Or.inl <| Or.inl <|
    ((AR.arMeshRotationData σ).arrowInterior_source_iff σ
      (toInteriorArrow σ AR (X.1.associatedArrow σ AR) X.2.1)).2
        X.1.1.z_projective⟩

omit [DecidableEq ι] in
theorem interiorCommonTargetPair_injective :
    Function.Injective (interiorCommonTargetPair σ AR) := by
  intro X Y h
  apply Subtype.ext
  apply commonTargetPair_injective σ AR
  have hf := congrArg (forgetInteriorCommonTarget σ AR) h
  simpa [interiorCommonTargetPair, forgetInteriorCommonTarget,
    toInteriorArrow, commonTargetPair] using hf

end HookWallBadBUnrestricted

namespace HookM6Channel

variable (M : AR.HookM6Channel σ)

/-- The projective predecessor arrow `z → a` represented by an `M₆`
extension. -/
def associatedArrow : σ.IrreduciblePair :=
  ⟨(M.1.z, M.1.triple.a),
    (M.z_projective_and_z_to_a σ AR).2⟩

/-- `M₆` terms whose two assigned arrow occurrences survive trimming. -/
abbrev InteriorChannel :=
  {M : AR.HookM6Channel σ //
    IsInteriorArrow σ (M.associatedArrow σ AR) ∧
      IsInteriorArrow σ (M.1.triple.hookOrbitAnchor σ AR)}

theorem associatedArrow_isInterior_iff :
    IsInteriorArrow σ (M.associatedArrow σ AR) ↔
      ¬ Injective (σ.obj M.1.z) := by
  simp [IsInteriorArrow, associatedArrow, M.2]

theorem hookOrbitAnchor_isInterior :
    IsInteriorArrow σ (M.1.triple.hookOrbitAnchor σ AR) := by
  refine ⟨?_, ?_⟩
  · simpa only [M.1.triple.hookOrbitAnchor_target σ AR] using M.2
  · exact (((AR.arMeshRotationData σ).arrowOrbitData σ).tau
      ⟨M.1.triple.firstArrow σ AR,
        M.1.triple.u_nonprojective⟩).2

theorem interiorChannel_iff :
    (IsInteriorArrow σ (M.associatedArrow σ AR) ∧
      IsInteriorArrow σ (M.1.triple.hookOrbitAnchor σ AR)) ↔
        ¬ Injective (σ.obj M.1.z) := by
  rw [HookM6Channel.associatedArrow_isInterior_iff σ AR M]
  simp only [HookM6Channel.hookOrbitAnchor_isInterior σ AR M, and_true]

/-- The common-target pair assigned to an `M₆` term.  The second
occurrence is the arrow immediately preceding the displayed hook. -/
def commonTargetPair : CommonTargetArrowPair σ :=
  ⟨(M.associatedArrow σ AR,
    M.1.triple.hookOrbitAnchor σ AR),
    (M.1.triple.hookOrbitAnchor_target σ AR).symm⟩

/-- `M₆` terms lie on the global first-two boundary because their
associated arrow starts at the projective fourth label `z`. -/
def sourceBoundaryPair : AR.SourceBoundaryCommonTargetArrowPair σ :=
  ⟨M.commonTargetPair σ AR, Or.inl <|
    ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff σ
      (M.associatedArrow σ AR)).2
        (Or.inr (M.z_projective_and_z_to_a σ AR).1)⟩

theorem commonTargetPair_injective :
    Function.Injective (commonTargetPair σ AR) := by
  intro M₁ M₂ h
  have hassociated := congrArg
    (fun p : CommonTargetArrowPair σ ↦ p.1.1) h
  have hanchor := congrArg
    (fun p : CommonTargetArrowPair σ ↦ p.1.2) h
  apply Subtype.ext
  apply HookFourthExtension.ext
  · exact StripAdmissibleTriple.hookOrbitAnchor_injective σ AR hanchor
  · exact congrArg
      (fun q : σ.IrreduciblePair ↦ q.1.1) hassociated

/-- The trimmed common-target occurrence assigned to an interior `M₆`
term. -/
def interiorCommonTargetPair (X : HookM6Channel.InteriorChannel σ AR) :
    AR.InteriorCommonTargetArrowPair σ :=
  ⟨(toInteriorArrow σ AR (X.1.associatedArrow σ AR) X.2.1,
    toInteriorArrow σ AR
      (X.1.1.triple.hookOrbitAnchor σ AR) X.2.2),
    (X.1.1.triple.hookOrbitAnchor_target σ AR).symm⟩

/-- Every interior `M₆` occurrence lies on the shifted source boundary. -/
def interiorSourceBoundaryPair (X : HookM6Channel.InteriorChannel σ AR) :
    AR.InteriorSourceBoundaryCommonTargetArrowPair σ :=
  ⟨HookM6Channel.interiorCommonTargetPair σ AR X, Or.inl <| Or.inl <|
    ((AR.arMeshRotationData σ).arrowInterior_source_iff σ
      (toInteriorArrow σ AR (X.1.associatedArrow σ AR) X.2.1)).2
        (X.1.z_projective_and_z_to_a σ AR).1⟩

theorem interiorCommonTargetPair_injective :
    Function.Injective (interiorCommonTargetPair σ AR) := by
  intro X Y h
  apply Subtype.ext
  apply commonTargetPair_injective σ AR
  have hf := congrArg (forgetInteriorCommonTarget σ AR) h
  simpa [interiorCommonTargetPair, forgetInteriorCommonTarget,
    toInteriorArrow, commonTargetPair] using hf

end HookM6Channel

namespace HookM5Channel

variable (M : AR.HookM5Channel σ)

/-- The unique outgoing arrow `u → z` or `b → z` represented by an
`M₅` extension. -/
def associatedArrow : σ.IrreduciblePair := by
  classical
  by_cases h : HasIrreducibleMorphism
      (σ.obj M.1.triple.u) (σ.obj M.1.z)
  · exact ⟨(M.1.triple.u, M.1.z), h⟩
  · exact ⟨(M.1.triple.b, M.1.z),
      (M.outgoing_to_z σ AR).resolve_left h⟩

/-- The displayed hook arrow ending at the source of the selected `M₅`
arrow. -/
def hookArrow : σ.IrreduciblePair := by
  classical
  by_cases h : HasIrreducibleMorphism
      (σ.obj M.1.triple.u) (σ.obj M.1.z)
  · exact M.1.triple.firstArrow σ AR
  · exact M.1.triple.secondArrow σ AR

@[simp]
theorem associatedArrow_target :
    (M.associatedArrow σ AR).1.2 = M.1.z := by
  classical
  by_cases h : HasIrreducibleMorphism
      (σ.obj M.1.triple.u) (σ.obj M.1.z)
  · simp [associatedArrow, h]
  · simp [associatedArrow, h]

/-- The selected outgoing arrow starts at the target of the selected hook
arrow. -/
theorem associatedArrow_source_eq_hookArrow_target :
    (M.associatedArrow σ AR).1.1 = (M.hookArrow σ AR).1.2 := by
  classical
  by_cases h : HasIrreducibleMorphism
      (σ.obj M.1.triple.u) (σ.obj M.1.z)
  · simp [associatedArrow, hookArrow, h,
      StripAdmissibleTriple.firstArrow]
  · simp [associatedArrow, hookArrow, h,
      StripAdmissibleTriple.secondArrow]

/-- Rotate the outgoing `M₅` arrow once.  Its new target is the hook
label from which the outgoing arrow started. -/
def rotatedAssociatedArrow : σ.IrreduciblePair :=
  (((AR.arMeshRotationData σ).arrowOrbitData σ).tau
    ⟨M.associatedArrow σ AR, by
      simpa only [HookM5Channel.associatedArrow_target σ AR M] using M.2⟩).1

/-- Rotating the selected `M₅` arrow and then taking the chain successor
returns the selected occurrence. -/
theorem rotatedAssociatedArrow_successor :
    ((AR.arMeshRotationData σ).arrowOrbitData σ).successor
        (M.rotatedAssociatedArrow σ AR) =
      M.associatedArrow σ AR := by
  let O := (AR.arMeshRotationData σ).arrowOrbitData σ
  let p : {q : σ.IrreduciblePair //
      ¬ Projective (σ.obj q.1.2)} :=
    ⟨M.associatedArrow σ AR, by
      simpa only [HookM5Channel.associatedArrow_target σ AR M] using M.2⟩
  let q := O.tau p
  change O.successor q.1 = p.1
  have hsuccessor : O.successor q.1 = O.tau.symm ⟨q.1, q.2⟩ := by
    simp [OpConjecture.BoundaryTranslationChains.Data.successor, q.2]
  rw [hsuccessor]
  exact congrArg Subtype.val (O.tau.symm_apply_apply p)

/-- Mesh rotation identifies the target of the rotated `M₅` occurrence
with the target of its selected hook arrow. -/
theorem rotatedAssociatedArrow_target_eq_hookArrow_target :
    (M.rotatedAssociatedArrow σ AR).1.2 =
      (M.hookArrow σ AR).1.2 := by
  let O := (AR.arMeshRotationData σ).arrowOrbitData σ
  have hrotate := (AR.arMeshRotationData σ).arrowOrbitData_tau_val σ
    ⟨M.associatedArrow σ AR, by
      simpa only [HookM5Channel.associatedArrow_target σ AR M] using M.2⟩
  exact (congrArg Prod.snd hrotate).trans
    (HookM5Channel.associatedArrow_source_eq_hookArrow_target σ AR M)

theorem hookArrow_target_nonprojective :
    ¬ Projective (σ.obj (M.hookArrow σ AR).1.2) := by
  classical
  by_cases h : HasIrreducibleMorphism
      (σ.obj M.1.triple.u) (σ.obj M.1.z)
  · simpa [hookArrow, h, StripAdmissibleTriple.firstArrow] using
      M.1.triple.u_nonprojective
  · simpa [hookArrow, h, StripAdmissibleTriple.secondArrow] using
      M.1.triple.b_nonprojective

theorem rotatedAssociatedArrow_isInterior :
    IsInteriorArrow σ (M.rotatedAssociatedArrow σ AR) := by
  refine ⟨?_, ?_⟩
  · rw [M.rotatedAssociatedArrow_target_eq_hookArrow_target σ AR]
    exact M.hookArrow_target_nonprojective σ AR
  · exact (((AR.arMeshRotationData σ).arrowOrbitData σ).tau
      ⟨M.associatedArrow σ AR, by
        simpa only [M.associatedArrow_target σ AR] using M.2⟩).2

theorem hookArrow_isInterior_iff :
    IsInteriorArrow σ (M.hookArrow σ AR) ↔
      HasIrreducibleMorphism
          (σ.obj M.1.triple.u) (σ.obj M.1.z) ∨
        ¬ Injective (σ.obj M.1.triple.u) := by
  classical
  by_cases h : HasIrreducibleMorphism
      (σ.obj M.1.triple.u) (σ.obj M.1.z)
  · simp only [h, true_or, iff_true]
    refine ⟨?_, ?_⟩
    · simpa [hookArrow, h, StripAdmissibleTriple.firstArrow] using
        M.1.triple.u_nonprojective
    · simpa [hookArrow, h, StripAdmissibleTriple.firstArrow] using
        M.1.triple.a_noninjective σ AR
  · simp only [h, false_or]
    constructor
    · intro hInterior
      simpa [hookArrow, h, StripAdmissibleTriple.secondArrow] using
        hInterior.2
    · intro huNI
      exact ⟨by
          simpa [hookArrow, h, StripAdmissibleTriple.secondArrow] using
            M.1.triple.b_nonprojective,
        by simpa [hookArrow, h, StripAdmissibleTriple.secondArrow] using
          huNI⟩

/-- The common-target pair assigned to an `M₅` term. -/
def commonTargetPair : CommonTargetArrowPair σ :=
  ⟨(M.rotatedAssociatedArrow σ AR, M.hookArrow σ AR),
    M.rotatedAssociatedArrow_target_eq_hookArrow_target σ AR⟩

/-- `M₅` terms whose rotated outgoing occurrence and selected hook
occurrence both survive trimming. -/
abbrev InteriorChannel :=
  {M : AR.HookM5Channel σ //
    IsInteriorArrow σ (M.rotatedAssociatedArrow σ AR) ∧
      IsInteriorArrow σ (M.hookArrow σ AR)}

theorem interiorChannel_iff :
    (IsInteriorArrow σ (M.rotatedAssociatedArrow σ AR) ∧
      IsInteriorArrow σ (M.hookArrow σ AR)) ↔
        HasIrreducibleMorphism
            (σ.obj M.1.triple.u) (σ.obj M.1.z) ∨
          ¬ Injective (σ.obj M.1.triple.u) := by
  rw [M.hookArrow_isInterior_iff σ AR]
  simp only [M.rotatedAssociatedArrow_isInterior σ AR, true_and]

theorem not_interiorChannel_iff :
    ¬ (IsInteriorArrow σ (M.rotatedAssociatedArrow σ AR) ∧
      IsInteriorArrow σ (M.hookArrow σ AR)) ↔
        ¬ HasIrreducibleMorphism
            (σ.obj M.1.triple.u) (σ.obj M.1.z) ∧
          Injective (σ.obj M.1.triple.u) := by
  classical
  rw [M.interiorChannel_iff σ AR]
  simp only [not_or, not_not]

/-- The trimmed common-target occurrence assigned to an interior `M₅`
term. -/
def interiorCommonTargetPair (X : HookM5Channel.InteriorChannel σ AR) :
    AR.InteriorCommonTargetArrowPair σ :=
  ⟨(toInteriorArrow σ AR (X.1.rotatedAssociatedArrow σ AR) X.2.1,
    toInteriorArrow σ AR (X.1.hookArrow σ AR) X.2.2),
    X.1.rotatedAssociatedArrow_target_eq_hookArrow_target σ AR⟩

/-- Every interior `M₅` occurrence lies on the shifted source boundary.
If the selected arrow starts at `u`, the selected hook arrow is itself on
the first layer.  If it starts at `b`, the selected hook arrow is on the
second layer and its predecessor is the first hook arrow. -/
def interiorSourceBoundaryPair (X : HookM5Channel.InteriorChannel σ AR) :
    AR.InteriorSourceBoundaryCommonTargetArrowPair σ := by
  classical
  let N := AR.arMeshRotationData σ
  let O := N.arrowOrbitData σ
  let U := N.arrowInteriorOrbitData σ
  let H := toInteriorArrow σ AR (X.1.hookArrow σ AR) X.2.2
  refine ⟨HookM5Channel.interiorCommonTargetPair σ AR X, Or.inr ?_⟩
  by_cases h : HasIrreducibleMorphism
      (σ.obj X.1.1.triple.u) (σ.obj X.1.1.z)
  · left
    apply (N.arrowInterior_source_iff σ H).2
    simpa [H, toInteriorArrow, hookArrow, h,
      StripAdmissibleTriple.firstArrow] using X.1.a_projective σ AR
  · right
    intro hnot
    apply (N.arrowInterior_source_iff σ (U.tau ⟨H, hnot⟩).1).2
    have hval : (U.tau ⟨H, hnot⟩).1.1 =
        X.1.1.triple.firstArrow σ AR := by
      have hpred := congrArg Subtype.val
        (X.1.1.triple.secondArrow_predecessor σ AR)
      simpa [U, N, O, H, ARMeshRotationData.arrowInteriorOrbitData,
        OpConjecture.BoundaryTranslationChains.Data.interior,
        toInteriorArrow, hookArrow, h] using hpred
    rw [hval]
    simpa [StripAdmissibleTriple.firstArrow] using
      X.1.a_projective σ AR

/-- The labelled common-target pair retains the entire `M₅` extension.
The two choices of outgoing source cannot be confused: that would identify
the projective first label of one hook with the nonprojective middle label
of the other. -/
theorem commonTargetPair_injective :
    Function.Injective (commonTargetPair σ AR) := by
  classical
  intro M₁ M₂ hpair
  have hrotated := congrArg
    (fun p : CommonTargetArrowPair σ ↦ p.1.1) hpair
  have hhook := congrArg
    (fun p : CommonTargetArrowPair σ ↦ p.1.2) hpair
  change M₁.rotatedAssociatedArrow σ AR =
    M₂.rotatedAssociatedArrow σ AR at hrotated
  change M₁.hookArrow σ AR = M₂.hookArrow σ AR at hhook
  have hassociated : M₁.associatedArrow σ AR =
      M₂.associatedArrow σ AR := by
    have hsucc := congrArg
      ((AR.arMeshRotationData σ).arrowOrbitData σ).successor hrotated
    simpa only [M₁.rotatedAssociatedArrow_successor σ AR,
      M₂.rotatedAssociatedArrow_successor σ AR] using hsucc
  have hz : M₁.1.z = M₂.1.z := by
    simpa only [M₁.associatedArrow_target σ AR,
      M₂.associatedArrow_target σ AR] using congrArg
        (fun q : σ.IrreduciblePair ↦ q.1.2) hassociated
  by_cases h₁ : HasIrreducibleMorphism
      (σ.obj M₁.1.triple.u) (σ.obj M₁.1.z)
  · by_cases h₂ : HasIrreducibleMorphism
        (σ.obj M₂.1.triple.u) (σ.obj M₂.1.z)
    · have htriple := StripAdmissibleTriple.firstArrow_injective σ AR
          (by simpa [hookArrow, h₁, h₂] using hhook)
      apply Subtype.ext
      exact HookFourthExtension.ext htriple hz
    · have hau : M₁.1.triple.a = M₂.1.triple.u := by
        have hhook' : M₁.1.triple.firstArrow σ AR =
            M₂.1.triple.secondArrow σ AR := by
          simpa [hookArrow, h₁, h₂] using hhook
        exact congrArg
          (fun q : σ.IrreduciblePair ↦ q.1.1) hhook'
      exact (M₂.1.triple.u_nonprojective
        (hau ▸ M₁.a_projective σ AR)).elim
  · by_cases h₂ : HasIrreducibleMorphism
        (σ.obj M₂.1.triple.u) (σ.obj M₂.1.z)
    · have hua : M₁.1.triple.u = M₂.1.triple.a := by
        have hhook' : M₁.1.triple.secondArrow σ AR =
            M₂.1.triple.firstArrow σ AR := by
          simpa [hookArrow, h₁, h₂] using hhook
        exact congrArg
          (fun q : σ.IrreduciblePair ↦ q.1.1) hhook'
      exact (M₁.1.triple.u_nonprojective
        (hua.symm ▸ M₂.a_projective σ AR)).elim
    · have htriple := StripAdmissibleTriple.secondArrow_injective σ AR
          (by simpa [hookArrow, h₁, h₂] using hhook)
      apply Subtype.ext
      exact HookFourthExtension.ext htriple hz

theorem interiorCommonTargetPair_injective :
    Function.Injective (interiorCommonTargetPair σ AR) := by
  intro X Y h
  apply Subtype.ext
  apply commonTargetPair_injective σ AR
  have hf := congrArg (forgetInteriorCommonTarget σ AR) h
  simpa [interiorCommonTargetPair, forgetInteriorCommonTarget,
    toInteriorArrow, commonTargetPair] using hf

end HookM5Channel

end OpConjecture.IndecomposableSkeleton.FiniteARTranslationData
