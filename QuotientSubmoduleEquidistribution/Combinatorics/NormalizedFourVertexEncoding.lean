import QuotientSubmoduleEquidistribution.Combinatorics.NormalizedFourVertexLadderClassification
import Batteries.Data.BitVec.Lemmas

/-!
# Exact encoding of a four-element translation support

This file constructs the finite bit-vector code from arbitrary semantic
four-label data already equipped with an equivalence to `Fin 4`.  The
accompanying lemmas prove that edges, optional translation targets, and the
projective boundary mask decode exactly.  This separates routine encoding
transport from both the AR realization and the finite classifiers.
-/

set_option autoImplicit false
noncomputable section

namespace QuotientSubmoduleEquidistribution.NormalizedFourVertexLadderClassification

universe u

/-- Row-major bit encoding of a relation on four labels. -/
def edgeBitsOfEquiv {L : Type u} (e : L ≃ Vertex)
    (E : L → L → Prop) [DecidableRel E] : BitVec 16 :=
  BitVec.ofFnLE fun i ↦
    let xy := (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm i
    decide (E (e.symm xy.1) (e.symm xy.2))

/-- Three-bit encoding of an optional target label. -/
def encodedTargetOfEquiv {L : Type u} (e : L ≃ Vertex)
    (t : Option L) : BitVec 3 :=
  match t with
  | none => 0
  | some y => BitVec.ofNat 3 ((e y).val + 1)

/-- Encode a loopless relation and a partial translation.  The label sent to
`0` is required only later to have no translation; its field is omitted by
the normalized `Code`. -/
def codeOfEquiv {L : Type u} (e : L ≃ Vertex)
    (E : L → L → Prop) [DecidableRel E]
    (T : L → Option L) : Code where
  edges := edgeBitsOfEquiv e E
  tauOne := encodedTargetOfEquiv e (T (e.symm 1))
  tauTwo := encodedTargetOfEquiv e (T (e.symm 2))
  tauThree := encodedTargetOfEquiv e (T (e.symm 3))

/-- Encode the possible additional projective boundary labels; the label at
`0` is implicit. -/
def additionalBoundaryOfEquiv {L : Type u} (e : L ≃ Vertex)
    (B : L → Prop) [DecidablePred B] : AdditionalBoundary :=
  BitVec.ofFnLE fun i ↦
    decide (B (e.symm ⟨i.val + 1, by omega⟩))

/-- Reading the row-major relation bits recovers the original relation. -/
theorem edgeBitsOfEquiv_apply {L : Type u} (e : L ≃ Vertex)
    (E : L → L → Prop) [DecidableRel E] (x y : L) :
    (edgeBitsOfEquiv e E).getLsbD
        ((e x).val * 4 + (e y).val) = decide (E x y) := by
  let i := e x
  let j := e y
  have hx : e.symm i = x := e.symm_apply_apply x
  have hy : e.symm j = y := e.symm_apply_apply y
  change (edgeBitsOfEquiv e E).getLsbD (i.val * 4 + j.val) =
    decide (E x y)
  rw [← hx, ← hy]
  clear_value i
  clear_value j
  clear hx hy x y
  have fin_two : ∀ h : 2 < 4, (⟨2, h⟩ : Fin 4) = 2 := by
    intro h
    exact Fin.ext rfl
  have fin_three : ∀ h : 3 < 4, (⟨3, h⟩ : Fin 4) = 3 := by
    intro h
    exact Fin.ext rfl
  fin_cases i <;> fin_cases j <;>
    simp [edgeBitsOfEquiv, finProdFinEquiv] <;>
      norm_num [Fin.divNat, Fin.modNat]
  all_goals simp only [fin_two, fin_three]

/-- The translation code at an arbitrary relabelled vertex is the encoding
of its optional semantic target. -/
theorem tauCode_codeOfEquiv {L : Type u} (e : L ≃ Vertex)
    (E : L → L → Prop) [DecidableRel E]
    (T : L → Option L) (x : L)
    (hroot : T (e.symm 0) = none) :
    tauCode (codeOfEquiv e E T) (e x) =
      encodedTargetOfEquiv e (T x) := by
  let q := e x
  have hx : e.symm q = x := e.symm_apply_apply x
  change tauCode (codeOfEquiv e E T) q = encodedTargetOfEquiv e (T x)
  rw [← hx]
  clear_value q
  clear hx x
  fin_cases q <;>
    simp [codeOfEquiv, tauCode, hroot, encodedTargetOfEquiv]

/-- Equality of a nonzero encoded target is exact. -/
theorem encodedTargetOfEquiv_eq_target {L : Type u} (e : L ≃ Vertex)
    (t : Option L) (y : L) :
    (encodedTargetOfEquiv e t ==
      BitVec.ofNat 3 ((e y).val + 1)) = true ↔ t = some y := by
  cases t with
  | none =>
      let j := e y
      have hy : e.symm j = y := e.symm_apply_apply y
      rw [← hy]
      clear_value j
      clear hy y
      fin_cases j <;> simp [encodedTargetOfEquiv]
  | some z =>
      let i := e z
      let j := e y
      have hz : e.symm i = z := e.symm_apply_apply z
      have hy : e.symm j = y := e.symm_apply_apply y
      rw [← hz, ← hy]
      clear_value i
      clear_value j
      clear hz hy z y
      fin_cases i <;> fin_cases j <;> simp [encodedTargetOfEquiv]

/-- Zero is exactly the missing-target code. -/
theorem encodedTargetOfEquiv_eq_zero {L : Type u} (e : L ≃ Vertex)
    (t : Option L) :
    (encodedTargetOfEquiv e t == 0) = true ↔ t = none := by
  cases t with
  | none => simp [encodedTargetOfEquiv]
  | some z =>
      let i := e z
      have hz : e.symm i = z := e.symm_apply_apply z
      rw [← hz]
      clear_value i
      clear hz z
      fin_cases i <;> simp [encodedTargetOfEquiv]

/-- The normalized target predicate decodes to the semantic partial
translation. -/
theorem tauEq_codeOfEquiv {L : Type u} (e : L ≃ Vertex)
    (E : L → L → Prop) [DecidableRel E]
    (T : L → Option L) (x y : L)
    (hroot : T (e.symm 0) = none) :
    tauEq (codeOfEquiv e E T) (e x) (e y) = true ↔
      T x = some y := by
  rw [tauEq, tauCode_codeOfEquiv e E T x hroot]
  exact encodedTargetOfEquiv_eq_target e (T x) y

/-- The normalized missing-target predicate decodes to `none`. -/
theorem tauNone_codeOfEquiv {L : Type u} (e : L ≃ Vertex)
    (E : L → L → Prop) [DecidableRel E]
    (T : L → Option L) (x : L)
    (hroot : T (e.symm 0) = none) :
    tauNone (codeOfEquiv e E T) (e x) = true ↔ T x = none := by
  rw [tauNone, tauCode_codeOfEquiv e E T x hroot]
  exact encodedTargetOfEquiv_eq_zero e (T x)

/-- The boundary bit mask decodes to the original boundary predicate when
the implicit root is a boundary label. -/
theorem boundaryAt_additionalBoundaryOfEquiv {L : Type u}
    (e : L ≃ Vertex) (B : L → Prop) [DecidablePred B]
    (hroot : B (e.symm 0)) (x : L) :
    boundaryAt (additionalBoundaryOfEquiv e B) (e x) = true ↔ B x := by
  let i := e x
  have hx : e.symm i = x := e.symm_apply_apply x
  change boundaryAt (additionalBoundaryOfEquiv e B) i = true ↔ B x
  rw [← hx]
  clear_value i
  clear hx x
  fin_cases i <;>
    simp [boundaryAt, additionalBoundaryOfEquiv, hroot]

/-- For a loopless semantic relation, `edge` on the encoded code is exactly
that relation. -/
theorem edge_codeOfEquiv {L : Type u} (e : L ≃ Vertex)
    (E : L → L → Prop) [DecidableRel E]
    (T : L → Option L) (hirr : ∀ x, ¬ E x x) (x y : L) :
    edge (codeOfEquiv e E T) (e x) (e y) = true ↔ E x y := by
  by_cases hxy : x = y
  · subst y
    simp [edge, hirr]
  · have hexy : e x ≠ e y := fun h ↦ hxy (e.injective h)
    simp only [edge, hexy, bne_iff_ne, Bool.and_eq_true, ne_eq,
      not_false_eq_true, true_and]
    change (edgeBitsOfEquiv e E).getLsbD
        ((e x).val * 4 + (e y).val) = true ↔ E x y
    rw [edgeBitsOfEquiv_apply e E x y]
    simp

end QuotientSubmoduleEquidistribution.NormalizedFourVertexLadderClassification
