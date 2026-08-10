import OpConjecture.RadicalSquareZero.OriginalNonsimpleClosure
import OpConjecture.RepresentationTheory.LevelThreeNonUniserialShapes

/-!
# Removing selected simples from separated-side quotient generation

For any indecomposable skeleton labeled by nonsimples and two copies of
simple objects, adjoining either simple copy to a support cannot create a new
nonsimple quotient.  Thus all separated-side pointwise closure laws reduce
to quotient generation from the nonsimple support alone.

This reduction is purely categorical.  The remaining square-zero input is
the comparison of those nonsimple-only closures with the original top trace,
and the distinction between the covered and free simple copies.
-/

set_option autoImplicit false

noncomputable section

open Set
open CategoryTheory

namespace OpConjecture.RadicalSquareZero

open RadicalSquareZeroCombinatorics.CoreFamily.TopCoverage

universe u v w x y

variable {R : Type u} [Ring R] [IsNoetherianRing R]
variable {Nonsimple : Type x} {Vertex : Type y}
  [Fintype Nonsimple] [Fintype Vertex]
  {tau : IndecomposableSkeleton.{u, max x y, w} R
    (Nonsimple ⊕ (Vertex ⊕ Vertex))}

/-- The two separated vertex copies are genuinely simple objects. -/
structure SeparatedSimpleLabelData
    (tau : IndecomposableSkeleton.{u, max x y, w} R
      (Nonsimple ⊕ (Vertex ⊕ Vertex))) where
  covered_simple (v : Vertex) :
    Simple (tau.obj (Sum.inr (Sum.inl v)))
  free_simple (v : Vertex) :
    Simple (tau.obj (Sum.inr (Sum.inr v)))

namespace SeparatedSimpleLabelData

/-- The separated support on a finite set of nonsimple labels. -/
def nonsimpleSupport (C : Finset Nonsimple) :
    Set (Nonsimple ⊕ (Vertex ⊕ Vertex)) :=
  Sum.inl '' (C : Set Nonsimple)

/-- The support on the covered simple copy. -/
def coveredSimpleSupport (U : Finset Vertex) :
    Set (Nonsimple ⊕ (Vertex ⊕ Vertex)) :=
  (Sum.inr ∘ Sum.inl) '' (U : Set Vertex)

/-- The support on the free simple copy. -/
def freeSimpleSupport (U : Finset Vertex) :
    Set (Nonsimple ⊕ (Vertex ⊕ Vertex)) :=
  (Sum.inr ∘ Sum.inr) '' (U : Set Vertex)

/-- Both selected simple parts of a separated support. -/
def simpleSupport (U W : Finset Vertex) :
    Set (Nonsimple ⊕ (Vertex ⊕ Vertex)) :=
  coveredSimpleSupport (Nonsimple := Nonsimple) U ∪
    freeSimpleSupport (Nonsimple := Nonsimple) W

omit [Fintype Nonsimple] [Fintype Vertex] in
@[simp]
theorem mem_nonsimpleSupport_iff
    (C : Finset Nonsimple) (z : Nonsimple) :
    Sum.inl z ∈ nonsimpleSupport (Vertex := Vertex) C ↔ z ∈ C := by
  simp [nonsimpleSupport]

omit [Fintype Nonsimple] [Fintype Vertex] in
@[simp]
theorem mem_coveredSimpleSupport_iff
    (U : Finset Vertex) (v : Vertex) :
    Sum.inr (Sum.inl v) ∈
        coveredSimpleSupport (Nonsimple := Nonsimple) U ↔
      v ∈ U := by
  simp [coveredSimpleSupport]

omit [Fintype Nonsimple] [Fintype Vertex] in
@[simp]
theorem mem_freeSimpleSupport_iff
    (U : Finset Vertex) (v : Vertex) :
    Sum.inr (Sum.inr v) ∈
        freeSimpleSupport (Nonsimple := Nonsimple) U ↔
      v ∈ U := by
  simp [freeSimpleSupport]

/-- Every separated support is its nonsimple part union its two simple
parts. -/
theorem nonsimpleSupport_union_simpleSupport_parts
    (T : Set (Nonsimple ⊕ (Vertex ⊕ Vertex))) :
    nonsimpleSupport (Vertex := Vertex) (bNonsimplePart T) ∪
        simpleSupport (Nonsimple := Nonsimple)
          (bCoveredSimplePart T) (bFreeSimplePart T) = T := by
  ext z
  rcases z with z | (v | v)
  · simp [nonsimpleSupport, simpleSupport, coveredSimpleSupport,
      freeSimpleSupport]
  · simp [nonsimpleSupport, simpleSupport, coveredSimpleSupport,
      freeSimpleSupport]
  · simp [nonsimpleSupport, simpleSupport, coveredSimpleSupport,
      freeSimpleSupport]

omit [Fintype Nonsimple] [Fintype Vertex] in
/-- Every object in the combined separated simple support is simple. -/
theorem simple_of_mem_simpleSupport
    (D : SeparatedSimpleLabelData tau)
    (U W : Finset Vertex) {i : Nonsimple ⊕ (Vertex ⊕ Vertex)}
    (hi : i ∈ simpleSupport (Nonsimple := Nonsimple) U W) :
    Simple (tau.obj i) := by
  rcases hi with hi | hi
  · rcases hi with ⟨v, -, rfl⟩
    exact D.covered_simple v
  · rcases hi with ⟨v, -, rfl⟩
    exact D.free_simple v

/-- Quotient closure of an arbitrary separated support is the closure of its
nonsimple part together with the literally selected simple labels. -/
theorem qClosure_eq_nonsimpleClosure_union_simpleSupport
    (D : SeparatedSimpleLabelData tau)
    (T : Set (Nonsimple ⊕ (Vertex ⊕ Vertex))) :
    tau.qClosure T =
      tau.qClosure
          (nonsimpleSupport (Vertex := Vertex) (bNonsimplePart T)) ∪
        simpleSupport (Nonsimple := Nonsimple)
          (bCoveredSimplePart T) (bFreeSimplePart T) := by
  let S₀ := nonsimpleSupport (Vertex := Vertex) (bNonsimplePart T)
  let U₀ := simpleSupport (Nonsimple := Nonsimple)
    (bCoveredSimplePart T) (bFreeSimplePart T)
  have hparts : S₀ ∪ U₀ = T :=
    nonsimpleSupport_union_simpleSupport_parts T
  calc
    tau.qClosure T = tau.qClosure (S₀ ∪ U₀) :=
      congrArg tau.qClosure hparts.symm
    _ = tau.qClosure S₀ ∪ U₀ :=
      tau.qClosure_union_eq_closure_union_of_forall_simple
        (fun i hi ↦ D.simple_of_mem_simpleSupport _ _ hi)
    _ = _ := rfl

/-- A nonsimple separated label is generated exactly when it is generated by
the selected nonsimple labels. -/
theorem nonsimple_mem_qClosure_iff
    (D : SeparatedSimpleLabelData tau)
    (T : Set (Nonsimple ⊕ (Vertex ⊕ Vertex))) (z : Nonsimple) :
    Sum.inl z ∈ tau.qClosure T ↔
      Sum.inl z ∈ tau.qClosure
        (nonsimpleSupport (Vertex := Vertex) (bNonsimplePart T)) := by
  rw [D.qClosure_eq_nonsimpleClosure_union_simpleSupport T]
  simp [simpleSupport, coveredSimpleSupport, freeSimpleSupport]

/-- Covered-simple membership reduces to literal selection or generation by
the selected nonsimple labels. -/
theorem covered_simple_mem_qClosure_iff
    (D : SeparatedSimpleLabelData tau)
    (T : Set (Nonsimple ⊕ (Vertex ⊕ Vertex))) (v : Vertex) :
    Sum.inr (Sum.inl v) ∈ tau.qClosure T ↔
      Sum.inr (Sum.inl v) ∈ T ∨
        Sum.inr (Sum.inl v) ∈ tau.qClosure
          (nonsimpleSupport (Vertex := Vertex) (bNonsimplePart T)) := by
  rw [D.qClosure_eq_nonsimpleClosure_union_simpleSupport T]
  simp [simpleSupport, coveredSimpleSupport, freeSimpleSupport, or_comm]

/-- Free-simple membership reduces to literal selection or generation by the
selected nonsimple labels; square-zero generatedness will eliminate the
second alternative. -/
theorem free_simple_mem_qClosure_iff
    (D : SeparatedSimpleLabelData tau)
    (T : Set (Nonsimple ⊕ (Vertex ⊕ Vertex))) (v : Vertex) :
    Sum.inr (Sum.inr v) ∈ tau.qClosure T ↔
      Sum.inr (Sum.inr v) ∈ T ∨
        Sum.inr (Sum.inr v) ∈ tau.qClosure
          (nonsimpleSupport (Vertex := Vertex) (bNonsimplePart T)) := by
  rw [D.qClosure_eq_nonsimpleClosure_union_simpleSupport T]
  simp [simpleSupport, coveredSimpleSupport, freeSimpleSupport, or_comm]

end SeparatedSimpleLabelData

namespace OriginalNonsimpleLabelData

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]
variable [IsSemisimpleRing S]
variable [IsNoetherianRing (TrivSqZeroExt S J)]
variable [DecidableEq Nonsimple] [DecidableEq Vertex]
variable
  {sigma : IndecomposableSkeleton.{max u v, max x y, w}
    (TrivSqZeroExt S J) (Nonsimple ⊕ Vertex)}

/-- Build the paired closure interface after the generic simple-source
reduction.  Only three nonsimple-support comparisons remain: common
nonsimple generation, covered-top generation, and exclusion of the free
simple copy. -/
noncomputable def toPairedClosureMembershipOfSeparatedSimple
    (D : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    {R : Type*} [Ring R] [IsNoetherianRing R]
    (tau : IndecomposableSkeleton.{_, max x y, _} R
      (Nonsimple ⊕ (Vertex ⊕ Vertex)))
    (E : SeparatedSimpleLabelData tau)
    (b_nonsimple_core :
      ∀ (C : Finset Nonsimple) (z : Nonsimple),
        Sum.inl z ∈ tau.qClosure
            (SeparatedSimpleLabelData.nonsimpleSupport
              (Vertex := Vertex) C) ↔
          Generates (sigma := sigma) C z)
    (b_covered_core :
      ∀ (C : Finset Nonsimple) (v : Vertex),
        Sum.inr (Sum.inl v) ∈ tau.qClosure
            (SeparatedSimpleLabelData.nonsimpleSupport
              (Vertex := Vertex) C) ↔
          v ∈ forcedTop (sigma := sigma) C)
    (b_free_core :
      ∀ (C : Finset Nonsimple) (v : Vertex),
        Sum.inr (Sum.inr v) ∉ tau.qClosure
          (SeparatedSimpleLabelData.nonsimpleSupport
            (Vertex := Vertex) C)) :
    PairedClosureMembership sigma.qClosure tau.qClosure :=
  D.toPairedClosureMembership
    (b_nonsimple_mem := fun T z ↦
      (E.nonsimple_mem_qClosure_iff T z).trans
        (b_nonsimple_core (bNonsimplePart T) z))
    (b_covered_simple_mem := fun T v ↦
      (E.covered_simple_mem_qClosure_iff T v).trans <| by
        rw [b_covered_core (bNonsimplePart T) v])
    (b_free_simple_mem := fun T v ↦
      (E.free_simple_mem_qClosure_iff T v).trans <| by
        simp [b_free_core (bNonsimplePart T) v])

end OriginalNonsimpleLabelData

end OpConjecture.RadicalSquareZero
