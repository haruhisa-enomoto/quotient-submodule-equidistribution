import QuotientSubmoduleEquidistribution.RepresentationTheory.PiRingModule
import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtOpposite
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The separated graph of a coordinate bimodule

For a bimodule `J` over the coordinate algebra `V → K`, an arrow from `i`
to `j` is present when the `(j,i)` Peirce corner of `J` is nonzero.  The
associated separated graph has two copies of `V`, with an edge from `i⁺` to
`j⁻` for every nonzero arrow corner.  Exchanging the left and right actions
on `J` reverses arrows, and swapping the two vertex copies gives a canonical
graph isomorphism.
-/

set_option autoImplicit false

noncomputable section

open scoped RightActions

namespace QuotientSubmoduleEquidistribution.SeparatedBimoduleGraph

open QuotientSubmoduleEquidistribution.TrivSqZeroExtOpposite

universe u v w

variable {K : Type u} {V : Type w} {J : Type v}
variable [Field K] [Fintype V] [DecidableEq V]
variable [AddCommGroup J]
variable [Module (V → K) J] [Module (V → K)ᵐᵒᵖ J]
variable [SMulCommClass (V → K) (V → K)ᵐᵒᵖ J]

/-- The `(target, source)` Peirce corner of the coordinate bimodule is
nonzero. -/
def HasArrow
    (K₀ : Type u) (V₀ : Type w) (J₀ : Type v)
    [Field K₀] [Fintype V₀] [DecidableEq V₀]
    [AddCommGroup J₀]
    [Module (V₀ → K₀) J₀] [Module (V₀ → K₀)ᵐᵒᵖ J₀]
    [SMulCommClass (V₀ → K₀) (V₀ → K₀)ᵐᵒᵖ J₀]
    (i j : V₀) : Prop :=
  ∃ x : J₀,
    PiRingModule.coordinateIdempotent K₀ V₀ j • x = x ∧
      x <• PiRingModule.coordinateIdempotent K₀ V₀ i = x ∧ x ≠ 0

/-- The separated graph of a coordinate bimodule, including both copies of
every isolated vertex. -/
def graph
    (K₀ : Type u) (V₀ : Type w) (J₀ : Type v)
    [Field K₀] [Fintype V₀] [DecidableEq V₀]
    [AddCommGroup J₀]
    [Module (V₀ → K₀) J₀] [Module (V₀ → K₀)ᵐᵒᵖ J₀]
    [SMulCommClass (V₀ → K₀) (V₀ → K₀)ᵐᵒᵖ J₀] :
    SimpleGraph (V₀ ⊕ V₀) where
  Adj a b :=
    match a, b with
    | Sum.inl i, Sum.inr j => HasArrow K₀ V₀ J₀ i j
    | Sum.inr j, Sum.inl i => HasArrow K₀ V₀ J₀ i j
    | _, _ => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> simp_all⟩
  loopless := ⟨by
    intro a
    cases a <;> exact id⟩

/-- Reversing the bimodule actions reverses the source and target of every
nonzero Peirce corner. -/
theorem reversed_hasArrow_iff (i j : V) :
    HasArrow K V (ReversedBimodule (V → K) J) i j ↔
      HasArrow K V J j i := by
  constructor
  · rintro ⟨x, hxTarget, hxSource, hx0⟩
    refine ⟨x.val, ?_, ?_, ?_⟩
    · exact congrArg ReversedBimodule.val hxSource
    · exact congrArg ReversedBimodule.val hxTarget
    · intro hzero
      apply hx0
      apply ReversedBimodule.ext'
      change x.val = (0 : J)
      exact hzero
  · rintro ⟨x, hxTarget, hxSource, hx0⟩
    refine ⟨ReversedBimodule.mk x, ?_, ?_, ?_⟩
    · apply ReversedBimodule.ext'
      exact hxSource
    · apply ReversedBimodule.ext'
      exact hxTarget
    · intro hzero
      apply hx0
      exact congrArg ReversedBimodule.val hzero

/-- Swap the positive and negative copies of the vertex set. -/
def swapVertexEquiv : (V ⊕ V) ≃ (V ⊕ V) where
  toFun
    | Sum.inl i => Sum.inr i
    | Sum.inr i => Sum.inl i
  invFun
    | Sum.inl i => Sum.inr i
    | Sum.inr i => Sum.inl i
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-- The separated graphs for a bimodule and for the bimodule with exchanged
actions are canonically isomorphic. -/
def reversedGraphIso :
    graph K V (ReversedBimodule (V → K) J) ≃g
      graph K V J where
  __ := swapVertexEquiv (V := V)
  map_rel_iff' := by
    intro a b
    cases a with
    | inl i =>
        cases b with
        | inl j => rfl
        | inr j =>
            exact (reversed_hasArrow_iff (K := K) (J := J) i j).symm
    | inr i =>
        cases b with
        | inl j =>
            exact (reversed_hasArrow_iff (K := K) (J := J) j i).symm
        | inr j => rfl

end QuotientSubmoduleEquidistribution.SeparatedBimoduleGraph
