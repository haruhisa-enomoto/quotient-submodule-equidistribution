import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Boundary-arrow balance

The finite directed-multigraph calculation used after mesh rotation in the
colevel-two proof.
-/

namespace OpConjecture.BoundaryArrowBalance

universe u v

variable {Vertex : Type u} {Arrow : Type v}
  [Fintype Vertex] [Fintype Arrow]
  [DecidableEq Vertex]

/-- Number of arrows whose source lies in `U` and target lies in `W`.
The arrow type may contain parallel arrows. -/
def edgeCount (src dst : Arrow → Vertex)
    (U W : Finset Vertex) : ℕ :=
  ((Finset.univ : Finset Arrow).filter fun a ↦
    src a ∈ U ∧ dst a ∈ W).card

/-- Partition the source condition into a set and its complement. -/
theorem edgeCount_add_compl_left
    (src dst : Arrow → Vertex)
    (U W : Finset Vertex) :
    edgeCount src dst U W +
        edgeCount src dst Uᶜ W =
      edgeCount src dst Finset.univ W := by
  classical
  let A := (Finset.univ : Finset Arrow).filter fun a ↦
    src a ∈ U ∧ dst a ∈ W
  let B := (Finset.univ : Finset Arrow).filter fun a ↦
    src a ∈ Uᶜ ∧ dst a ∈ W
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    simp only [A, B, Finset.mem_filter,
      Finset.mem_univ, true_and] at haA haB
    exact (Finset.mem_compl.mp haB.1) haA.1
  have hunion :
      A ∪ B =
        (Finset.univ : Finset Arrow).filter fun a ↦
          src a ∈ (Finset.univ : Finset Vertex) ∧
            dst a ∈ W := by
    ext a
    simp only [A, B, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_compl]
    tauto
  unfold edgeCount
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- Partition the target condition into a set and its complement. -/
theorem edgeCount_add_compl_right
    (src dst : Arrow → Vertex)
    (U W : Finset Vertex) :
    edgeCount src dst U W +
        edgeCount src dst U Wᶜ =
      edgeCount src dst U Finset.univ := by
  classical
  let A := (Finset.univ : Finset Arrow).filter fun a ↦
    src a ∈ U ∧ dst a ∈ W
  let B := (Finset.univ : Finset Arrow).filter fun a ↦
    src a ∈ U ∧ dst a ∈ Wᶜ
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    simp only [A, B, Finset.mem_filter,
      Finset.mem_univ, true_and] at haA haB
    exact (Finset.mem_compl.mp haB.2) haA.2
  have hunion :
      A ∪ B =
        (Finset.univ : Finset Arrow).filter fun a ↦
          src a ∈ U ∧
            dst a ∈ (Finset.univ : Finset Vertex) := by
    ext a
    simp only [A, B, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, and_true, Finset.mem_compl]
    tauto
  unfold edgeCount
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- The colevel-two boundary calculation.

`P` and `I` model the projective and injective vertices.  The hypothesis
is the first mesh-rotation identity from the manuscript: arrows ending
away from `P` are equinumerous with arrows starting away from `I`.
The conclusion identifies the two mixed boundary counts. -/
theorem mixedBoundary_eq_of_meshRotation
    (src dst : Arrow → Vertex)
    (P I : Finset Vertex)
    (hmesh :
      edgeCount src dst Finset.univ Pᶜ =
        edgeCount src dst Iᶜ Finset.univ) :
    edgeCount src dst Iᶜ P =
      edgeCount src dst I Pᶜ := by
  have htarget :=
    edgeCount_add_compl_right
      src dst (Finset.univ : Finset Vertex) P
  have hsource :=
    edgeCount_add_compl_left
      src dst I (Finset.univ : Finset Vertex)
  have hinto_out :
      edgeCount src dst Finset.univ P =
        edgeCount src dst I Finset.univ := by
    omega
  have hintoP :=
    edgeCount_add_compl_left src dst I P
  have houtI :=
    edgeCount_add_compl_right src dst I P
  omega

end OpConjecture.BoundaryArrowBalance
