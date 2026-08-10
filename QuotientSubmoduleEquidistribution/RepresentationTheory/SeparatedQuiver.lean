import QuotientSubmoduleEquidistribution.Foundation.RepresentationTheory.Quiver.Acyclic.PathAlgebra
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The separated quiver
-/

set_option autoImplicit false

namespace QuotientSubmoduleEquidistribution.SeparatedQuiver

open Quiver

universe u v w

/-- The two copies of the vertices in a separated quiver. -/
abbrev Vertex (V : Type u) := V ⊕ V

/-- The separated quiver has one arrow `i⁺ ⟶ j⁻` for every original
arrow `i ⟶ j`, and no other arrows. -/
instance separatedQuiver {V : Type u} [Quiver.{v} V] :
    Quiver.{v} (Vertex V) where
  Hom a b :=
    match a, b with
    | Sum.inl i, Sum.inr j => i ⟶ j
    | _, _ => PEmpty

instance separatedArrowFinite {V : Type u} [Quiver.{v} V]
    [∀ i j : V, Finite (i ⟶ j)] :
    ∀ a b : Vertex V, Finite (a ⟶ b)
  | Sum.inl _, Sum.inl _ => inferInstanceAs (Finite PEmpty)
  | Sum.inl i, Sum.inr j => inferInstanceAs (Finite (i ⟶ j))
  | Sum.inr _, Sum.inl _ => inferInstanceAs (Finite PEmpty)
  | Sum.inr _, Sum.inr _ => inferInstanceAs (Finite PEmpty)

noncomputable instance separatedVertexFinite {V : Type u} [Finite V] :
    Finite (Vertex V) := by
  letI : Fintype V := Fintype.ofFinite V
  exact Finite.intro (Fintype.equivFin (V ⊕ V))

/-- The height is zero on the `+` copy and one on the `-` copy. -/
def height {V : Type u} : Vertex V → ℕ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- Every separated-quiver arrow strictly increases height. -/
theorem height_lt_of_arrow {V : Type u} [Quiver.{v} V]
    {a b : Vertex V} (e : a ⟶ b) : height a < height b := by
  cases a with
  | inl i =>
      cases b with
      | inl j => exact PEmpty.elim e
      | inr j => exact Nat.zero_lt_one
  | inr i =>
      cases b with
      | inl j => exact PEmpty.elim e
      | inr j => exact PEmpty.elim e

/-- Height is nondecreasing along every separated-quiver path. -/
theorem height_le_of_path {V : Type u} [Quiver.{v} V]
    {a b : Vertex V} (p : Path a b) : height a ≤ height b := by
  induction p with
  | nil => exact le_rfl
  | cons p e ih => exact ih.trans (height_lt_of_arrow e).le

/-- Two separated-quiver arrows cannot be composed. -/
theorem no_composable_arrows {V : Type u} [Quiver.{v} V]
    {a b c : Vertex V} (f : a ⟶ b) (e : b ⟶ c) : False := by
  cases b with
  | inl i =>
      cases a with
      | inl j => exact PEmpty.elim f
      | inr j => exact PEmpty.elim f
  | inr i =>
      cases c with
      | inl j => exact PEmpty.elim e
      | inr j => exact PEmpty.elim e

/-- The separated quiver is acyclic, without any hypothesis on the original
quiver. -/
theorem isAcyclic {V : Type u} [Quiver.{v} V] :
    QuotientSubmoduleEquidistribution.Foundation.Quiver.IsAcyclic (Vertex V) := by
  intro a p
  cases p with
  | nil => rfl
  | cons p e =>
      exact False.elim
        ((Nat.not_lt_of_ge (height_le_of_path p))
          (height_lt_of_arrow e))

/-- Every path in the separated quiver has length at most one. -/
theorem path_length_le_one {V : Type u} [Quiver.{v} V]
    {a b : Vertex V} (p : Path a b) : p.length ≤ 1 := by
  cases p with
  | nil => simp
  | @cons b c p e =>
      cases p with
      | nil => simp
      | @cons d b p f =>
          exact False.elim (no_composable_arrows f e)

/-- The unoriented graph underlying the separated quiver, retaining isolated
vertices. -/
def underlyingGraph {V : Type u} [Quiver.{v} V] :
    SimpleGraph (Vertex V) where
  Adj a b := Nonempty (a ⟶ b) ∨ Nonempty (b ⟶ a)
  symm :=
    ⟨by
      intro a b h
      exact h.symm⟩
  loopless :=
    ⟨by
      intro a h
      rcases h with h | h
      · exact (Nat.lt_irrefl (height a)) (height_lt_of_arrow h.some)
      · exact (Nat.lt_irrefl (height a)) (height_lt_of_arrow h.some)⟩

/-- Exchanging the `+` and `-` copies identifies the vertices of the
separated quiver of the opposite quiver with those of the original
separated quiver. -/
def oppositeVertexEquiv {V : Type u} : Vertex Vᵒᵖ ≃ Vertex V where
  toFun
    | Sum.inl i => Sum.inr i.unop
    | Sum.inr i => Sum.inl i.unop
  invFun
    | Sum.inl i => Sum.inr (Opposite.op i)
    | Sum.inr i => Sum.inl (Opposite.op i)
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-- The underlying graphs of the separated quivers of a quiver and its
opposite are canonically isomorphic by swapping the two vertex copies. -/
def underlyingGraphOppositeIso {V : Type u} [Quiver.{v} V] :
    (underlyingGraph (V := Vᵒᵖ)) ≃g underlyingGraph (V := V) where
  __ := oppositeVertexEquiv
  map_rel_iff' := by
    intro a b
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            change (Nonempty PEmpty ∨ Nonempty PEmpty) ↔
              (Nonempty PEmpty ∨ Nonempty PEmpty)
            simp
        | inr j =>
            change (Nonempty PEmpty ∨ Nonempty (j.unop ⟶ i.unop)) ↔
              (Nonempty ((j.unop ⟶ i.unop)ᵒᵖ) ∨ Nonempty PEmpty)
            constructor
            · intro h
              rcases h with h | h
              · exact PEmpty.elim h.some
              · obtain ⟨e⟩ := h
                exact Or.inl ⟨Opposite.op e⟩
            · intro h
              rcases h with h | h
              · obtain ⟨e⟩ := h
                exact Or.inr ⟨e.unop⟩
              · exact PEmpty.elim h.some
    | inr i =>
        cases b with
        | inl j =>
            change (Nonempty (i.unop ⟶ j.unop) ∨ Nonempty PEmpty) ↔
              (Nonempty PEmpty ∨ Nonempty ((i.unop ⟶ j.unop)ᵒᵖ))
            constructor
            · intro h
              rcases h with h | h
              · obtain ⟨e⟩ := h
                exact Or.inr ⟨Opposite.op e⟩
              · exact PEmpty.elim h.some
            · intro h
              rcases h with h | h
              · exact PEmpty.elim h.some
              · obtain ⟨e⟩ := h
                exact Or.inl ⟨e.unop⟩
        | inr j =>
            change (Nonempty PEmpty ∨ Nonempty PEmpty) ↔
              (Nonempty PEmpty ∨ Nonempty PEmpty)
            simp

/-- Over a division ring, the path algebra of a finite separated quiver with
finite arrow types is finite-dimensional. -/
theorem finiteDimensional_pathAlgebra
    (k : Type w) (V : Type u) [DivisionRing k] [Quiver.{v} V]
    [Finite V] [∀ i j : V, Finite (i ⟶ j)] :
    FiniteDimensional k (QuotientSubmoduleEquidistribution.Foundation.pathAlgebra k (Vertex V)) :=
  QuotientSubmoduleEquidistribution.Foundation.finiteDimensional_pathAlgebra_of_isAcyclic
    k (Vertex V) isAcyclic

end QuotientSubmoduleEquidistribution.SeparatedQuiver
