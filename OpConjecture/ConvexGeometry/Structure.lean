import OpConjecture.ConvexGeometry.Compact

/-!
# The structural theorem for finitary convex geometries

This file packages the abstract conclusions used in
`paper/op_conjecture/main.tex`, Theorem `thm:infinite-convex-structure`.
The complete-lattice formulas themselves are supplied by
`ConvexGeometry.ClosedSets`; the structure below records the substantive
algebraicity, spatiality, irreducibility, compactness, and basis assertions.
-/

open Set

namespace OpConjecture.SetClosure

variable {E : Type*}

/-- The abstract, representation-independent content of the manuscript's
infinite convex-structure theorem.

`IsCompactlyGenerated` is Mathlib's name for an algebraic complete lattice.
The final two fields say that the finite extreme-point set is the unique
inclusion-minimal generating set of every compact closed set. -/
structure InfiniteConvexStructure (c : SetClosure E) : Prop where
  algebraic : IsCompactlyGenerated c.Closeds
  spatial : OpConjecture.IsSpatial c.Closeds
  completelyJoinIrreducible_iff_pointClosure :
    ∀ J : c.Closeds,
      OpConjecture.IsCompletelyJoinIrreducible J ↔
        ∃ x : E, J = c.pointClosure x
  pointClosure_injective : Function.Injective c.pointClosure
  pointClosure_compact :
    ∀ x : E, IsCompactElement (c.pointClosure x)
  compact_extremePoints_basis :
    ∀ (C : c.Closeds), IsCompactElement C →
      (c.extremePoints (C : Set E)).Finite ∧
        c.IsMinimalGenerator
          (c.extremePoints (C : Set E)) (C : Set E)
  compact_minimalGenerator_unique :
    ∀ (C : c.Closeds), IsCompactElement C → ∀ B : Set E,
      c.IsMinimalGenerator B (C : Set E) ↔
        B = c.extremePoints (C : Set E)

/-- Every finitary anti-exchange closure with closed empty set has the full
abstract infinite convex structure asserted in the manuscript. -/
theorem infiniteConvexStructure
    {c : SetClosure E}
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    (hempty : c.IsClosed ∅) :
    c.InfiniteConvexStructure where
  algebraic := isCompactlyGenerated_closeds hfin
  spatial := isSpatial_closeds hfin hae hempty
  completelyJoinIrreducible_iff_pointClosure :=
    isCompletelyJoinIrreducible_iff_eq_pointClosure hfin hae hempty
  pointClosure_injective :=
    pointClosure_injective_closeds hae hempty
  pointClosure_compact :=
    pointClosure_isCompactElement hfin
  compact_extremePoints_basis := by
    intro C hC
    exact OpConjecture.SetClosure.compact_extremePoints_basis hfin hae hC
  compact_minimalGenerator_unique := by
    intro C hC B
    exact
      compact_isMinimalGenerator_iff_eq_extremePoints hfin hae hC

/-- The finite accessibility, cover, grading, and generation conclusions used
in `cor:finite-convex-consequences`, before identifying extreme points with
the relevant module-theoretic split objects. -/
structure FiniteConvexConsequences [Finite E] (c : SetClosure E) : Prop where
  extremePoints_nonempty :
    ∀ {C : Set E}, c.IsClosed C → C.Nonempty →
      (c.extremePoints C).Nonempty
  extreme_deletion_closed :
    ∀ {C : Set E} {x : E}, c.IsClosed C →
      x ∈ c.extremePoints C → c.IsClosed (C \ {x})
  generated_by_extremePoints :
    ∀ {C : Set E}, c.IsClosed C →
      c (c.extremePoints C) = C
  cover_adds_one :
    ∀ {C D : c.Closeds}, C ⋖ D →
      ∃ x : E, x ∉ (C : Set E) ∧
        (D : Set E) = insert x (C : Set E)
  cover_cardinality :
    ∀ {C D : c.Closeds}, C ⋖ D →
      (C : Set E).ncard + 1 = (D : Set E).ncard

/-- Every finite convex geometry has the paper's finite structural
consequences. -/
theorem finiteConvexConsequences [Finite E]
    {c : SetClosure E}
    (hae : c.IsAntiExchange) (hempty : c.IsClosed ∅) :
    c.FiniteConvexConsequences where
  extremePoints_nonempty := by
    intro C hC hCne
    exact OpConjecture.SetClosure.extremePoints_nonempty
      hae hempty hC hCne
  extreme_deletion_closed := by
    intro C x hC hx
    exact
      (mem_extremePoints_iff_isClosed_sdiff_singleton hC hx.1).1 hx
  generated_by_extremePoints :=
    closure_extremePoints hae
  cover_adds_one :=
    covBy_eq_insert hae
  cover_cardinality :=
    ncard_add_one_eq_of_covBy hae

end OpConjecture.SetClosure
