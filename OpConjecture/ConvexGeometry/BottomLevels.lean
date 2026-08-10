import OpConjecture.ConvexGeometry.LevelPolynomial

/-!
# The first two levels of a finite closure system

This file identifies levels zero and one using only the axioms of a closure
operator.  It is independent of the representation-theoretic realization.
-/

noncomputable section

namespace OpConjecture.SetClosure

open Set

variable {E : Type*}

/-- Points whose singleton is closed. -/
def ClosedSingletons (c : OpConjecture.SetClosure E) :=
  {x : E // c.IsClosed {x}}

/--
Closed singleton points are exactly the closed sets of cardinality one.
This equivalence does not require the whole ground type to be finite.
-/
def closedSingletonEquivLevelOne (c : OpConjecture.SetClosure E) :
    ClosedSingletons c ≃
      {C : c.Closeds // (C : Set E).ncard = 1} :=
  Equiv.ofBijective
    (fun x ↦
      ⟨⟨{x.1}, x.2⟩, by simp⟩)
    (by
      classical
      constructor
      · intro x y hxy
        apply Subtype.ext
        have hsets :
            ({x.1} : Set E) = {y.1} := by
          exact congrArg
            (fun C : {C : c.Closeds // (C : Set E).ncard = 1} ↦
              (C.1 : Set E)) hxy
        exact Set.singleton_eq_singleton_iff.mp hsets
      · intro C
        obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp C.2
        refine
          ⟨⟨x, by
              rw [← hx]
              exact C.1.property⟩,
            ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact hx.symm)

/-- The level-one count is the number of closed singleton points. -/
theorem levelCount_one_eq_natCard_closedSingletons
    [Finite E] (c : OpConjecture.SetClosure E) :
    c.levelCount 1 = Nat.card (ClosedSingletons c) := by
  unfold OpConjecture.SetClosure.levelCount
  calc
    {C : c.Closeds | (C : Set E).ncard = 1}.ncard =
        Nat.card {C : c.Closeds // (C : Set E).ncard = 1} :=
      (Nat.card_coe_set_eq _).symm
    _ = Nat.card (ClosedSingletons c) :=
      Nat.card_congr (closedSingletonEquivLevelOne c).symm

/-- If the empty set is closed, level zero consists of it alone. -/
theorem levelCount_zero_eq_one_of_isClosed_empty
    [Finite E] (c : OpConjecture.SetClosure E)
    (hempty : c.IsClosed ∅) :
    c.levelCount 0 = 1 := by
  classical
  unfold OpConjecture.SetClosure.levelCount
  have hlevel :
      {C : c.Closeds | (C : Set E).ncard = 0} =
        ({⟨∅, hempty⟩} : Set c.Closeds) := by
    ext C
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hC
      apply Subtype.ext
      exact (Set.ncard_eq_zero).mp hC
    · rintro rfl
      simp
  rw [hlevel]
  simp

end OpConjecture.SetClosure
