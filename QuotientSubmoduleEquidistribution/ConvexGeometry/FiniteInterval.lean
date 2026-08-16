import QuotientSubmoduleEquidistribution.ConvexGeometry.Structure

/-!
# Finite intervals in finitary convex geometries

This file supplies the literal arbitrary-ground-set interval accessibility
statement from `cor:finite-interval-chain` in the frozen OP paper.  Only the
difference of the two closed sets is assumed finite.
-/

open Set

namespace QuotientSubmoduleEquidistribution.SetClosure

variable {E : Type*} {c : SetClosure E}

/-- Contract a closure operator to the finite interval from `C` to `D`.
The ground type consists of the points of `D \ C`; a subset is closed by
first adjoining the fixed lower set `C` and then applying the ambient
closure. -/
def intervalClosure (c : SetClosure E) (C D : Set E) :
    SetClosure ↥(D \ C) where
  toFun S := {x | x.1 ∈ c (C ∪ Subtype.val '' S)}
  monotone' := by
    intro S T hST x hx
    apply c.monotone _ hx
    rintro z (hzC | ⟨y, hyS, rfl⟩)
    · exact Or.inl hzC
    · exact Or.inr ⟨y, hST hyS, rfl⟩
  le_closure' := by
    intro S x hx
    exact c.le_closure _ (Or.inr ⟨x, hx, rfl⟩)
  idempotent' := by
    intro S
    apply Set.Subset.antisymm
    · intro x hx
      apply c.closure_min _ (c.isClosed_closure _) hx
      rintro z (hzC | ⟨y, hy, rfl⟩)
      · exact c.le_closure _ (Or.inl hzC)
      · exact hy
    · intro x hx
      apply c.monotone _ hx
      intro z hz
      rcases hz with hzC | ⟨y, hy, rfl⟩
      · exact Or.inl hzC
      · exact Or.inr ⟨y, c.le_closure _ (Or.inr ⟨y, hy, rfl⟩), rfl⟩

@[simp]
theorem mem_intervalClosure {C D : Set E} {S : Set ↥(D \ C)}
    {x : ↥(D \ C)} :
    x ∈ c.intervalClosure C D S ↔
      x.1 ∈ c (C ∪ Subtype.val '' S) :=
  Iff.rfl

/-- Closed subsets of the contracted interval give ambient closed sets after
the fixed lower set is reattached. -/
theorem isClosed_union_image_of_intervalClosed
    {C D : Set E} (hD : c.IsClosed D) (hCD : C ⊆ D)
    {S : Set ↥(D \ C)}
    (hS : (c.intervalClosure C D).IsClosed S) :
    c.IsClosed (C ∪ Subtype.val '' S) := by
  rw [ClosureOperator.isClosed_iff]
  apply Set.Subset.antisymm
  · intro z hz
    have hzD : z ∈ D := by
      apply c.closure_min _ hD hz
      rintro y (hyC | ⟨x, -, rfl⟩)
      · exact hCD hyC
      · exact x.2.1
    by_cases hzC : z ∈ C
    · exact Or.inl hzC
    · let x : ↥(D \ C) := ⟨z, hzD, hzC⟩
      have hx : x ∈ c.intervalClosure C D S := hz
      rw [hS.closure_eq] at hx
      exact Or.inr ⟨x, hx, rfl⟩
  · exact c.le_closure _

/-- Conversely, an ambient closed set of the form `C ∪ image S` gives a
closed subset of the contracted interval. -/
theorem intervalClosed_of_union_image_isClosed
    {C D : Set E} {S : Set ↥(D \ C)}
    (hS : c.IsClosed (C ∪ Subtype.val '' S)) :
    (c.intervalClosure C D).IsClosed S := by
  rw [ClosureOperator.isClosed_iff]
  apply Set.Subset.antisymm
  · intro x hx
    change x.1 ∈ c (C ∪ Subtype.val '' S) at hx
    rw [hS.closure_eq] at hx
    have hxbase : x.1 ∈ C ∪ Subtype.val '' S := hx
    rcases hxbase with hxC | ⟨y, hy, hyx⟩
    · exact False.elim (x.2.2 hxC)
    · simpa using Subtype.ext hyx ▸ hy
  · exact (c.intervalClosure C D).le_closure _

/-- The contracted interval inherits anti-exchange from the ambient closure. -/
theorem intervalClosure_isAntiExchange
    {C D : Set E} (hae : c.IsAntiExchange)
    (hD : c.IsClosed D) (hCD : C ⊆ D) :
    (c.intervalClosure C D).IsAntiExchange := by
  intro K x y hK hxK hyK hxy hx
  have hbase : c.IsClosed (C ∪ Subtype.val '' K) :=
    isClosed_union_image_of_intervalClosed hD hCD hK
  have hxbase : x.1 ∉ C ∪ Subtype.val '' K := by
    rintro (hxC | ⟨z, hzK, hzx⟩)
    · exact x.2.2 hxC
    · apply hxK
      simpa using Subtype.ext hzx ▸ hzK
  have hybase : y.1 ∉ C ∪ Subtype.val '' K := by
    rintro (hyC | ⟨z, hzK, hzy⟩)
    · exact y.2.2 hyC
    · apply hyK
      simpa using Subtype.ext hzy ▸ hzK
  have hxyval : x.1 ≠ y.1 := fun h ↦ hxy (Subtype.ext h)
  have hinsert (z : ↥(D \ C)) :
      C ∪ Subtype.val '' (insert z K) =
        insert z.1 (C ∪ Subtype.val '' K) := by
    rw [Set.image_insert_eq, Set.union_insert]
  have hx' : x.1 ∈ c (insert y.1 (C ∪ Subtype.val '' K)) := by
    rw [← hinsert y]
    exact hx
  have hy' := hae hbase hxbase hybase hxyval hx'
  rw [← hinsert x] at hy'
  exact hy'

/-- The empty contracted support is closed when the lower endpoint is. -/
theorem intervalClosure_empty_closed
    {C D : Set E} (hC : c.IsClosed C) :
    (c.intervalClosure C D).IsClosed ∅ := by
  apply intervalClosed_of_union_image_isClosed
  simpa using hC

/-- The full contracted support is closed when the upper endpoint is. -/
theorem intervalClosure_univ_closed
    {C D : Set E} (hD : c.IsClosed D) (hCD : C ⊆ D) :
    (c.intervalClosure C D).IsClosed Set.univ := by
  apply intervalClosed_of_union_image_isClosed
  convert hD using 1
  ext x
  constructor
  · rintro (hxC | ⟨y, -, rfl⟩)
    · exact hCD hxC
    · exact y.2.1
  · intro hxD
    by_cases hxC : x ∈ C
    · exact Or.inl hxC
    · exact Or.inr ⟨⟨x, hxD, hxC⟩, Set.mem_univ _, rfl⟩

/-- A proper finite interval has a legal first deletion, without assuming
that the ambient ground type is finite. -/
theorem exists_closed_sdiff_singleton_between_of_finite_sdiff
    (_hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    {C D : Set E} (hC : c.IsClosed C) (hD : c.IsClosed D)
    (hCD : C ⊂ D) (hDCfin : (D \ C).Finite) :
    ∃ x : E, x ∈ D \ C ∧ c.IsClosed (D \ {x}) ∧ C ⊆ D \ {x} := by
  classical
  letI : Fintype ↥(D \ C) := hDCfin.fintype
  let d := c.intervalClosure C D
  have hdAE : d.IsAntiExchange :=
    intervalClosure_isAntiExchange hae hD hCD.subset
  have hdEmpty : d.IsClosed ∅ := intervalClosure_empty_closed hC
  have hdUniv : d.IsClosed Set.univ :=
    intervalClosure_univ_closed hD hCD.subset
  obtain ⟨z, hzD, hzC⟩ := Set.exists_of_ssubset hCD
  let z' : ↥(D \ C) := ⟨z, hzD, hzC⟩
  have hstrict : (∅ : Set ↥(D \ C)) ⊂ Set.univ := by
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨Set.empty_subset _, ?_⟩
    intro h
    have : z' ∈ (∅ : Set ↥(D \ C)) := h ▸ Set.mem_univ z'
    exact this
  obtain ⟨x, -, hdel, -⟩ :=
    exists_closed_sdiff_singleton_between hdAE hdEmpty hdUniv hstrict
  have hbase : c.IsClosed
      (C ∪ Subtype.val '' ((Set.univ : Set ↥(D \ C)) \ {x})) :=
    isClosed_union_image_of_intervalClosed hD hCD.subset hdel
  have heq :
      C ∪ Subtype.val '' ((Set.univ : Set ↥(D \ C)) \ {x}) =
        D \ {x.1} := by
    ext y
    constructor
    · rintro (hyC | ⟨w, ⟨-, hwx⟩, rfl⟩)
      · exact ⟨hCD.subset hyC, fun hyx ↦ x.2.2 (hyx ▸ hyC)⟩
      · exact ⟨w.2.1, fun h ↦ hwx (Subtype.ext h)⟩
    · rintro ⟨hyD, hyx⟩
      by_cases hyC : y ∈ C
      · exact Or.inl hyC
      · exact Or.inr ⟨⟨y, hyD, hyC⟩,
          ⟨Set.mem_univ _, fun h ↦ hyx (congrArg Subtype.val h)⟩, rfl⟩
  refine ⟨x.1, x.2, heq ▸ hbase, ?_⟩
  intro y hyC
  exact ⟨hCD.subset hyC, fun hyx ↦ x.2.2 (hyx ▸ hyC)⟩

/-- A finite deletion chain from the upper closed set down to the lower one.
The `delete` constructor records the next point in the paper's ordering. -/
inductive FiniteIntervalDeletionChain (c : SetClosure E) (C : Set E) :
    Set E → Prop
  | refl : FiniteIntervalDeletionChain c C C
  | delete {D : Set E} (x : E) (hx : x ∈ D \ C)
      (hclosed : c.IsClosed (D \ {x}))
      (tail : FiniteIntervalDeletionChain c C (D \ {x})) :
      FiniteIntervalDeletionChain c C D

/-- Literal finite-interval accessibility: if `D \ C` is finite, one can
pass from `D` to `C` by successively deleting extreme points while remaining
closed at every step. -/
theorem finiteIntervalDeletionChain
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    {C D : Set E} (hC : c.IsClosed C) (hD : c.IsClosed D)
    (hCD : C ⊆ D) (hDCfin : (D \ C).Finite) :
    FiniteIntervalDeletionChain c C D := by
  classical
  by_cases hEq : C = D
  · subst D
    exact .refl
  · have hstrict : C ⊂ D := hCD.ssubset_of_ne hEq
    obtain ⟨x, hx, hDdel, hCDdel⟩ :=
      exists_closed_sdiff_singleton_between_of_finite_sdiff
        hfin hae hC hD hstrict hDCfin
    apply FiniteIntervalDeletionChain.delete x hx hDdel
    apply finiteIntervalDeletionChain hfin hae hC hDdel hCDdel
    exact hDCfin.subset (by
      intro y hy
      exact ⟨hy.1.1, hy.2⟩)
termination_by (D \ C).ncard
decreasing_by
  apply Set.ncard_lt_ncard _ hDCfin
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro y hy
    exact ⟨hy.1.1, hy.2⟩
  · intro heq
    have hx' : x ∈ (D \ {x}) \ C := heq ▸ hx
    exact hx'.1.2 rfl

end QuotientSubmoduleEquidistribution.SetClosure
