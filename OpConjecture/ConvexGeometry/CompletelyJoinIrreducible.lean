import OpConjecture.ConvexGeometry.ClosedSets

/-!
# Completely join-irreducible closed sets and spatiality

Mathlib's `SupIrred` is finite/binary join-irreducibility.  The manuscript
uses complete join-irreducibility, so we define the complete notion here.
-/

open Set

namespace OpConjecture

/-- An element is completely join-irreducible when every supremum equal to
it contains it as one of the joined elements. -/
def IsCompletelyJoinIrreducible {L : Type*} [CompleteLattice L] (j : L) : Prop :=
  ∀ S : Set L, sSup S = j → j ∈ S

/-- A complete lattice is spatial when every element is the supremum of
the completely join-irreducible elements below it. -/
def IsSpatial (L : Type*) [CompleteLattice L] : Prop :=
  ∀ a : L, sSup {j : L | IsCompletelyJoinIrreducible j ∧ j ≤ a} = a

namespace SetClosure

variable {E : Type*} {c : SetClosure E}

/-- An element with a greatest strict predecessor is completely
join-irreducible. -/
theorem isCompletelyJoinIrreducible_of_greatest_lt
    {L : Type*} [CompleteLattice L] {j jₛ : L}
    (hₛ : jₛ < j) (hgreatest : ∀ ⦃a : L⦄, a < j → a ≤ jₛ) :
    IsCompletelyJoinIrreducible j := by
  intro S hS
  by_contra hjS
  have hle : sSup S ≤ jₛ := by
    apply sSup_le
    intro a haS
    have haj : a ≤ j := by
      rw [← hS]
      exact le_sSup haS
    have hane : a ≠ j := by
      intro haj'
      exact hjS (haj' ▸ haS)
    exact hgreatest (lt_of_le_of_ne haj hane)
  have hjle : j ≤ jₛ := hS ▸ hle
  exact (not_le_of_gt hₛ) hjle

/-- In a finitary convex geometry, a point closure is completely
join-irreducible. -/
theorem pointClosure_isCompletelyJoinIrreducible
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    (hempty : c.IsClosed ∅) (x : E) :
    IsCompletelyJoinIrreducible (c.pointClosure x) := by
  let Jₛ : c.Closeds :=
    ⟨c ({x} : Set E) \ {x},
      isClosed_pointClosure_sdiff_singleton hfin hae hempty x⟩
  apply isCompletelyJoinIrreducible_of_greatest_lt (jₛ := Jₛ)
  · change c ({x} : Set E) \ {x} ⊂ c ({x} : Set E)
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨sdiff_subset, ?_⟩
    intro heq
    have hxJ : x ∈ c ({x} : Set E) :=
      c.le_closure {x} (mem_singleton x)
    have : x ∈ c ({x} : Set E) \ {x} := heq.symm ▸ hxJ
    exact this.2 rfl
  · intro A hAJ
    change (A : Set E) ⊆ c ({x} : Set E) \ {x}
    intro y hyA
    refine ⟨hAJ.le hyA, ?_⟩
    intro hyx
    have hxA : x ∈ (A : Set E) := hyx ▸ hyA
    have hJA : c.pointClosure x ≤ A :=
      pointClosure_le_iff.2 hxA
    exact hAJ.2 hJA

/-- The completely join-irreducible closed sets are exactly the point
closures. -/
theorem isCompletelyJoinIrreducible_iff_eq_pointClosure
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    (hempty : c.IsClosed ∅) (J : c.Closeds) :
    IsCompletelyJoinIrreducible J ↔
      ∃ x : E, J = c.pointClosure x := by
  constructor
  · intro hJ
    let P : Set c.Closeds :=
      c.pointClosure '' (J : Set E)
    have hsup : sSup P = J := by
      apply le_antisymm
      · apply sSup_le
        intro K hK
        obtain ⟨x, hxJ, rfl⟩ := hK
        exact pointClosure_le_iff.2 hxJ
      · rw [← iSup_pointClosure J]
        apply iSup_le
        intro x
        exact le_sSup ⟨x.1, x.2, rfl⟩
    have hmem : J ∈ P := hJ P hsup
    obtain ⟨x, hxJ, hx⟩ := hmem
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, rfl⟩
    exact pointClosure_isCompletelyJoinIrreducible hfin hae hempty x

/-- The closed-set lattice of a finitary convex geometry is spatial. -/
theorem isSpatial_closeds
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    (hempty : c.IsClosed ∅) :
    IsSpatial c.Closeds := by
  intro C
  apply le_antisymm
  · apply sSup_le
    intro J hJ
    exact hJ.2
  · calc
      C = ⨆ x : (C : Set E), c.pointClosure x.1 :=
        (iSup_pointClosure C).symm
      _ ≤ sSup {J : c.Closeds |
          IsCompletelyJoinIrreducible J ∧ J ≤ C} := by
        apply iSup_le
        intro x
        apply le_sSup
        exact ⟨pointClosure_isCompletelyJoinIrreducible hfin hae hempty x.1,
          pointClosure_le_iff.2 x.2⟩

end SetClosure

end OpConjecture
