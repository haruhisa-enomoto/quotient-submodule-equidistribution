import Mathlib.Data.Set.Card
import OpConjecture.ConvexGeometry.CofiniteTwo

/-!
# Two-point complements without a finite ambient type

The finite implementation of `cofiniteTwoCount` enumerates all two-element
finsets and therefore assumes a finite ground type.  The manuscript also uses
the same count when the ambient indecomposable skeleton may be infinite.  This
file gives that version as a set of two-element deletion subsets.

For an anti-exchange closure, the deletion set is the disjoint union of
two-element subsets of the top extreme boundary and the oriented mixed
boundary.  Only those two boundary types need to be finite in order to recover
the natural-number formula; the ambient type remains arbitrary.
-/

noncomputable section

open Set

namespace OpConjecture.SetClosure

universe u

variable {E : Type u} (c : SetClosure E)

/-- The set of two-element deletion subsets whose complements are closed.
This definition does not require the ambient type to be finite. -/
def cofiniteTwoDeletionSet : Set (Set E) :=
  {D | D.ncard = 2 ∧ c.IsClosed Dᶜ}

/-- The set of top extreme points of the full closed set. -/
def topExtremeSet : Set E :=
  {x | c.IsTopExtreme x}

/-- The two-element subsets consisting entirely of top extreme points. -/
def topExtremePairSet : Set (Set E) :=
  {D | D ⊆ c.topExtremeSet ∧ D.ncard = 2}

/-- Forget the orientation of a mixed boundary pair. -/
def MixedBoundaryPair.deletion (p : c.MixedBoundaryPair) : Set E :=
  {p.1.1, p.1.2}

/-- The mixed two-element deletions, defined as the range of the canonical
orientation which puts the unique top extreme point first. -/
def mixedBoundaryDeletionSet : Set (Set E) :=
  Set.range (MixedBoundaryPair.deletion c)

namespace MixedBoundaryPair

/-- Forgetting the canonical orientation of a mixed boundary pair is
injective. -/
theorem deletion_injective :
    Function.Injective (deletion (c := c)) := by
  intro p q h
  have hfst : p.1.1 = q.1.1 := by
    have hmem : q.1.1 ∈ ({p.1.1, p.1.2} : Set E) := by
      change q.1.1 ∈ deletion c p
      rw [h]
      simp [deletion]
    rcases hmem with hqp | hqp
    · exact hqp.symm
    · exact (p.2.2.1 (hqp ▸ q.2.1)).elim
  have hsnd : p.1.2 = q.1.2 := by
    have hmem : q.1.2 ∈ ({p.1.1, p.1.2} : Set E) := by
      change q.1.2 ∈ deletion c p
      rw [h]
      simp [deletion]
    rcases hmem with hqp | hqp
    · exact (q.2.2.1 (hqp ▸ p.2.1)).elim
    · exact hqp.symm
  exact Subtype.ext (Prod.ext hfst hsnd)

end MixedBoundaryPair

/-- The arbitrary-ambient two-deletion partition. -/
theorem cofiniteTwoDeletionSet_eq_topExtremePairSet_union_mixedBoundary
    (hae : c.IsAntiExchange) :
    c.cofiniteTwoDeletionSet =
      c.topExtremePairSet ∪ c.mixedBoundaryDeletionSet := by
  ext D
  constructor
  · rintro ⟨hcard, hclosed⟩
    obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.mp hcard
    have hextreme :=
      isTopExtreme_or_isTopExtreme_of_isClosed_compl_pair
        c hae hxy hclosed
    rcases hextreme with hx | hy
    · by_cases hy' : c.IsTopExtreme y
      · left
        refine ⟨?_, Set.ncard_pair hxy⟩
        intro z hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy'
      · right
        exact ⟨⟨(x, y), hx, hy', hclosed⟩, rfl⟩
    · by_cases hx' : c.IsTopExtreme x
      · left
        refine ⟨?_, Set.ncard_pair hxy⟩
        intro z hz
        rcases hz with rfl | rfl
        · exact hx'
        · exact hy
      · right
        exact
          ⟨⟨(y, x), hy, hx', by
              simpa [Set.pair_comm] using hclosed⟩,
            by simp [MixedBoundaryPair.deletion, Set.pair_comm]⟩
  · rintro (htop | hmixed)
    · exact ⟨htop.2, isClosed_compl_of_subset_topExtreme c htop.1⟩
    · obtain ⟨p, rfl⟩ := hmixed
      exact ⟨Set.ncard_pair p.ne, p.2.2.2⟩

/-- The top and mixed pieces of the arbitrary-ambient partition are
disjoint. -/
theorem disjoint_topExtremePairSet_mixedBoundaryDeletionSet :
    Disjoint c.topExtremePairSet c.mixedBoundaryDeletionSet := by
  rw [Set.disjoint_left]
  intro D htop hmixed
  obtain ⟨p, hp⟩ := hmixed
  have hpD : p.1.2 ∈ D := by
    rw [← hp]
    simp [MixedBoundaryPair.deletion]
  exact p.2.2.1 (htop.1 hpD)

/-- Extended-natural cardinal form of the arbitrary-ambient two-deletion
partition.  It records finite cardinality exactly and collapses every infinite
cardinality to `⊤`, so the statement remains valid if a boundary is infinite. -/
theorem encard_cofiniteTwoDeletionSet_eq
    (hae : c.IsAntiExchange) :
    c.cofiniteTwoDeletionSet.encard =
      c.topExtremePairSet.encard + ENat.card c.MixedBoundaryPair := by
  rw [cofiniteTwoDeletionSet_eq_topExtremePairSet_union_mixedBoundary c hae,
    Set.encard_union_eq
      (disjoint_topExtremePairSet_mixedBoundaryDeletionSet c)]
  congr 1
  exact
    (ENat.card_congr
      (Equiv.ofInjective (MixedBoundaryPair.deletion c)
        (MixedBoundaryPair.deletion_injective c))).symm

/-- The two-deletion set is finite as soon as its two boundary pieces are
finite.  This makes the manuscript's finiteness assertion explicit instead
of relying only on the value of `Set.ncard`. -/
theorem finite_cofiniteTwoDeletionSet
    (hae : c.IsAntiExchange)
    (hextreme : c.topExtremeSet.Finite)
    [Finite c.MixedBoundaryPair] :
    c.cofiniteTwoDeletionSet.Finite := by
  rw [cofiniteTwoDeletionSet_eq_topExtremePairSet_union_mixedBoundary c hae]
  apply Set.Finite.union
  · exact hextreme.powerset.subset fun D hD ↦ hD.1
  · rw [mixedBoundaryDeletionSet, ← Set.image_univ]
    exact (Set.toFinite (Set.univ : Set c.MixedBoundaryPair)).image
      (MixedBoundaryPair.deletion c)

/-- Natural-number form of the arbitrary-ambient two-deletion formula.
It assumes finiteness only of the top extreme boundary and the mixed boundary,
not of the ground type. -/
theorem ncard_cofiniteTwoDeletionSet_eq_choose_add
    (hae : c.IsAntiExchange)
    (hextreme : c.topExtremeSet.Finite)
    [Finite c.MixedBoundaryPair] :
    c.cofiniteTwoDeletionSet.ncard =
      Nat.choose c.topExtremeSet.ncard 2 +
        Nat.card c.MixedBoundaryPair := by
  have htop : c.topExtremePairSet.Finite := by
    exact (hextreme.powerset.subset fun D hD ↦ hD.1)
  have hmixed : c.mixedBoundaryDeletionSet.Finite := by
    rw [mixedBoundaryDeletionSet, ← Set.image_univ]
    exact (Set.toFinite (Set.univ : Set c.MixedBoundaryPair)).image
      (MixedBoundaryPair.deletion c)
  rw [cofiniteTwoDeletionSet_eq_topExtremePairSet_union_mixedBoundary c hae,
    Set.ncard_union_eq
      (disjoint_topExtremePairSet_mixedBoundaryDeletionSet c) htop hmixed,
    topExtremePairSet,
    Set.ncard_powerset_ncard hextreme 2,
    mixedBoundaryDeletionSet,
    Set.ncard_range_of_injective
      (MixedBoundaryPair.deletion_injective c)]

end OpConjecture.SetClosure
