import OpConjecture.RepresentationTheory.FiniteDimensionalRecurrence

/-!
# Pointwise faithful descent along annihilator factors

This file formalizes the pointwise route through annihilator factors used in
the preferred bottom-level-four proof.  Total profile equality on a
factor-closed class descends to its faithful cells; conversely, pointwise
faithful equality on every factor sums back to total equality.  Ringel's
core-cardinality theorem then reduces each fixed level to the strict
small-core branch.
-/

noncomputable section

namespace OpConjecture.BottomLevels.AnnihilatorInduction

variable {B : Type*}
  (measure : B → ℕ)
  (totalQ totalS faithfulQ faithfulS : B → ℕ)
  (ProperFactor : B → Type*)
  [∀ b : B, Fintype (ProperFactor b)]
  (factor : ∀ b : B, ProperFactor b → B)

/-- Equality of faithful contributions on every node implies equality of
the total counts by the annihilator recurrence. -/
theorem total_eq_of_pointwise_faithful_eq
    (hQ : ∀ b : B,
      totalQ b = faithfulQ b +
        ∑ I : ProperFactor b, faithfulQ (factor b I))
    (hS : ∀ b : B,
      totalS b = faithfulS b +
        ∑ I : ProperFactor b, faithfulS (factor b I))
    (hfaithful : ∀ b : B, faithfulQ b = faithfulS b)
    (b : B) : totalQ b = totalS b := by
  classical
  rw [hQ b, hS b, hfaithful b]
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  exact hfaithful (factor b I)

/-- On a factor-closed family with strict measure drop, equality of all total
profiles descends to equality of the faithful cells. -/
theorem faithful_eq_of_factor_closed_total_eq
    (hsmaller : ∀ (b : B) (I : ProperFactor b),
      measure (factor b I) < measure b)
    (hQ : ∀ b : B,
      totalQ b = faithfulQ b +
        ∑ I : ProperFactor b, faithfulQ (factor b I))
    (hS : ∀ b : B,
      totalS b = faithfulS b +
        ∑ I : ProperFactor b, faithfulS (factor b I))
    (htotal : ∀ b : B, totalQ b = totalS b)
    (b : B) : faithfulQ b = faithfulS b := by
  exact
    (total_and_faithful_eq_of_recurrence_of_local_either
      (measure := measure)
      (totalQ := totalQ) (totalS := totalS)
      (faithfulQ := faithfulQ) (faithfulS := faithfulS)
      (ProperFactor := ProperFactor) (factor := factor)
      hsmaller hQ hS
      (fun b _ => Or.inr (htotal b)) b).2

end OpConjecture.BottomLevels.AnnihilatorInduction

namespace OpConjecture.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode

open OpConjecture.BottomLevels
open OpConjecture.BottomLevels.AnnihilatorInduction
open OpConjecture.IndecomposableSkeleton.FaithfulCore

universe u

variable (K : Type u) [Field K]

/-- Pointwise equality of faithful counts on every finite-dimensional node
implies equality of the total count at the chosen level. -/
theorem levelCount_eq_of_pointwise_faithfulCount_eq
    (n : ℕ)
    (hfaithful : ∀ C : AlgebraNode K,
      faithfulQCount K C n = faithfulSCount K C n)
    (B : AlgebraNode K) :
    (qClosure K B).levelCount n = (sClosure K B).levelCount n := by
  exact total_eq_of_pointwise_faithful_eq
    (totalQ := fun C => (qClosure K C).levelCount n)
    (totalS := fun C => (sClosure K C).levelCount n)
    (faithfulQ := fun C => faithfulQCount K C n)
    (faithfulS := fun C => faithfulSCount K C n)
    (ProperFactor := ProperFactor K) (factor := factor K)
    (fun C => qRecurrence K C n)
    (fun C => sRecurrence K C n)
    hfaithful B

/-- Equality of the total count on every node in a factor-closed family
descends to equality of its faithful cell. -/
theorem faithfulCount_eq_of_factor_closed_levelCount_eq
    (n : ℕ)
    (htotal : ∀ C : AlgebraNode K,
      (qClosure K C).levelCount n = (sClosure K C).levelCount n)
    (B : AlgebraNode K) :
    faithfulQCount K B n = faithfulSCount K B n := by
  exact faithful_eq_of_factor_closed_total_eq
    (measure := measure K)
    (totalQ := fun C => (qClosure K C).levelCount n)
    (totalS := fun C => (sClosure K C).levelCount n)
    (faithfulQ := fun C => faithfulQCount K C n)
    (faithfulS := fun C => faithfulSCount K C n)
    (ProperFactor := ProperFactor K) (factor := factor K)
    (factor_measure_lt K)
    (fun C => qRecurrence K C n)
    (fun C => sRecurrence K C n)
    htotal B

/-- At an arbitrary level, Ringel core-cardinality handles the branch at or
below the common faithful-core size.  Consequently a theorem for the strict
small-core branch gives the faithful equality at that level. -/
theorem faithfulCount_eq_of_ringel_of_smallCore
    (n : ℕ)
    (B : AlgebraNode K)
    (hRingel : RingelCoreCardinality B.skeleton)
    (hsmall :
      ((quotientCoreData K B).core : Set B.Index).ncard < n →
        faithfulQCount K B n = faithfulSCount K B n) :
    faithfulQCount K B n = faithfulSCount K B n := by
  by_cases hcore :
      ((quotientCoreData K B).core : Set B.Index).ncard < n
  · exact hsmall hcore
  · exact faithfulLevelCount_eq_of_ringel_of_level_le
      (K := K) B.skeleton hRingel (Nat.le_of_not_gt hcore)

/-- A factor-closed family version of the preceding reduction.  Pointwise
Ringel core-cardinality plus only the strict small-core cases imply equality
of the total level count by annihilator summation. -/
theorem levelCount_eq_of_ringel_of_pointwise_smallCore
    (n : ℕ)
    (hRingel : ∀ C : AlgebraNode K, RingelCoreCardinality C.skeleton)
    (hsmall : ∀ C : AlgebraNode K,
      ((quotientCoreData K C).core : Set C.Index).ncard < n →
        faithfulQCount K C n = faithfulSCount K C n)
    (B : AlgebraNode K) :
    (qClosure K B).levelCount n = (sClosure K B).levelCount n := by
  apply levelCount_eq_of_pointwise_faithfulCount_eq K n
  intro C
  exact faithfulCount_eq_of_ringel_of_smallCore K n C
    (hRingel C) (hsmall C)

/-- The pointwise version of the remaining data for the two bottom levels
used by the headline theorem.  It requires no connectedness predicate or
separate block-product induction: every annihilator factor is treated at
its own faithful cell. -/
structure PointwiseThreeFourData where
  ringel : ∀ B : AlgebraNode K, RingelCoreCardinality B.skeleton
  smallCore : ∀ (B : AlgebraNode K) (n : ℕ), n = 3 ∨ n = 4 →
    ((quotientCoreData K B).core : Set B.Index).ncard < n →
      faithfulQCount K B n = faithfulSCount K B n

/-- Pointwise strict-small-core equality in degrees three and four, together
with Ringel core-cardinality, gives both total level equalities on every
finite-dimensional node. -/
theorem pointwise_levelCount_three_and_four_eq
    (D : PointwiseThreeFourData K)
    (B : AlgebraNode K) :
    (qClosure K B).levelCount 3 = (sClosure K B).levelCount 3 ∧
      (qClosure K B).levelCount 4 = (sClosure K B).levelCount 4 := by
  constructor
  · exact levelCount_eq_of_ringel_of_pointwise_smallCore K 3
      D.ringel (fun C ↦ D.smallCore C 3 (Or.inl rfl)) B
  · exact levelCount_eq_of_ringel_of_pointwise_smallCore K 4
      D.ringel (fun C ↦ D.smallCore C 4 (Or.inr rfl)) B

/-- The exact remaining nodewise inputs for the pointwise degree-four
argument.  The `smallCore` field is intentionally abstract: it is the only
place where a separate small-core theorem is used. -/
structure PointwiseLevelFourData where
  ringel : ∀ B : AlgebraNode K, RingelCoreCardinality B.skeleton
  smallCore : ∀ B : AlgebraNode K,
    ((quotientCoreData K B).core : Set B.Index).ncard < 4 →
      faithfulQCount K B 4 = faithfulSCount K B 4

/-- Ringel core-cardinality settles the common-core-size-at-least-four
branch; hence only the strict small-core branch is needed for pointwise
faithful equality in degree four. -/
theorem faithfulCount_four_eq
    (D : PointwiseLevelFourData K)
    (B : AlgebraNode K) :
    faithfulQCount K B 4 = faithfulSCount K B 4 := by
  exact faithfulCount_eq_of_ringel_of_smallCore K 4 B
    (D.ringel B) (D.smallCore B)

/-- The preferred pointwise-faithful proof of total degree-four equality:
prove the strict small-core faithful case on every annihilator factor, use
Ringel above the cutoff, and sum the faithful cells by the canonical
annihilator recurrence. -/
theorem levelCount_four_eq
    (D : PointwiseLevelFourData K)
    (B : AlgebraNode K) :
    (qClosure K B).levelCount 4 = (sClosure K B).levelCount 4 := by
  exact levelCount_eq_of_ringel_of_pointwise_smallCore K 4
    D.ringel D.smallCore B

end OpConjecture.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode
