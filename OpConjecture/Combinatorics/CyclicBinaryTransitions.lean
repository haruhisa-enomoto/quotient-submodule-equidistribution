import Mathlib.Data.Finset.Card

/-!
# Binary transitions along finite permutations

The fixed-strip part of the four-vertex factor-ladder argument ends with an
elementary cyclic count: in a finite cyclic binary word, the number of
transitions from zero to one equals the number of transitions from one to
zero.  We prove the slightly stronger statement for an arbitrary finite
permutation, hence simultaneously on all of its cycles.
-/

set_option autoImplicit false

namespace OpConjecture.CyclicBinaryTransitions

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Positions at which a binary value changes from false to true while
following `e`. -/
def rises (e : ι ≃ ι) (f : ι → Bool) : Finset ι :=
  Finset.univ.filter fun i ↦ f (e.symm i) = false ∧ f i = true

/-- Positions after which a binary value changes from true to false while
following `e`. -/
def falls (e : ι ≃ ι) (f : ι → Bool) : Finset ι :=
  Finset.univ.filter fun i ↦ f i = true ∧ f (e i) = false

/-- Positions whose incoming edge under `e` has two true endpoints. -/
private def incomingStays (e : ι ≃ ι) (f : ι → Bool) : Finset ι :=
  Finset.univ.filter fun i ↦ f (e.symm i) = true ∧ f i = true

/-- Positions whose outgoing edge under `e` has two true endpoints. -/
private def outgoingStays (e : ι ≃ ι) (f : ι → Bool) : Finset ι :=
  Finset.univ.filter fun i ↦ f i = true ∧ f (e i) = true

/-- Along any finite permutation, the number of false-to-true transitions
is the number of true-to-false transitions. -/
theorem rises_card_eq_falls_card (e : ι ≃ ι) (f : ι → Bool) :
    (rises e f).card = (falls e f).card := by
  classical
  let support : Finset ι := Finset.univ.filter fun i ↦ f i = true
  let inStay := incomingStays e f
  let outStay := outgoingStays e f
  have hrise_union : rises e f ∪ inStay = support := by
    ext i
    cases hprev : f (e.symm i) <;>
      simp [rises, incomingStays, support, inStay, hprev]
  have hfall_union : falls e f ∪ outStay = support := by
    ext i
    cases hnext : f (e i) <;>
      simp [falls, outgoingStays, support, outStay, hnext]
  have hrise_disjoint : Disjoint (rises e f) inStay := by
    refine Finset.disjoint_left.2 ?_
    intro i hirise hin
    simp [rises] at hirise
    simp [inStay, incomingStays] at hin
    simp_all
  have hfall_disjoint : Disjoint (falls e f) outStay := by
    refine Finset.disjoint_left.2 ?_
    intro i hfall hout
    simp [falls] at hfall
    simp [outStay, outgoingStays] at hout
    simp_all
  have hstay_map : outStay.map e.toEmbedding = inStay := by
    ext i
    simp [outStay, inStay, outgoingStays, incomingStays, and_comm]
  have hstay_card : outStay.card = inStay.card := by
    rw [← hstay_map, Finset.card_map]
  have hrise_card : (rises e f).card + inStay.card = support.card := by
    rw [← hrise_union, Finset.card_union_of_disjoint hrise_disjoint]
  have hfall_card : (falls e f).card + outStay.card = support.card := by
    rw [← hfall_union, Finset.card_union_of_disjoint hfall_disjoint]
  omega

end OpConjecture.CyclicBinaryTransitions
