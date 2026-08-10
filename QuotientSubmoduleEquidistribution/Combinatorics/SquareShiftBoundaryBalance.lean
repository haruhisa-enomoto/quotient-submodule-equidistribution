import QuotientSubmoduleEquidistribution.Combinatorics.BoundaryTranslationWeightedBalance

/-!
# Boundary balance for a square-shift grid

The strip proof compares a finite rectangle of labelled equalities under the
move `(f,e) ↦ (f+2,e+2)`.  After rebasing the two index intervals, the
incoming boundary consists of the first two rows or columns and the outgoing
boundary consists of the last two rows or columns.  This file realizes that
move as a finite partial translation and obtains the boundary-sum identity
from weighted chain conservation.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace QuotientSubmoduleEquidistribution.SquareShiftBoundaryBalance

/-- A finite rectangular grid. -/
abbrev Grid (rows cols : ℕ) := Fin rows × Fin cols

/-- Positions with no predecessor under subtraction by `(2,2)`. -/
def Incoming {rows cols : ℕ} (p : Grid rows cols) : Prop :=
  p.1.1 < 2 ∨ p.2.1 < 2

/-- Positions with no successor under addition by `(2,2)`. -/
def Outgoing {rows cols : ℕ} (p : Grid rows cols) : Prop :=
  rows ≤ p.1.1 + 2 ∨ cols ≤ p.2.1 + 2

/-- Add two to both coordinates of a non-outgoing position. -/
def addTwo {rows cols : ℕ} (p : Grid rows cols)
    (hp : ¬ Outgoing p) : Grid rows cols :=
  (⟨p.1.1 + 2, by
      simp only [Outgoing, not_or] at hp
      omega⟩,
    ⟨p.2.1 + 2, by
      simp only [Outgoing, not_or] at hp
      omega⟩)

/-- Subtract two from both coordinates of a non-incoming position. -/
def subTwo {rows cols : ℕ} (p : Grid rows cols)
    (_hp : ¬ Incoming p) : Grid rows cols :=
  (⟨p.1.1 - 2, by omega⟩, ⟨p.2.1 - 2, by omega⟩)

/-- Simultaneous subtraction by two is an equivalence from the complement
of the incoming boundary to the complement of the outgoing boundary. -/
def translationEquiv (rows cols : ℕ) :
    {p : Grid rows cols // ¬ Incoming p} ≃
      {p : Grid rows cols // ¬ Outgoing p} where
  toFun p := ⟨subTwo p.1 p.2, by
    have hpcoords : 2 ≤ p.1.1.1 ∧ 2 ≤ p.1.2.1 := by
      simpa [Incoming, not_or, not_lt] using p.2
    simp only [Outgoing, not_or, subTwo]
    constructor
    · have hbound := p.1.1.2
      omega
    · have hbound := p.1.2.2
      omega⟩
  invFun p := ⟨addTwo p.1 p.2, by
    simp only [Incoming, not_or, addTwo]
    constructor <;> omega⟩
  left_inv p := by
    have hpcoords : 2 ≤ p.1.1.1 ∧ 2 ≤ p.1.2.1 := by
      simpa [Incoming, not_or, not_lt] using p.2
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;>
      simp only [subTwo, addTwo] <;> omega
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;>
      simp only [subTwo, addTwo] <;> omega

/-- The square shift as a finite partial translation. -/
def data (rows cols : ℕ) :
    QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data
      (Grid rows cols) Incoming Outgoing where
  tau := translationEquiv rows cols

/-- Away from the outgoing boundary, successor is literal simultaneous
addition by two. -/
theorem successor_eq_addTwo
    {rows cols : ℕ} (p : Grid rows cols) (hp : ¬ Outgoing p) :
    (data rows cols).successor p = addTwo p hp := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.successor,
      data, translationEquiv, addTwo, hp]

noncomputable instance incomingFintype (rows cols : ℕ) :
    Fintype {p : Grid rows cols // Incoming p} := Fintype.ofFinite _

noncomputable instance outgoingFintype (rows cols : ℕ) :
    Fintype {p : Grid rows cols // Outgoing p} := Fintype.ofFinite _

/-- Every weight invariant under the interior square shift has equal total
weight on the incoming and outgoing grid boundaries. -/
theorem sum_incoming_eq_sum_outgoing
    {rows cols : ℕ} {A : Type*} [AddCommMonoid A]
    (weight : Grid rows cols → A)
    (hshift : ∀ p (hp : ¬ Outgoing p),
      weight (addTwo p hp) = weight p) :
    (∑ p : {p : Grid rows cols // Incoming p}, weight p.1) =
      ∑ p : {p : Grid rows cols // Outgoing p}, weight p.1 := by
  apply (data rows cols).sum_source_eq_sum_target_of_successor_invariant
    weight
  intro p hp
  rw [successor_eq_addTwo p hp]
  exact hshift p hp

/-- Indicator form of square-shift conservation.  If equality of two
labelled sequences is unchanged by advancing both indices by two, then the
number of equality positions on the two grid boundaries agrees. -/
theorem sum_equalityIndicators_incoming_eq_outgoing
    {rows cols : ℕ} {Label : Type*} [DecidableEq Label]
    (x : Fin rows → Label) (y : Fin cols → Label)
    (hsquare : ∀ p (hp : ¬ Outgoing p),
      x (addTwo p hp).1 = y (addTwo p hp).2 ↔ x p.1 = y p.2) :
    (∑ p : {p : Grid rows cols // Incoming p},
        if x p.1.1 = y p.1.2 then 1 else 0) =
      ∑ p : {p : Grid rows cols // Outgoing p},
        if x p.1.1 = y p.1.2 then 1 else 0 := by
  apply sum_incoming_eq_sum_outgoing
    (weight := fun p ↦ if x p.1 = y p.2 then 1 else 0)
  intro p hp
  by_cases h : x p.1 = y p.2
  · have hadd := (hsquare p hp).2 h
    simp [h, hadd]
  · have hadd : x (addTwo p hp).1 ≠ y (addTwo p hp).2 := by
      exact fun h' ↦ h ((hsquare p hp).1 h')
    simp [h, hadd]

end QuotientSubmoduleEquidistribution.SquareShiftBoundaryBalance
