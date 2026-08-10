import OpConjecture.RepresentationTheory.FactorHomCriterion

/-!
# Termination and repeated pairs in factor ladders

This file formalizes the general recurrence facts used in the four-vertex
ladder appendix.  Eventual vanishing turns failure to reach a boundary into
termination without a boundary coefficient.  Since the recurrence is
determined by two consecutive terms, a repeated ordered pair propagates
forever and is incompatible with eventual vanishing unless both terms are
zero.
-/

set_option autoImplicit false
noncomputable section

namespace OpConjecture.FactorLadder

universe u

variable {D : Type u}

namespace Data

variable (A : Data D)

/-- The ladder starting at `x` vanishes from some index onward. -/
def EventuallyZero (x : D) : Prop :=
  ∃ N, ∀ n, N ≤ n → A.ladder x n = 0

/-- No selected boundary label has a positive coefficient in any ladder
term. -/
def AvoidsBoundary (P : Set D) (x : D) : Prop :=
  ∀ n p, p ∈ P → ¬ 0 < A.ladder x n p

/-- The sequence eventually vanishes and never contains a selected boundary
coefficient.  This is the literal condition counted in the four-ladder
appendix. -/
def TerminatesWithoutBoundary (P : Set D) (x : D) : Prop :=
  A.EventuallyZero x ∧ A.AvoidsBoundary P x

theorem avoidsBoundary_iff_not_reachesBoundary
    (P : Set D) (x : D) :
    A.AvoidsBoundary P x ↔ ¬ A.ReachesBoundary P x := by
  constructor
  · intro hAvoid
    rintro ⟨n, p, hp, hpos⟩
    exact hAvoid n p hp hpos
  · intro hnot n p hp hpos
    exact hnot ⟨n, p, hp, hpos⟩

/-- Under eventual vanishing, failure to reach the boundary is exactly the
terminating-without-boundary condition used by the finite configuration
count. -/
theorem terminatesWithoutBoundary_iff_not_reachesBoundary
    (P : Set D) (x : D) (hzero : A.EventuallyZero x) :
    A.TerminatesWithoutBoundary P x ↔
      ¬ A.ReachesBoundary P x := by
  rw [TerminatesWithoutBoundary,
    A.avoidsBoundary_iff_not_reachesBoundary]
  exact and_iff_right hzero

/-- Equality of two consecutive ladder terms propagates by every common
forward shift. -/
theorem ladder_add_eq_of_pair_eq
    (x : D) {n m : ℕ}
    (hzero : A.ladder x n = A.ladder x m)
    (hone : A.ladder x (n + 1) = A.ladder x (m + 1)) :
    ∀ r, A.ladder x (n + r) = A.ladder x (m + r) := by
  intro r
  induction r using Nat.twoStepInduction with
  | zero => simpa using hzero
  | one => simpa [Nat.add_assoc] using hone
  | more r hr hr1 =>
      rw [show n + (r + 2) = (n + r) + 2 by omega,
        show m + (r + 2) = (m + r) + 2 by omega,
        ladder_add_two, ladder_add_two,
        show n + r + 1 = n + (r + 1) by omega,
        show m + r + 1 = m + (r + 1) by omega,
        hr, hr1]

/-- A nonzero ordered pair cannot repeat later in an eventually vanishing
factor ladder. -/
theorem pair_ne_of_eventuallyZero_of_lt
    (x : D) (hEventually : A.EventuallyZero x)
    {n m : ℕ} (hnm : n < m)
    (hnonzero : A.ladder x n ≠ 0 ∨ A.ladder x (n + 1) ≠ 0) :
    A.ladder x n ≠ A.ladder x m ∨
      A.ladder x (n + 1) ≠ A.ladder x (m + 1) := by
  by_contra hrepeat
  push Not at hrepeat
  let d := m - n
  have hd : 0 < d := Nat.sub_pos_of_lt hnm
  have hm : m = n + d := by omega
  have hshift : ∀ r,
      A.ladder x (n + r) = A.ladder x (n + d + r) := by
    intro r
    simpa [hm] using
      A.ladder_add_eq_of_pair_eq x hrepeat.1 hrepeat.2 r
  have hiterate : ∀ k,
      A.ladder x n = A.ladder x (n + k * d) ∧
        A.ladder x (n + 1) = A.ladder x (n + 1 + k * d) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        constructor
        · calc
            A.ladder x n = A.ladder x (n + k * d) := ih.1
            _ = A.ladder x (n + d + k * d) := hshift (k * d)
            _ = A.ladder x (n + (k + 1) * d) := by
              simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm]
        · calc
            A.ladder x (n + 1) =
                A.ladder x (n + 1 + k * d) := ih.2
            _ = A.ladder x (n + d + (1 + k * d)) := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                hshift (1 + k * d)
            _ = A.ladder x (n + 1 + (k + 1) * d) := by
              simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm]
  obtain ⟨N, hN⟩ := hEventually
  let k := N + 1
  have hdk : k ≤ k * d := by
    simpa using Nat.mul_le_mul_left k hd
  have hNk : N ≤ n + k * d := by
    have hNk' : N ≤ k := by simp [k]
    omega
  have hNk1 : N ≤ n + 1 + k * d := by omega
  rcases hnonzero with hn | hn
  · exact hn ((hiterate k).1.trans (hN _ hNk))
  · exact hn ((hiterate k).2.trans (hN _ hNk1))

/-- The finite ladder fragment consumed by the normalized four-vertex
classifier.  It records only the boundary coefficients through term four
and the two repeated-pair exclusions actually used in the manuscript's
case split. -/
structure FourStepAvoidingCertificate
    (P : Set D) (x : D) : Prop where
  start_not_mem : x ∉ P
  boundary_zero_through_four :
    ∀ n ≤ 4, ∀ p, p ∈ P → A.ladder x n p = 0
  pair_zero_two :
    A.ladder x 0 ≠ A.ladder x 2 ∨
      A.ladder x 1 ≠ A.ladder x 3
  pair_zero_three :
    A.ladder x 0 ≠ A.ladder x 3 ∨
      A.ladder x 1 ≠ A.ladder x 4

/-- Eventual vanishing plus boundary avoidance supplies the exact finite
certificate.  Coefficientwise nonnegativity is separated as an explicit
hypothesis so the result applies to any concrete ladder realization. -/
theorem fourStepAvoidingCertificate_of_terminatesWithoutBoundary
    (P : Set D) (x : D)
    (hnonneg : ∀ n d, 0 ≤ A.ladder x n d)
    (h : A.TerminatesWithoutBoundary P x) :
    A.FourStepAvoidingCertificate P x := by
  have hbasis : A.ladder x 0 ≠ 0 := by
    intro hzero
    have hx := congrFun hzero x
    rw [A.ladder_zero, FactorLadder.basis_apply_self, Pi.zero_apply] at hx
    exact one_ne_zero hx
  refine
    { start_not_mem := ?_
      boundary_zero_through_four := ?_
      pair_zero_two := ?_
      pair_zero_three := ?_ }
  · intro hxP
    exact h.2 0 x hxP (by simp [FactorLadder.basis])
  · intro n hn p hp
    have hnotpos := h.2 n p hp
    have hge := hnonneg n p
    omega
  · have hne := A.pair_ne_of_eventuallyZero_of_lt
      x h.1 (n := 0) (m := 2) (by omega) (Or.inl hbasis)
    simpa using hne
  · have hne := A.pair_ne_of_eventuallyZero_of_lt
      x h.1 (n := 0) (m := 3) (by omega) (Or.inl hbasis)
    simpa using hne

end Data

namespace IyamaRadicalLayerInput

/-- Iyama's eventual radical-layer vanishing supplies the exact termination
interpretation of a bad factor ladder. -/
theorem terminatesWithoutBoundary_iff_not_reachesBoundary
    {A : Data D} {factorHomNonzero : D → D → Prop}
    (H : IyamaRadicalLayerInput A factorHomNonzero)
    (P : Set D) (x : D) :
    A.TerminatesWithoutBoundary P x ↔
      ¬ A.ReachesBoundary P x := by
  apply A.terminatesWithoutBoundary_iff_not_reachesBoundary
  exact H.eventually_ladder_zero x

end IyamaRadicalLayerInput

end OpConjecture.FactorLadder
