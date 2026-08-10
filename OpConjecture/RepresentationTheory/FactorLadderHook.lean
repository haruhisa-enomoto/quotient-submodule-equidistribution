import OpConjecture.RepresentationTheory.FactorLadderTermination

/-!
# Hook packets in an abstract factor ladder

The basic packet in the four-support lemma is a three-term hook.  This file
states its exact operator content and proves, directly from the recurrence,
that the ladder is `b, u, 0, 0, ...` and avoids the selected boundary.
-/

set_option autoImplicit false
noncomputable section

namespace OpConjecture.FactorLadder

universe u

variable {D : Type u}

namespace Data

/-- Numerical operator data carried by a hook `(a,u,b)`.

For an AR factor ladder the first three equalities come from singleton
predecessor sets and `τ b = a`.  Nonnegativity of the restricted translation
is automatic for the actual AR operator. -/
structure KilledHook (A : Data D) (P : Set D) where
  a : D
  u : D
  b : D
  theta_b : A.theta (basis b) = basis u
  theta_u : A.theta (basis u) = basis a
  tau_b : A.tau (basis b) = basis a
  tau_u_nonneg : ∀ d, 0 ≤ A.tau (basis u) d
  u_not_mem : u ∉ P
  b_not_mem : b ∉ P

namespace KilledHook

variable {A : Data D} {P : Set D} (H : A.KilledHook P)

@[simp]
theorem ladder_zero_eq : A.ladder H.b 0 = basis H.b :=
  A.ladder_zero H.b

@[simp]
theorem ladder_one_eq : A.ladder H.b 1 = basis H.u := by
  rw [A.ladder_one, H.theta_b]

@[simp]
theorem ladder_two_eq : A.ladder H.b 2 = 0 := by
  rw [show 2 = 0 + 2 by omega, A.ladder_add_two,
    A.ladder_one, A.ladder_zero, H.theta_b, H.theta_u, H.tau_b,
    sub_self]
  funext d
  simp [positivePart]

@[simp]
theorem ladder_three_eq : A.ladder H.b 3 = 0 := by
  rw [show 3 = 1 + 2 by omega, A.ladder_add_two,
    H.ladder_two_eq, map_zero, H.ladder_one_eq]
  funext d
  simp only [Pi.zero_apply, zero_sub, positivePart_apply]
  exact max_eq_right (neg_nonpos.mpr (H.tau_u_nonneg d))

/-- Every term from index two onward vanishes. -/
theorem ladder_eq_zero_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    A.ladder H.b n = 0 :=
  A.ladder_eq_zero_of_consecutive H.b 2
    H.ladder_two_eq H.ladder_three_eq n hn

/-- A hook ladder is eventually zero, with uniform cutoff two. -/
theorem eventuallyZero : A.EventuallyZero H.b :=
  ⟨2, fun _ n ↦ H.ladder_eq_zero_of_two_le n⟩

/-- Neither nonzero term of the hook ladder meets the selected boundary. -/
theorem avoidsBoundary : A.AvoidsBoundary P H.b := by
  intro n p hp
  by_cases hn : n < 2
  · interval_cases n
    · have hpb : p ≠ H.b := by
        intro h
        exact H.b_not_mem (h ▸ hp)
      simp [hpb]
    · have hpu : p ≠ H.u := by
        intro h
        exact H.u_not_mem (h ▸ hp)
      rw [H.ladder_one_eq]
      simp [hpu]
  · rw [H.ladder_eq_zero_of_two_le (by omega)]
    simp

/-- A hook is a literal terminating-without-boundary packet. -/
theorem terminatesWithoutBoundary :
    A.TerminatesWithoutBoundary P H.b :=
  ⟨H.eventuallyZero, H.avoidsBoundary⟩

/-- In particular, a hook ladder does not reach the selected boundary. -/
theorem not_reachesBoundary : ¬ A.ReachesBoundary P H.b :=
  (A.avoidsBoundary_iff_not_reachesBoundary P H.b).1 H.avoidsBoundary

end KilledHook

end Data

end OpConjecture.FactorLadder
