import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderTermination

/-!
# Hookless packets in an abstract factor ladder

The four-support lemma has two hookless terminating configurations.  This
file isolates their exact numerical operator content and verifies the two
finite ladder patterns directly from the coefficientwise-positive
recurrence.
-/

set_option autoImplicit false
noncomputable section

namespace QuotientSubmoduleEquidistribution.FactorLadder

universe u

variable {D : Type u}

theorem positivePart_basis (x : D) : positivePart (basis x) = basis x := by
  apply (positivePart_eq_self_iff (basis x)).2
  intro d
  classical
  by_cases h : d = x
  · simp [basis, h]
  · simp [basis, h]

theorem positivePart_neg_basis (x : D) :
    positivePart (-basis x) = 0 := by
  funext d
  classical
  by_cases h : d = x
  · subst d
    simp [positivePart]
  · simp [positivePart, basis, h]

namespace Data

/-- Numerical operator data for row `F` of the manuscript's hookless
four-vertex packets.  The ladder itself uses `a,c,z`; the boundary witness
`p` records the fourth, projective vertex of the configuration. -/
structure KilledFixedPacket (A : Data D) (P : Set D) where
  p : D
  a : D
  c : D
  z : D
  theta_z : A.theta (basis z) = basis c
  theta_c : A.theta (basis c) = basis a + basis z
  tau_z : A.tau (basis z) = basis a
  tau_c : A.tau (basis c) = basis c
  p_mem : p ∈ P
  c_not_mem : c ∉ P
  z_not_mem : z ∉ P

namespace KilledFixedPacket

variable {A : Data D} {P : Set D} (F : A.KilledFixedPacket P)

@[simp]
theorem ladder_zero_eq : A.ladder F.z 0 = basis F.z :=
  A.ladder_zero F.z

@[simp]
theorem ladder_one_eq : A.ladder F.z 1 = basis F.c := by
  rw [A.ladder_one, F.theta_z]

@[simp]
theorem ladder_two_eq : A.ladder F.z 2 = basis F.z := by
  rw [show 2 = 0 + 2 by omega, A.ladder_add_two,
    A.ladder_one, A.ladder_zero, F.theta_z, F.theta_c, F.tau_z]
  have hsub : basis F.a + basis F.z - basis F.a = basis F.z := by
    abel
  rw [hsub, positivePart_basis]

@[simp]
theorem ladder_three_eq : A.ladder F.z 3 = 0 := by
  rw [show 3 = 1 + 2 by omega, A.ladder_add_two,
    F.ladder_two_eq, F.ladder_one_eq, F.theta_z, F.tau_c, sub_self]
  funext d
  simp [positivePart]

@[simp]
theorem ladder_four_eq : A.ladder F.z 4 = 0 := by
  rw [show 4 = 2 + 2 by omega, A.ladder_add_two,
    F.ladder_three_eq, map_zero, F.ladder_two_eq, F.tau_z,
    zero_sub, positivePart_neg_basis]

/-- Every fixed-packet ladder term from index three onward vanishes. -/
theorem ladder_eq_zero_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    A.ladder F.z n = 0 :=
  A.ladder_eq_zero_of_consecutive F.z 3
    F.ladder_three_eq F.ladder_four_eq n hn

/-- A fixed packet is eventually zero, with uniform cutoff three. -/
theorem eventuallyZero : A.EventuallyZero F.z :=
  ⟨3, fun _ n ↦ F.ladder_eq_zero_of_three_le n⟩

/-- The nonzero fixed-packet terms avoid the selected boundary. -/
theorem avoidsBoundary : A.AvoidsBoundary P F.z := by
  intro n p hp
  by_cases hn : n < 3
  · interval_cases n
    · have hpz : p ≠ F.z := by
        intro h
        exact F.z_not_mem (h ▸ hp)
      simp [hpz]
    · have hpc : p ≠ F.c := by
        intro h
        exact F.c_not_mem (h ▸ hp)
      rw [F.ladder_one_eq]
      simp [hpc]
    · have hpz : p ≠ F.z := by
        intro h
        exact F.z_not_mem (h ▸ hp)
      rw [F.ladder_two_eq]
      simp [hpz]
  · rw [F.ladder_eq_zero_of_three_le (by omega)]
    simp

/-- A fixed packet is a literal terminating-without-boundary packet. -/
theorem terminatesWithoutBoundary :
    A.TerminatesWithoutBoundary P F.z :=
  ⟨F.eventuallyZero, F.avoidsBoundary⟩

/-- In particular, a fixed-packet ladder does not reach the boundary. -/
theorem not_reachesBoundary : ¬ A.ReachesBoundary P F.z :=
  (A.avoidsBoundary_iff_not_reachesBoundary P F.z).1 F.avoidsBoundary

end KilledFixedPacket

/-- Numerical operator data for row `T` of the manuscript's hookless
four-vertex packets. -/
structure KilledTrianglePacket (A : Data D) (P : Set D) where
  p : D
  A₁ : D
  A₂ : D
  x : D
  theta_x : A.theta (basis x) = basis A₁
  theta_A₁ : A.theta (basis A₁) = basis A₂
  theta_A₂ : A.theta (basis A₂) = basis p + basis x
  tau_x : A.tau (basis x) = 0
  tau_A₁ : A.tau (basis A₁) = basis p
  tau_A₂ : A.tau (basis A₂) = basis A₁
  p_mem : p ∈ P
  A₁_not_mem : A₁ ∉ P
  A₂_not_mem : A₂ ∉ P
  x_not_mem : x ∉ P

namespace KilledTrianglePacket

variable {A : Data D} {P : Set D} (T : A.KilledTrianglePacket P)

@[simp]
theorem ladder_zero_eq : A.ladder T.x 0 = basis T.x :=
  A.ladder_zero T.x

@[simp]
theorem ladder_one_eq : A.ladder T.x 1 = basis T.A₁ := by
  rw [A.ladder_one, T.theta_x]

@[simp]
theorem ladder_two_eq : A.ladder T.x 2 = basis T.A₂ := by
  rw [show 2 = 0 + 2 by omega, A.ladder_add_two,
    A.ladder_one, A.ladder_zero, T.theta_x, T.theta_A₁, T.tau_x,
    sub_zero, positivePart_basis]

@[simp]
theorem ladder_three_eq : A.ladder T.x 3 = basis T.x := by
  rw [show 3 = 1 + 2 by omega, A.ladder_add_two,
    T.ladder_two_eq, T.ladder_one_eq, T.theta_A₂, T.tau_A₁]
  have hsub : basis T.p + basis T.x - basis T.p = basis T.x := by
    abel
  rw [hsub, positivePart_basis]

@[simp]
theorem ladder_four_eq : A.ladder T.x 4 = 0 := by
  rw [show 4 = 2 + 2 by omega, A.ladder_add_two,
    T.ladder_three_eq, T.ladder_two_eq, T.theta_x, T.tau_A₂,
    sub_self]
  funext d
  simp [positivePart]

@[simp]
theorem ladder_five_eq : A.ladder T.x 5 = 0 := by
  rw [show 5 = 3 + 2 by omega, A.ladder_add_two,
    T.ladder_four_eq, map_zero, T.ladder_three_eq, T.tau_x, sub_self]
  funext d
  simp [positivePart]

/-- Every triangle-packet ladder term from index four onward vanishes. -/
theorem ladder_eq_zero_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    A.ladder T.x n = 0 :=
  A.ladder_eq_zero_of_consecutive T.x 4
    T.ladder_four_eq T.ladder_five_eq n hn

/-- A triangle packet is eventually zero, with uniform cutoff four. -/
theorem eventuallyZero : A.EventuallyZero T.x :=
  ⟨4, fun _ n ↦ T.ladder_eq_zero_of_four_le n⟩

/-- The nonzero triangle-packet terms avoid the selected boundary. -/
theorem avoidsBoundary : A.AvoidsBoundary P T.x := by
  intro n p hp
  by_cases hn : n < 4
  · interval_cases n
    · have hpx : p ≠ T.x := by
        intro h
        exact T.x_not_mem (h ▸ hp)
      simp [hpx]
    · have hpA₁ : p ≠ T.A₁ := by
        intro h
        exact T.A₁_not_mem (h ▸ hp)
      rw [T.ladder_one_eq]
      simp [hpA₁]
    · have hpA₂ : p ≠ T.A₂ := by
        intro h
        exact T.A₂_not_mem (h ▸ hp)
      rw [T.ladder_two_eq]
      simp [hpA₂]
    · have hpx : p ≠ T.x := by
        intro h
        exact T.x_not_mem (h ▸ hp)
      rw [T.ladder_three_eq]
      simp [hpx]
  · rw [T.ladder_eq_zero_of_four_le (by omega)]
    simp

/-- A triangle packet is a literal terminating-without-boundary packet. -/
theorem terminatesWithoutBoundary :
    A.TerminatesWithoutBoundary P T.x :=
  ⟨T.eventuallyZero, T.avoidsBoundary⟩

/-- In particular, a triangle-packet ladder does not reach the boundary. -/
theorem not_reachesBoundary : ¬ A.ReachesBoundary P T.x :=
  (A.avoidsBoundary_iff_not_reachesBoundary P T.x).1 T.avoidsBoundary

end KilledTrianglePacket

end Data

end QuotientSubmoduleEquidistribution.FactorLadder
