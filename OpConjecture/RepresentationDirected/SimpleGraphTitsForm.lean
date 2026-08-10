import OpConjecture.RepresentationDirected.SimpleGraphTits
import Mathlib.Tactic.Ring

/-!
# The Tits form, faithfulness, and reflection transport

This file proves the invariant integral Tits form for an arbitrary finite
simple graph, faithfulness of its geometric representation, and transport of
simple reflections by transported simple roots.  No finite-type or
classification hypothesis is used.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace OpConjecture.RepresentationDirected.RootSignStrategy

open SimpleGraphCoxeter WordRootProcess

universe u

variable {L : Type u} [Fintype L]

/-- The ordered-edge term in the simply-laced Tits form. -/
def adjacencyPairing (G : SimpleGraph L)
    (z w : RootLattice L) : ℤ := by
  classical
  exact ∑ i, ∑ j, if G.Adj i j then z i * w j else 0

/-- The integral symmetric Tits form for a simple graph. -/
def titsForm (G : SimpleGraph L) (z w : RootLattice L) : ℤ :=
  2 * (∑ i, z i * w i) - adjacencyPairing G z w

theorem adjacencyPairing_comm (G : SimpleGraph L)
    (z w : RootLattice L) :
    adjacencyPairing G z w = adjacencyPairing G w z := by
  classical
  unfold adjacencyPairing
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [G.adj_comm]
  by_cases hij : G.Adj i j <;> simp [hij, mul_comm]

theorem titsForm_comm (G : SimpleGraph L) (z w : RootLattice L) :
    titsForm G z w = titsForm G w z := by
  classical
  unfold titsForm
  rw [adjacencyPairing_comm]
  have hdiag : (∑ i, z i * w i) = ∑ i, w i * z i :=
    Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  rw [hdiag]

theorem adjacencyPairing_add_left (G : SimpleGraph L)
    (z z' w : RootLattice L) :
    adjacencyPairing G (z + z') w =
      adjacencyPairing G z w + adjacencyPairing G z' w := by
  classical
  unfold adjacencyPairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : G.Adj i j <;> simp [hij, add_mul]

theorem adjacencyPairing_zsmul_left (G : SimpleGraph L)
    (c : ℤ) (z w : RootLattice L) :
    adjacencyPairing G (c • z) w = c * adjacencyPairing G z w := by
  classical
  unfold adjacencyPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : G.Adj i j <;> simp [hij]
  ring

theorem titsForm_add_left (G : SimpleGraph L)
    (z z' w : RootLattice L) :
    titsForm G (z + z') w = titsForm G z w + titsForm G z' w := by
  classical
  unfold titsForm
  rw [adjacencyPairing_add_left]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem titsForm_add_right (G : SimpleGraph L)
    (z w w' : RootLattice L) :
    titsForm G z (w + w') = titsForm G z w + titsForm G z w' := by
  rw [titsForm_comm G z (w + w'), titsForm_add_left,
    titsForm_comm G w z, titsForm_comm G w' z]

theorem titsForm_zsmul_left (G : SimpleGraph L)
    (c : ℤ) (z w : RootLattice L) :
    titsForm G (c • z) w = c * titsForm G z w := by
  classical
  unfold titsForm
  rw [adjacencyPairing_zsmul_left]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hdiag : (∑ x, c * (z x * w x)) = c * ∑ x, z x * w x := by
    rw [Finset.mul_sum]
  rw [hdiag]
  ring

theorem titsForm_zsmul_right (G : SimpleGraph L)
    (c : ℤ) (z w : RootLattice L) :
    titsForm G z (c • w) = c * titsForm G z w := by
  rw [titsForm_comm G z (c • w), titsForm_zsmul_left,
    titsForm_comm G w z]

theorem titsForm_neg_left (G : SimpleGraph L) (z w : RootLattice L) :
    titsForm G (-z) w = -titsForm G z w := by
  simpa only [neg_one_mul, neg_smul, one_smul] using
    titsForm_zsmul_left G (-1) z w

theorem titsForm_neg_right (G : SimpleGraph L) (z w : RootLattice L) :
    titsForm G z (-w) = -titsForm G z w := by
  rw [titsForm_comm, titsForm_neg_left, titsForm_comm]

theorem titsForm_sub_left (G : SimpleGraph L)
    (z z' w : RootLattice L) :
    titsForm G (z - z') w = titsForm G z w - titsForm G z' w := by
  rw [sub_eq_add_neg, titsForm_add_left, titsForm_neg_left, sub_eq_add_neg]

theorem titsForm_sub_right (G : SimpleGraph L)
    (z w w' : RootLattice L) :
    titsForm G z (w - w') = titsForm G z w - titsForm G z w' := by
  rw [sub_eq_add_neg, titsForm_add_right, titsForm_neg_right, sub_eq_add_neg]

theorem adjacencyPairing_simpleRoot_left (G : SimpleGraph L)
    (i : L) (z : RootLattice L) :
    adjacencyPairing G (simpleRoot i) z = neighborSum G i z := by
  classical
  unfold adjacencyPairing neighborSum
  rw [Finset.sum_eq_single i]
  · simp only [simpleRoot_apply_self, one_mul]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext j
      simp
    · intro j _
      rfl
  · intro j _ hji
    simp [simpleRoot_apply_of_ne hji]
  · simp

theorem titsForm_simpleRoot_left (G : SimpleGraph L)
    (i : L) (z : RootLattice L) :
    titsForm G (simpleRoot i) z =
      2 * z i - neighborSum G i z := by
  classical
  unfold titsForm
  rw [adjacencyPairing_simpleRoot_left]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [simpleRoot_apply_of_ne hji]
  · simp

theorem titsForm_simpleRoot_right (G : SimpleGraph L)
    (i : L) (z : RootLattice L) :
    titsForm G z (simpleRoot i) =
      2 * z i - neighborSum G i z := by
  rw [titsForm_comm, titsForm_simpleRoot_left]

/-- Coordinate-free reflection formula for the graph reflection. -/
theorem simpleReflection_eq_sub_titsForm_smul
    (G : SimpleGraph L) (i : L) (z : RootLattice L) :
    simpleReflection G i z =
      z - (titsForm G (simpleRoot i) z) • simpleRoot i := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [simpleReflection_apply_self, titsForm_simpleRoot_left]
    simp
    ring
  · rw [simpleReflection_apply_of_ne G hji]
    simp [simpleRoot_apply_of_ne hji]

theorem titsForm_simpleRoot_self (G : SimpleGraph L) (i : L) :
    titsForm G (simpleRoot i) (simpleRoot i) = 2 := by
  rw [titsForm_simpleRoot_left]
  rw [show neighborSum G i (simpleRoot i) = 0 by
    unfold neighborSum
    apply Finset.sum_eq_zero
    intro h hh
    rw [simpleRoot_apply_of_ne]
    intro hhi
    subst h
    simp at hh]
  simp

/-- Each simple reflection preserves the Tits form. -/
theorem simpleReflection_preserves_titsForm
    (G : SimpleGraph L) (i : L) (z w : RootLattice L) :
    titsForm G (simpleReflection G i z) (simpleReflection G i w) =
      titsForm G z w := by
  rw [simpleReflection_eq_sub_titsForm_smul,
    simpleReflection_eq_sub_titsForm_smul]
  simp_rw [titsForm_sub_left, titsForm_sub_right,
    titsForm_zsmul_left, titsForm_zsmul_right,
    titsForm_simpleRoot_self, titsForm_simpleRoot_left,
    titsForm_simpleRoot_right]
  ring

/-- The full geometric representation preserves the Tits form. -/
theorem geometricRepresentation_preserves_titsForm
    (G : SimpleGraph L) (w : Group G) (z y : RootLattice L) :
    titsForm G (geometricRepresentation G w z)
        (geometricRepresentation G w y) = titsForm G z y := by
  induction w using (system G).simple_induction_left with
  | one => simp
  | mul_simple_left w i ih =>
      rw [map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        geometricRepresentation_simple]
      simp only [simpleReflectionEquiv_apply]
      rw [simpleReflection_preserves_titsForm, ih]

/-- Tits root signs make the graph geometric representation faithful. -/
theorem geometricRepresentation_injective (G : SimpleGraph L) :
    Function.Injective (geometricRepresentation G) := by
  intro w v hwv
  have hkernel : geometricRepresentation G (w⁻¹ * v) = 1 := by
    rw [map_mul, map_inv, hwv]
    simp
  have hgroup : w⁻¹ * v = 1 := by
    by_contra hne
    obtain ⟨i, hi⟩ := (system G).exists_rightDescent_of_ne_one hne
    have hneg :=
      rightDescentImpliesNegativeRoot_of_hasGlobalRootSignCompatibility
        G (globalRootSignCompatibility G) (w⁻¹ * v) i hi
    have hpos : IsPositive
        (geometricRepresentation G (w⁻¹ * v) (simpleRoot i)) := by
      rw [hkernel]
      simpa using simpleRoot_isPositive i
    exact hpos.not_isNegative hneg
  exact inv_mul_eq_one.mp hgroup

/-- Transport of a simple root transports its reflection. -/
theorem rootTransportDeterminesReflection
    (G : SimpleGraph L) : RootTransportDeterminesReflection G := by
  intro w i j hroot
  apply geometricRepresentation_injective G
  ext z
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    geometricRepresentation_simple, geometricRepresentation_simple]
  simp only [simpleReflectionEquiv_apply]
  rw [simpleReflection_eq_sub_titsForm_smul,
    simpleReflection_eq_sub_titsForm_smul, map_sub, map_zsmul, hroot]
  rw [← hroot, geometricRepresentation_preserves_titsForm]

/-- The geometric deletion/exchange step no longer needs a supplied
faithfulness or reflection-transport hypothesis. -/
theorem exists_eraseIdx_of_wordRoot_negative_unconditional
    (G : SimpleGraph L) (Q : List L) (i : L)
    (hnegative :
      IsNegative (geometricRepresentation G (wordProd G Q) (simpleRoot i))) :
    ∃ k, k < Q.length ∧
      wordProd G (Q.concat i) = wordProd G (Q.eraseIdx k) :=
  exists_eraseIdx_of_wordRoot_negative G (realRootSignDichotomy G)
    (rootTransportDeterminesReflection G) Q i hnegative

end OpConjecture.RepresentationDirected.RootSignStrategy
