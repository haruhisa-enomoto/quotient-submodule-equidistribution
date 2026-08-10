import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coordinate idempotents for a split basic semisimple quotient

This file isolates the general ring-theoretic part of the split-basic
realization.  An explicit equivalence

`B / jacobson B ≃ₐ[K] (i → K)`

lifts the standard coordinate idempotents to a complete orthogonal family in
`B`.  Every off-diagonal Peirce corner, and every corner between one lifted
coordinate and its complement, lies in the Jacobson radical.
-/

noncomputable section

namespace OpConjecture.SplitBasicCoordinateSystem

universe u v

variable {K B : Type u} {I : Type v}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]
  [Fintype I] [DecidableEq I]

/-- An explicit split basic description of the semisimple quotient. -/
structure QuotientCoordinateData where
  quotientEquiv : (B ⧸ Ring.jacobson B) ≃ₐ[K] (I → K)

namespace QuotientCoordinateData

variable (D : QuotientCoordinateData (K := K) (B := B) (I := I))

/-- The coordinate idempotent in the semisimple quotient. -/
def quotientCoordinate (i : I) : B ⧸ Ring.jacobson B :=
  D.quotientEquiv.symm (Pi.single i 1)

omit [IsArtinianRing B] in
theorem quotientCoordinate_complete :
    CompleteOrthogonalIdempotents D.quotientCoordinate := by
  change CompleteOrthogonalIdempotents
    (fun i : I ↦ D.quotientEquiv.symm (Pi.single i 1))
  simpa [Function.comp_def] using
    ((CompleteOrthogonalIdempotents.single (fun _ : I ↦ K)).map
      D.quotientEquiv.symm.toRingHom)

private theorem jacobson_element_nilpotent
    (x : B)
    (hx : x ∈ RingHom.ker (Ideal.Quotient.mk (Ring.jacobson B))) :
    IsNilpotent x := by
  have hnil : IsNilpotent (Ring.jacobson B) := by
    simpa only [Ideal.jacobson_bot] using
      (IsArtinianRing.isNilpotent_jacobson_bot (R := B))
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  have hxJ : x ∈ Ring.jacobson B := by
    simpa [RingHom.mem_ker] using hx
  have hxpow : x ^ n ∈ (Ring.jacobson B) ^ n := Ideal.pow_mem_pow hxJ n
  rw [show (Ring.jacobson B) ^ n = ⊥ from hn] at hxpow
  simpa using hxpow

theorem exists_liftedCoordinate :
    ∃ e : I → B,
      CompleteOrthogonalIdempotents e ∧
        (Ideal.Quotient.mk (Ring.jacobson B)) ∘ e = D.quotientCoordinate := by
  apply D.quotientCoordinate_complete.lift_of_isNilpotent_ker
    (Ideal.Quotient.mk (Ring.jacobson B))
      (jacobson_element_nilpotent (B := B))
  intro i
  exact Ideal.Quotient.mk_surjective _

/-- A chosen lift of the coordinate idempotents. -/
noncomputable def liftedCoordinate (i : I) : B :=
  D.exists_liftedCoordinate.choose i

theorem liftedCoordinate_complete :
    CompleteOrthogonalIdempotents D.liftedCoordinate :=
  D.exists_liftedCoordinate.choose_spec.1

theorem quotient_mk_liftedCoordinate (i : I) :
    Ideal.Quotient.mk (Ring.jacobson B) (D.liftedCoordinate i) =
      D.quotientCoordinate i :=
  congrFun D.exists_liftedCoordinate.choose_spec.2 i

theorem liftedCoordinate_ne_zero (i : I) : D.liftedCoordinate i ≠ 0 := by
  intro hi
  have hq : D.quotientCoordinate i = 0 := by
    rw [← D.quotient_mk_liftedCoordinate i, hi, map_zero]
  have hs : (Pi.single i (1 : K) : I → K) = 0 := by
    have hs' := congrArg D.quotientEquiv hq
    rw [quotientCoordinate, D.quotientEquiv.apply_symm_apply, map_zero] at hs'
    exact hs'
  have hsi : (1 : K) = 0 := by
    simpa [Pi.single_apply] using congrFun hs i
  exact one_ne_zero hsi

/-- A lifted coordinate is not the identity as soon as there is another
coordinate. -/
theorem liftedCoordinate_ne_one_of_exists_ne
    (i : I) (hother : ∃ j : I, j ≠ i) : D.liftedCoordinate i ≠ 1 := by
  intro hi
  obtain ⟨j, hji⟩ := hother
  apply D.liftedCoordinate_ne_zero j
  have hzero :
      D.liftedCoordinate j * D.liftedCoordinate i = 0 :=
    D.liftedCoordinate_complete.ortho hji
  simpa [hi] using hzero

/-- Distinct lifted coordinates have every Peirce corner in the radical. -/
theorem offDiagonal_mem_jacobson {i j : I} (hij : i ≠ j) (r : B) :
    D.liftedCoordinate i * r * D.liftedCoordinate j ∈ Ring.jacobson B := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply D.quotientEquiv.injective
  simp only [map_zero, map_mul]
  rw [D.quotient_mk_liftedCoordinate, D.quotient_mk_liftedCoordinate]
  simp only [quotientCoordinate, D.quotientEquiv.apply_symm_apply]
  ext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · simp [hki]

/-- The corner from one lifted coordinate to its complementary idempotent is
contained in the radical. -/
theorem coordinate_complement_mem_jacobson (i : I) (r : B) :
    D.liftedCoordinate i * r * (1 - D.liftedCoordinate i) ∈
      Ring.jacobson B := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply D.quotientEquiv.injective
  simp only [map_zero, map_mul, map_sub, map_one]
  rw [D.quotient_mk_liftedCoordinate]
  simp only [quotientCoordinate, D.quotientEquiv.apply_symm_apply]
  ext k
  by_cases hki : k = i
  · subst k
    simp
  · simp [hki]

/-- The reverse corner from the complementary idempotent to one lifted
coordinate is contained in the radical. -/
theorem complement_coordinate_mem_jacobson (i : I) (r : B) :
    (1 - D.liftedCoordinate i) * r * D.liftedCoordinate i ∈
      Ring.jacobson B := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply D.quotientEquiv.injective
  simp only [map_zero, map_mul, map_sub, map_one]
  rw [D.quotient_mk_liftedCoordinate]
  simp only [quotientCoordinate, D.quotientEquiv.apply_symm_apply]
  ext k
  by_cases hki : k = i
  · subst k
    simp
  · simp [hki]

/-- The lifted coordinate idempotents define an algebra section of the
split-basic semisimple quotient. -/
def coordinateSection : (I → K) →ₐ[K] B := by
  let e := D.liftedCoordinate
  refine
    { toFun := fun x ↦ ∑ i, x i • e i
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_
      commutes' := ?_ }
  · simpa [e] using D.liftedCoordinate_complete.complete
  · intro x y
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [smul_mul_smul_comm, D.liftedCoordinate_complete.idem i]
      rfl
    · intro j hj hji
      rw [smul_mul_smul_comm,
        D.liftedCoordinate_complete.ortho hji.symm, smul_zero]
    · simp
  · simp
  · intro x y
    simp [add_smul, Finset.sum_add_distrib]
  · intro r
    rw [show algebraMap K (I → K) r = fun _ ↦ r from rfl]
    rw [← Finset.smul_sum]
    rw [D.liftedCoordinate_complete.complete]
    simp [Algebra.smul_def]

theorem coordinateSection_apply (x : I → K) :
    D.coordinateSection x = ∑ i, x i • D.liftedCoordinate i :=
  rfl

/-- Projecting the coordinate section back to the chosen semisimple
coordinates is the identity. -/
theorem quotient_coordinateSection (x : I → K) :
    D.quotientEquiv
        (Ideal.Quotient.mk (Ring.jacobson B) (D.coordinateSection x)) = x := by
  change D.quotientEquiv
    ((Ideal.Quotient.mkₐ K (Ring.jacobson B)) (D.coordinateSection x)) = x
  ext i
  simp [D.coordinateSection_apply, D.quotient_mk_liftedCoordinate,
    quotientCoordinate]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

/-- The quotient map expressed in the chosen coordinate system. -/
def coordinateProjection : B →ₐ[K] (I → K) :=
  D.quotientEquiv.toAlgHom.comp
    (Ideal.Quotient.mkₐ K (Ring.jacobson B))

@[simp]
theorem coordinateProjection_coordinateSection (x : I → K) :
    D.coordinateProjection (D.coordinateSection x) = x :=
  D.quotient_coordinateSection x

omit [IsArtinianRing B] [Fintype I] [DecidableEq I] in
@[simp]
theorem coordinateProjection_radical (x : Ring.jacobson B) :
    D.coordinateProjection x = 0 := by
  change D.quotientEquiv
    (Ideal.Quotient.mk (Ring.jacobson B) (x : B)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property, map_zero]

/-- The radical remainder after subtracting the chosen semisimple
representative. -/
def radicalRemainder (b : B) : Ring.jacobson B :=
  ⟨b - D.coordinateSection (D.coordinateProjection b), by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply D.quotientEquiv.injective
    simp [coordinateProjection, D.quotient_coordinateSection]⟩

@[simp]
theorem coe_radicalRemainder (b : B) :
    (D.radicalRemainder b : B) =
      b - D.coordinateSection (D.coordinateProjection b) :=
  rfl

/-- The canonical vector-space decomposition of a split basic algebra into
its coordinate semisimple part and its Jacobson radical. -/
def splitRadicalLinearEquiv :
    ((I → K) × Ring.jacobson B) ≃ₗ[K] B where
  toFun p := D.coordinateSection p.1 + p.2
  invFun b := (D.coordinateProjection b, D.radicalRemainder b)
  map_add' x y := by
    change D.coordinateSection (x.1 + y.1) + ((x.2 : B) + y.2) =
      (D.coordinateSection x.1 + x.2) +
        (D.coordinateSection y.1 + y.2)
    rw [map_add]
    abel
  map_smul' r x := by simp
  left_inv x := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp
  right_inv b := by
    simp

omit [IsArtinianRing B] [Fintype I] [DecidableEq I] in
/-- Products of radical elements vanish when the Jacobson radical is
square-zero. -/
theorem radical_mul_eq_zero_of_sq_eq_bot
    (hJ : (Ring.jacobson B) ^ 2 = ⊥)
    (x y : Ring.jacobson B) : (x : B) * y = 0 := by
  have hxy : (x : B) * y ∈ (Ring.jacobson B) ^ 2 := by
    rw [show (2 : ℕ) = 1 + 1 by omega, Submodule.pow_succ,
      Submodule.pow_one]
    exact Ideal.mul_mem_mul x.property y.property
  rw [hJ] at hxy
  simpa using hxy

/-- Under `J² = 0`, multiplication in the split-radical decomposition is
the usual square-zero-extension multiplication. -/
theorem splitRadicalLinearEquiv_mul
    (hJ : (Ring.jacobson B) ^ 2 = ⊥)
    (x y : (I → K) × Ring.jacobson B) :
    D.splitRadicalLinearEquiv x * D.splitRadicalLinearEquiv y =
      D.coordinateSection (x.1 * y.1) +
        D.coordinateSection x.1 * (y.2 : B) +
        (x.2 : B) * D.coordinateSection y.1 := by
  change
    (D.coordinateSection x.1 + (x.2 : B)) *
        (D.coordinateSection y.1 + (y.2 : B)) = _
  rw [add_mul, mul_add, mul_add, map_mul,
    radical_mul_eq_zero_of_sq_eq_bot hJ x.2 y.2, add_zero]

end QuotientCoordinateData

end OpConjecture.SplitBasicCoordinateSystem
