import OpConjecture.RepresentationTheory.SplitBasicQuotient

/-!
# Conventional basicness and split quotient coordinates

For a finite-dimensional algebra, basicness may be expressed by saying that
the semisimple quotient is reduced: equivalently, every Wedderburn matrix
block has size one.  Over an algebraically closed field this is equivalent to
commutativity of the semisimple quotient, and hence to the intrinsic
split-basic quotient condition used by the coordinate development.
-/

noncomputable section

namespace OpConjecture.BasicnessWrapper

universe u

/-- Standard ring-theoretic basicness for a finite-dimensional algebra:
every matrix block in its semisimple quotient has size one. -/
def IsBasicAlgebra (K B : Type u)
    [Field K] [Ring B] [Algebra K B] [FiniteDimensional K B] : Prop :=
  IsReduced (B ⧸ Ring.jacobson B)

private theorem fin_subsingleton_of_pi_matrix_reduced
    (K : Type u) [Field K]
    {n : ℕ} {d : Fin n → ℕ}
    [IsReduced (∀ i, Matrix (Fin (d i)) (Fin (d i)) K)]
    (i : Fin n) : Subsingleton (Fin (d i)) := by
  constructor
  intro a b
  by_contra hab
  let z : ∀ j, Matrix (Fin (d j)) (Fin (d j)) K :=
    Pi.single i (Matrix.single a b 1)
  have hzpow : z ^ 2 = 0 := by
    ext j p q
    by_cases hji : j = i
    · subst j
      simp only [z, Pi.single_eq_same, Pi.pow_apply, Pi.zero_apply, pow_two]
      simp only [Matrix.mul_apply, Matrix.single, Matrix.of_apply]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hax : a = x
      · subst x
        have hba : b ≠ a := Ne.symm hab
        simp [hba]
      · simp [hax]
    · simp [z, hji]
  have hz : z = 0 := IsReduced.eq_zero z ⟨2, hzpow⟩
  have hone : (1 : K) = 0 := by
    have := congrArg (fun w ↦ w i a b) hz
    simp [z, Matrix.single] at this
  exact one_ne_zero hone

variable (K B : Type u)
  [Field K] [IsAlgClosed K] [Ring B] [Algebra K B]
  [FiniteDimensional K B]

omit [IsAlgClosed K] in
/-- A commutative semisimple quotient is reduced, so it is basic.  This
implication does not use algebraic closedness. -/
theorem isBasicAlgebra_of_quotient_mul_comm
    (hcomm : ∀ x y : B ⧸ Ring.jacobson B, x * y = y * x) :
    IsBasicAlgebra K B := by
  let Q := B ⧸ Ring.jacobson B
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI : CommRing Q :=
    { (inferInstance : Ring Q) with
      mul_comm := hcomm }
  letI : IsSemisimpleRing Q := inferInstance
  exact (inferInstance : IsReduced Q)

/-- Over an algebraically closed field, conventional basicness makes the
semisimple quotient commutative. -/
theorem quotient_mul_comm_of_isBasicAlgebra
    (h : IsBasicAlgebra K B) :
    ∀ x y : B ⧸ Ring.jacobson B, x * y = y * x := by
  let Q := B ⧸ Ring.jacobson B
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI : FiniteDimensional K Q := inferInstance
  letI : IsReduced Q := h
  letI : IsSemisimpleRing Q := inferInstance
  obtain ⟨n, d, _hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed K Q
  letI : IsReduced (∀ i, Matrix (Fin (d i)) (Fin (d i)) K) :=
    isReduced_of_injective e.symm e.symm.injective
  have hsub (i : Fin n) : Subsingleton (Fin (d i)) :=
    fin_subsingleton_of_pi_matrix_reduced K i
  intro x y
  apply e.injective
  rw [map_mul, map_mul]
  ext i a b
  haveI : Subsingleton (Fin (d i)) := hsub i
  change
    (∑ j, e x i a j * e y i j b) =
      ∑ j, e y i a j * e x i j b
  apply Finset.sum_congr rfl
  intro j _
  rw [Subsingleton.elim a j, Subsingleton.elim b j, mul_comm]

/-- Over an algebraically closed field, conventional basicness is exactly
commutativity of the semisimple quotient. -/
theorem isBasicAlgebra_iff_quotient_mul_comm :
    IsBasicAlgebra K B ↔
      ∀ x y : B ⧸ Ring.jacobson B, x * y = y * x :=
  ⟨quotient_mul_comm_of_isBasicAlgebra K B,
    isBasicAlgebra_of_quotient_mul_comm K B⟩

/-- Conventional basicness over an algebraically closed field supplies the
intrinsic split-basic condition already used downstream. -/
theorem isSplitBasicQuotient_of_isBasicAlgebra
    (h : IsBasicAlgebra K B) :
    OpConjecture.SplitBasicQuotient.IsSplitBasicQuotient K B :=
  OpConjecture.SplitBasicQuotient.isSplitBasicQuotient_of_quotient_mul_comm
    K B (quotient_mul_comm_of_isBasicAlgebra K B h)

/-- In the finite-dimensional algebraically closed setting, conventional
basicness and the downstream intrinsic split-basic quotient predicate are
equivalent. -/
theorem isBasicAlgebra_iff_isSplitBasicQuotient :
    IsBasicAlgebra K B ↔
      OpConjecture.SplitBasicQuotient.IsSplitBasicQuotient K B := by
  constructor
  · exact isSplitBasicQuotient_of_isBasicAlgebra K B
  · rintro ⟨hcomm, _⟩
    exact isBasicAlgebra_of_quotient_mul_comm K B hcomm

/-- Conventional basicness over an algebraically closed field supplies an
explicit finite coordinate presentation of the semisimple quotient. -/
theorem exists_quotientCoordinateData_of_isBasicAlgebra
    (h : IsBasicAlgebra K B) :
    ∃ n : ℕ,
      Nonempty
        (OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData
          (K := K) (B := B) (I := Fin n)) :=
  OpConjecture.SplitBasicQuotient.exists_quotientCoordinateData_of_isSplitBasicQuotient
    (isSplitBasicQuotient_of_isBasicAlgebra K B h)

end OpConjecture.BasicnessWrapper
