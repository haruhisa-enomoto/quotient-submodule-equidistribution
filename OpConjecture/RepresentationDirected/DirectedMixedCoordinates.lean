import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Integral mixed coordinates for directed Hom matrices

This file isolates the numerical core of the manuscript's mixed-basis
construction.  An upper unitriangular integral matrix remains upper
unitriangular after selected columns are replaced by standard-basis columns.
Its inverse therefore defines integral mixed coordinates.

The retained-submatrix results give uniqueness after restriction and the
one-step coordinate transport used by the effective-lifting induction.  No
functor category or Grothendieck group is needed for these statements.
-/

noncomputable section

open Matrix

namespace OpConjecture.RepresentationDirected

universe uI

namespace UpperUnitriangular

variable {I : Type uI} [Fintype I] [LinearOrder I]

/-- Replace the columns in `D` by the corresponding standard-basis
columns. -/
noncomputable def mixedMatrix (H : Matrix I I ℤ) (D : Finset I) : Matrix I I ℤ := by
  classical
  exact fun a j => if j ∈ D then if a = j then 1 else 0 else H a j

omit [Fintype I] in
@[simp]
theorem mixedMatrix_apply_of_mem (H : Matrix I I ℤ) (D : Finset I)
    {a j : I} (hj : j ∈ D) :
    mixedMatrix H D a j = if a = j then 1 else 0 := by
  simp [mixedMatrix, hj]

omit [Fintype I] in
@[simp]
theorem mixedMatrix_apply_of_not_mem (H : Matrix I I ℤ) (D : Finset I)
    {a j : I} (hj : j ∉ D) :
    mixedMatrix H D a j = H a j := by
  simp [mixedMatrix, hj]

omit [Fintype I] in
theorem mixedMatrix_blockTriangular (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) :
    (mixedMatrix H D).BlockTriangular id := by
  intro i j hji
  by_cases hj : j ∈ D
  · have hne : i ≠ j := by
      intro hij
      subst j
      exact (lt_irrefl i) hji
    simp [mixedMatrix, hj, hne]
  · simpa [mixedMatrix, hj] using hupper hji

omit [Fintype I] in
theorem mixedMatrix_diagonal (H : Matrix I I ℤ) (D : Finset I)
    (hdiag : ∀ i, H i i = 1) (i : I) :
    mixedMatrix H D i i = 1 := by
  by_cases hi : i ∈ D <;> simp [mixedMatrix, hi, hdiag]

theorem mixedMatrix_det (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) (hdiag : ∀ i, H i i = 1) :
    (mixedMatrix H D).det = 1 := by
  rw [Matrix.det_of_upperTriangular
    (mixedMatrix_blockTriangular H D hupper)]
  simp [mixedMatrix_diagonal H D hdiag]

theorem mixedMatrix_isUnit (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) (hdiag : ∀ i, H i i = 1) :
    IsUnit (mixedMatrix H D) := by
  rw [Matrix.isUnit_iff_isUnit_det, mixedMatrix_det H D hupper hdiag]
  exact isUnit_one

/-- Integral coordinates in the mixed columns. -/
def coordinates (H : Matrix I I ℤ) (D : Finset I) (v : I → ℤ) : I → ℤ :=
  (mixedMatrix H D)⁻¹ *ᵥ v

theorem mixedMatrix_mulVec_coordinates (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) (hdiag : ∀ i, H i i = 1)
    (v : I → ℤ) :
    mixedMatrix H D *ᵥ coordinates H D v = v := by
  rw [coordinates, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _
      (by rw [mixedMatrix_det H D hupper hdiag]; exact isUnit_one),
    Matrix.one_mulVec]

theorem coordinates_eq_of_mulVec_eq (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) (hdiag : ∀ i, H i i = 1)
    {v x : I → ℤ} (hx : mixedMatrix H D *ᵥ x = v) :
    coordinates H D v = x := by
  rw [coordinates, ← hx, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _
      (by rw [mixedMatrix_det H D hupper hdiag]; exact isUnit_one),
    Matrix.one_mulVec]

theorem coordinates_add (H : Matrix I I ℤ) (D : Finset I)
    (v w : I → ℤ) :
    coordinates H D (v + w) = coordinates H D v + coordinates H D w := by
  simp [coordinates, Matrix.mulVec_add]

theorem coordinates_zero (H : Matrix I I ℤ) (D : Finset I) :
    coordinates H D 0 = 0 := by
  simp [coordinates]

/-- Mixed coordinates commute with finite sums. -/
theorem coordinates_sum {J : Type*} [Fintype J]
    (H : Matrix I I ℤ) (D : Finset I) (v : J → I → ℤ) :
    coordinates H D (∑ j, v j) = ∑ j, coordinates H D (v j) := by
  classical
  have hsum : ∀ s : Finset J,
      coordinates H D (∑ j ∈ s, v j) =
        ∑ j ∈ s, coordinates H D (v j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [coordinates_zero]
    | @insert j s hj ih =>
        simp only [Finset.sum_insert hj]
        rw [coordinates_add, ih]
  exact hsum Finset.univ

theorem coordinates_retained_column (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) (hdiag : ∀ i, H i i = 1)
    {j : I} (hj : j ∉ D) :
    coordinates H D (H.col j) = Pi.single j 1 := by
  apply coordinates_eq_of_mulVec_eq H D hupper hdiag
  rw [Matrix.mulVec_single_one]
  ext a
  simp [mixedMatrix, hj]

/-- The matrix subsystem on the positions retained outside `D`. -/
def retainedMatrix (H : Matrix I I ℤ) (D : Finset I) :
    Matrix {i // i ∉ D} {i // i ∉ D} ℤ :=
  H.submatrix Subtype.val Subtype.val

omit [Fintype I] in
theorem retainedMatrix_blockTriangular (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) :
    (retainedMatrix H D).BlockTriangular id := by
  intro i j hji
  exact hupper hji

omit [Fintype I] [LinearOrder I] in
theorem retainedMatrix_diagonal (H : Matrix I I ℤ) (D : Finset I)
    (hdiag : ∀ i, H i i = 1) (i : {i // i ∉ D}) :
    retainedMatrix H D i i = 1 := hdiag i

theorem retainedMatrix_det (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) (hdiag : ∀ i, H i i = 1) :
    (retainedMatrix H D).det = 1 := by
  classical
  rw [Matrix.det_of_upperTriangular
    (retainedMatrix_blockTriangular H D hupper)]
  simp [retainedMatrix_diagonal H D hdiag]

theorem retainedMatrix_isUnit (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) (hdiag : ∀ i, H i i = 1) :
    IsUnit (retainedMatrix H D) := by
  classical
  rw [Matrix.isUnit_iff_isUnit_det, retainedMatrix_det H D hupper hdiag]
  exact isUnit_one

theorem retainedMatrix_mulVec_injective (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) (hdiag : ∀ i, H i i = 1) :
    Function.Injective (retainedMatrix H D).mulVec := by
  classical
  exact Matrix.mulVec_injective_of_isUnit
    (retainedMatrix_isUnit H D hupper hdiag)

/-- On a retained row, omitted standard-basis columns vanish, so the mixed
matrix equation is exactly the retained matrix equation. -/
theorem mixedMatrix_mulVec_apply_retained (H : Matrix I I ℤ) (D : Finset I)
    (x : I → ℤ) {a : I} (ha : a ∉ D) :
    (mixedMatrix H D *ᵥ x) a =
      (retainedMatrix H D *ᵥ fun j => x j.1) ⟨a, ha⟩ := by
  classical
  simp only [Matrix.mulVec, dotProduct, retainedMatrix, Matrix.submatrix_apply]
  calc
    (∑ j, mixedMatrix H D a j * x j) =
        (∑ j ∈ Finset.univ.filter (fun j => j ∉ D),
          mixedMatrix H D a j * x j) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hj
      have hjD : j ∈ D := by simpa using hj
      have haj : a ≠ j := by
        intro haj
        subst j
        exact ha hjD
      simp [mixedMatrix, hjD, haj]
    _ = (∑ j : {j // j ∉ D}, mixedMatrix H D a j.1 * x j.1) := by
      exact Finset.sum_subtype _ (by simp) _
    _ = (∑ j : {j // j ∉ D}, H a j.1 * x j.1) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [mixedMatrix_apply_of_not_mem H D j.2]

/-- The retained coordinates give the restricted vector expansion. -/
theorem retained_expansion (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) (hdiag : ∀ i, H i i = 1)
    (v : I → ℤ) {a : I} (ha : a ∉ D) :
    v a = (retainedMatrix H D *ᵥ
      fun j => coordinates H D v j.1) ⟨a, ha⟩ := by
  rw [← mixedMatrix_mulVec_apply_retained H D _ ha,
    mixedMatrix_mulVec_coordinates H D hupper hdiag]

/-- A vector's retained mixed coordinates are determined uniquely by its
values on the retained rows. -/
theorem coordinates_eq_on_retained_of_eq_on_retained
    (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) (hdiag : ∀ i, H i i = 1)
    {v w : I → ℤ} (hvw : ∀ a, a ∉ D → v a = w a)
    {a : I} (ha : a ∉ D) :
    coordinates H D v a = coordinates H D w a := by
  classical
  have hcoordinates :
      (fun j : {j // j ∉ D} => coordinates H D v j.1) =
        (fun j : {j // j ∉ D} => coordinates H D w j.1) := by
    apply retainedMatrix_mulVec_injective H D hupper hdiag
    funext b
    rw [← retained_expansion H D hupper hdiag v b.2,
      ← retained_expansion H D hupper hdiag w b.2]
    exact hvw b.1 b.2
  exact congrFun hcoordinates ⟨a, ha⟩

/-- If two mixed-coordinate vectors agree at every retained position except
`i`, then their values in row `i` differ by exactly the `i`-coordinate
difference. -/
theorem value_eq_add_coordinate_sub
    (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) (hdiag : ∀ j, H j j = 1)
    {i : I} (v w : I → ℤ)
    (hcoordinates : ∀ j, j ∉ insert i D →
      coordinates H D v j = coordinates H D w j) :
    v i = w i + coordinates H D v i - coordinates H D w i := by
  classical
  let B := mixedMatrix H D
  let cv := coordinates H D v
  let cw := coordinates H D w
  have hexpand (x : I → ℤ) :
      x i = coordinates H D x i +
        ∑ j ∈ Finset.univ.erase i,
          B i j * coordinates H D x j := by
    calc
      x i = Matrix.mulVec (mixedMatrix H D) (coordinates H D x) i :=
        (congrFun
          (mixedMatrix_mulVec_coordinates H D hupper hdiag x) i).symm
      _ = ∑ j, B i j * coordinates H D x j := rfl
      _ = coordinates H D x i +
          ∑ j ∈ Finset.univ.erase i,
            B i j * coordinates H D x j := by
        rw [← Finset.sum_erase_add Finset.univ
          (fun j => B i j * coordinates H D x j) (Finset.mem_univ i)]
        simp [B, mixedMatrix_diagonal H D hdiag, add_comm]
  have hrest :
      (∑ j ∈ Finset.univ.erase i, B i j * cv j) =
        ∑ j ∈ Finset.univ.erase i, B i j * cw j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    by_cases hjD : j ∈ D
    · have hij : i ≠ j := Ne.symm hji
      simp [B, hjD, hij]
    · have hjinsert : j ∉ insert i D := by
        simp [hji, hjD]
      dsimp only [cv, cw]
      rw [hcoordinates j hjinsert]
  rw [hexpand v, hexpand w]
  change cv i + (∑ j ∈ Finset.univ.erase i, B i j * cv j) =
    cw i + (∑ j ∈ Finset.univ.erase i, B i j * cw j) + cv i - cw i
  rw [hrest]
  ring

omit [Fintype I] in
/-- If the newly omitted column is zero on all rows that remain retained,
then inserting that column does not change those rows of the mixed matrix. -/
theorem mixedMatrix_apply_insert_of_column_zero
    (H : Matrix I I ℤ) (D : Finset I) {i a j : I}
    (hi : i ∉ D) (ha : a ∉ insert i D) (hai : H a i = 0) :
    mixedMatrix H (insert i D) a j = mixedMatrix H D a j := by
  classical
  by_cases hji : j = i
  · subst j
    have hne : a ≠ i := by
      intro hai'
      subst a
      exact ha (Finset.mem_insert_self i D)
    simp [mixedMatrix, hi, hne, hai]
  · by_cases hjD : j ∈ D
    · have hne : a ≠ j := by
        intro haj
        subst a
        exact ha (Finset.mem_insert_of_mem hjD)
      simp [mixedMatrix, hjD, hne]
    · simp [mixedMatrix, hji, hjD]

/-- One-step deletion transport for mixed coordinates.  The zero-column
hypothesis is the numerical form of choosing a newly deleted object which
receives no map from the remaining retained objects. -/
theorem coordinates_insert_eq_of_column_zero
    (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) (hdiag : ∀ i, H i i = 1)
    {i : I} (hi : i ∉ D)
    (hzero : ∀ a, a ∉ insert i D → H a i = 0)
    (v : I → ℤ) {a : I} (ha : a ∉ insert i D) :
    coordinates H (insert i D) v a = coordinates H D v a := by
  classical
  have hcoordinates :
      (fun j : {j // j ∉ insert i D} =>
          coordinates H (insert i D) v j.1) =
        (fun j : {j // j ∉ insert i D} =>
          coordinates H D v j.1) := by
    apply retainedMatrix_mulVec_injective H (insert i D) hupper hdiag
    funext b
    rw [← mixedMatrix_mulVec_apply_retained H (insert i D) _ b.2,
      mixedMatrix_mulVec_coordinates H (insert i D) hupper hdiag]
    calc
      v b.1 = (mixedMatrix H D *ᵥ coordinates H D v) b.1 := by
        rw [mixedMatrix_mulVec_coordinates H D hupper hdiag]
      _ = (mixedMatrix H (insert i D) *ᵥ coordinates H D v) b.1 := by
        simp only [Matrix.mulVec, dotProduct]
        apply Finset.sum_congr rfl
        intro j _
        rw [mixedMatrix_apply_insert_of_column_zero H D hi b.2
          (hzero b.1 b.2)]
      _ = (retainedMatrix H (insert i D) *ᵥ
          fun j => coordinates H D v j.1) b :=
        mixedMatrix_mulVec_apply_retained H (insert i D) _ b.2
  exact congrFun hcoordinates ⟨a, ha⟩

/-- `Finset.cons` version of one-step deletion transport, avoiding a
caller-visible decidable-equality choice. -/
theorem coordinates_cons_eq_of_column_zero
    (H : Matrix I I ℤ) (D : Finset I)
    (hupper : H.BlockTriangular id) (hdiag : ∀ i, H i i = 1)
    {i : I} (hi : i ∉ D)
    (hzero : ∀ a, a ∉ D.cons i hi → H a i = 0)
    (v : I → ℤ) {a : I} (ha : a ∉ D.cons i hi) :
    coordinates H (D.cons i hi) v a = coordinates H D v a := by
  simpa only [Finset.cons_eq_insert] using
    coordinates_insert_eq_of_column_zero H D hupper hdiag hi
      (by simpa only [← Finset.cons_eq_insert i D hi] using hzero)
      v (by simpa only [← Finset.cons_eq_insert i D hi] using ha)

end UpperUnitriangular

end OpConjecture.RepresentationDirected
