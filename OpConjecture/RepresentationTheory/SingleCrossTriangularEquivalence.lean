import OpConjecture.RepresentationTheory.SingleCrossRadicalNormalForm
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# A single cross radical gives the triangular A2 algebra

This file is the pure algebra recognition step at the hereditary two-simple,
three-indecomposable boundary.  It defines an abstract three-dimensional
triangular algebra and proves that a split two-coordinate algebra with one
nonzero cross-radical generator is isomorphic to it.

The argument uses only the coordinate idempotents and the radical normal
form.  It does not use a quiver presentation or a classification of modules.
-/

noncomputable section

open scoped RightActions

namespace OpConjecture.A2Triangular

universe u

variable (K : Type u) [Field K]

/-- The diagonal algebra of the triangular model. -/
abbrev Base := K × K

/-- The one-dimensional off-diagonal corner.  A wrapper keeps its asymmetric
`K × K` actions from installing nonstandard module instances on `K` itself. -/
structure Arrow where
  value : K

omit [Field K] in
@[ext]
theorem Arrow.ext {x y : Arrow K} (h : x.value = y.value) : x = y := by
  cases x
  cases y
  simp_all

/-- The arrow wrapper is additively the ground field. -/
def Arrow.equiv : Arrow K ≃ K where
  toFun := Arrow.value
  invFun := Arrow.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (Arrow K) := (Arrow.equiv K).addCommGroup

@[simp]
theorem Arrow.zero_value : (0 : Arrow K).value = 0 := rfl

/-- The additive coordinate equivalence. -/
def Arrow.addEquiv : Arrow K ≃+ K where
  __ := Arrow.equiv K
  map_add' _ _ := rfl

instance : Module K (Arrow K) := (Arrow.addEquiv K).module K

@[simp]
theorem Arrow.add_value (x y : Arrow K) :
    (x + y).value = x.value + y.value := rfl

@[simp]
theorem Arrow.smul_value (c : K) (x : Arrow K) :
    (c • x).value = c * x.value := rfl

/-- The linear coordinate equivalence. -/
def Arrow.linearEquiv : Arrow K ≃ₗ[K] K where
  __ := Arrow.addEquiv K
  map_smul' _ _ := rfl

/-- Left multiplication on the arrow corner sees the second diagonal
coordinate. -/
def leftCharacter : Base K →+* K := RingHom.snd K K

instance : Module (Base K) (Arrow K) :=
  Module.compHom (Arrow K) (leftCharacter K)

/-- Right multiplication on the arrow corner sees the first diagonal
coordinate. -/
def rightCharacter : (Base K)ᵐᵒᵖ →+* K :=
  (RingHom.fst K K).fromOpposite fun _ _ => Commute.all _ _

instance : Module (Base K)ᵐᵒᵖ (Arrow K) :=
  Module.compHom (Arrow K) (rightCharacter K)

instance : SMulCommClass (Base K) (Base K)ᵐᵒᵖ (Arrow K) where
  smul_comm r s m := by
    apply Arrow.ext
    change r.2 * (s.unop.1 * m.value) = s.unop.1 * (r.2 * m.value)
    ring

instance : IsScalarTower K (Base K) (Arrow K) where
  smul_assoc c r m := by
    apply Arrow.ext
    change (c * r.2) * m.value = c * (r.2 * m.value)
    ring

instance : IsScalarTower K (Base K)ᵐᵒᵖ (Arrow K) where
  smul_assoc c r m := by
    apply Arrow.ext
    change (c * r.unop.1) * m.value = c * (r.unop.1 * m.value)
    ring

/-- The three-dimensional triangular algebra, with multiplication

`((r0,r1),a) * ((s0,s1),b) = ((r0*s0,r1*s1), r1*b + a*s0)`.

Thus the first diagonal coordinate is the right endpoint of the arrow and
the second is its left endpoint. -/
abbrev Model := TrivSqZeroExt (Base K) (Arrow K)

/-- The arrow corner has its transported one-dimensional vector-space
structure. -/
noncomputable instance Arrow.finiteDimensional :
    FiniteDimensional K (Arrow K) :=
  (Arrow.linearEquiv K).symm.finiteDimensional

noncomputable instance finiteDimensional :
    FiniteDimensional K (Model K) := by
  change Module.Finite K ((K × K) × Arrow K)
  infer_instance

theorem finrank_eq_three : Module.finrank K (Model K) = 3 := by
  have harrow : Module.finrank K (Arrow K) = 1 := by
    calc
      Module.finrank K (Arrow K) = Module.finrank K K :=
        (Arrow.linearEquiv K).finrank_eq
      _ = 1 := by simp
  change Module.finrank K ((K × K) × Arrow K) = 3
  simp [harrow]

end OpConjecture.A2Triangular

namespace OpConjecture.QuotientSurvival.TwoCoordinateData

open OpConjecture.CotangentExtBridge

universe u

variable {K B : Type u}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]

variable (D : OpConjecture.QuotientSurvival.TwoCoordinateData
  (K := K) (B := B))

/-- Removing the two scalar coordinate components from an element leaves an
element of the Jacobson radical. -/
theorem diagonalRemainder_mem_jacobson (b : B) :
    b - ∑ k : Fin 2,
        CoordinateData.coordinateCharacter D k b • D.liftedCoordinate k ∈
      Ring.jacobson B := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change (Ideal.Quotient.mkₐ K (Ring.jacobson B))
      (b - ∑ k : Fin 2,
        CoordinateData.coordinateCharacter D k b • D.liftedCoordinate k) = 0
  have hq (x : Fin 2) :
      (Ideal.Quotient.mkₐ K (Ring.jacobson B)) (D.liftedCoordinate x) =
        D.quotientCoordinate x := by
    exact D.quotient_mk_liftedCoordinate x
  apply D.quotientEquiv.injective
  simp only [map_sub, map_sum, map_smul, map_zero]
  ext k
  simp_rw [hq]
  fin_cases k <;> simp [CoordinateData.coordinateCharacter,
    OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData.quotientCoordinate]

/-- Two distinct lifted coordinates, in the endpoint order used by the
triangular model, sum to one. -/
theorem liftedCoordinate_add_of_ne {i j : Fin 2} (hij : i ≠ j) :
    D.liftedCoordinate j + D.liftedCoordinate i = 1 := by
  have hcomplete := D.liftedCoordinate_complete.complete
  fin_cases i <;> fin_cases j <;> simp at hij
  · simpa [Fin.sum_univ_two, add_comm] using hcomplete
  · simpa [Fin.sum_univ_two] using hcomplete

/-- A sum over two coordinates can be ordered by any chosen distinct pair. -/
theorem sum_eq_add_of_ne {M : Type*} [AddCommMonoid M]
    {i j : Fin 2} (hij : i ≠ j) (f : Fin 2 → M) :
    (∑ k : Fin 2, f k) = f j + f i := by
  fin_cases i <;> fin_cases j <;> simp at hij
  · simp [Fin.sum_univ_two, add_comm]
  · simp [Fin.sum_univ_two]

/-- The two scalar diagonal coordinates mapped to the chosen lifted
idempotents. -/
def diagonalAlgHom {i j : Fin 2} (hij : i ≠ j) :
    OpConjecture.A2Triangular.Base K →ₐ[K] B where
  toFun r := r.1 • D.liftedCoordinate j + r.2 • D.liftedCoordinate i
  map_one' := by
    simpa only [Prod.fst_one, Prod.snd_one, one_smul] using
      D.liftedCoordinate_add_of_ne hij
  map_mul' x y := by
    change
      (x.1 * y.1) • D.liftedCoordinate j +
          (x.2 * y.2) • D.liftedCoordinate i =
        (x.1 • D.liftedCoordinate j + x.2 • D.liftedCoordinate i) *
          (y.1 • D.liftedCoordinate j + y.2 • D.liftedCoordinate i)
    simp only [mul_add, add_mul, smul_mul_smul_comm]
    rw [D.liftedCoordinate_complete.idem,
      D.liftedCoordinate_complete.ortho hij.symm,
      D.liftedCoordinate_complete.ortho hij,
      D.liftedCoordinate_complete.idem]
    simp
  map_zero' := by simp
  map_add' x y := by
    change
      (x.1 + y.1) • D.liftedCoordinate j +
          (x.2 + y.2) • D.liftedCoordinate i =
        (x.1 • D.liftedCoordinate j + x.2 • D.liftedCoordinate i) +
          (y.1 • D.liftedCoordinate j + y.2 • D.liftedCoordinate i)
    module
  commutes' c := by
    change c • D.liftedCoordinate j + c • D.liftedCoordinate i =
      algebraMap K B c
    rw [← smul_add, D.liftedCoordinate_add_of_ne hij]
    simp [Algebra.smul_def]

/-- The multiplication table determined by a cross-radical generator gives
an algebra map from the triangular model. -/
def singleCrossTriangularAlgHom
    {i j : Fin 2} (hij : i ≠ j) (a : B)
    (hL : D.liftedCoordinate i * a = a)
    (hR : a * D.liftedCoordinate j = a)
    (hdata : SingleCrossRadicalData (K := K) a) :
    OpConjecture.A2Triangular.Model K →ₐ[K] B := by
  have hja : D.liftedCoordinate j * a = 0 := by
    calc
      D.liftedCoordinate j * a =
          D.liftedCoordinate j * (D.liftedCoordinate i * a) := by rw [hL]
      _ = (D.liftedCoordinate j * D.liftedCoordinate i) * a := by
        rw [mul_assoc]
      _ = 0 := by
        rw [D.liftedCoordinate_complete.ortho hij.symm, zero_mul]
  have hai : a * D.liftedCoordinate i = 0 := by
    calc
      a * D.liftedCoordinate i =
          (a * D.liftedCoordinate j) * D.liftedCoordinate i := by rw [hR]
      _ = a * (D.liftedCoordinate j * D.liftedCoordinate i) := by
        rw [mul_assoc]
      _ = 0 := by
        rw [D.liftedCoordinate_complete.ortho hij.symm, mul_zero]
  refine TrivSqZeroExt.lift (D.diagonalAlgHom hij)
    ((LinearMap.toSpanSingleton K B a).comp
      (OpConjecture.A2Triangular.Arrow.linearEquiv K).toLinearMap) ?_ ?_ ?_
  · intro x y
    change (x.value • a) * (y.value • a) = 0
    rw [smul_mul_smul_comm, hdata.a_sq, smul_zero]
  · intro r x
    change (r.2 * x.value) • a =
      (r.1 • D.liftedCoordinate j + r.2 • D.liftedCoordinate i) *
        (x.value • a)
    symm
    rw [add_mul, smul_mul_smul_comm, smul_mul_smul_comm,
      hja, hL, smul_zero, zero_add]
  · intro r x
    change (r.1 * x.value) • a =
      (x.value • a) *
        (r.1 • D.liftedCoordinate j + r.2 • D.liftedCoordinate i)
    symm
    rw [mul_add, smul_mul_smul_comm, smul_mul_smul_comm,
      hR, hai, smul_zero, add_zero]
    rw [mul_comm]

@[simp]
theorem singleCrossTriangularAlgHom_apply
    {i j : Fin 2} (hij : i ≠ j) (a : B)
    (hL : D.liftedCoordinate i * a = a)
    (hR : a * D.liftedCoordinate j = a)
    (hdata : SingleCrossRadicalData (K := K) a)
    (x : OpConjecture.A2Triangular.Model K) :
    D.singleCrossTriangularAlgHom hij a hL hR hdata x =
      (x.fst.1 • D.liftedCoordinate j + x.fst.2 • D.liftedCoordinate i) +
        x.snd.value • a := by
  rw [singleCrossTriangularAlgHom, TrivSqZeroExt.lift_def]
  rfl

theorem coordinateCharacter_singleCrossTriangularAlgHom_right
    {i j : Fin 2} (hij : i ≠ j) (a : B)
    (hL : D.liftedCoordinate i * a = a)
    (hR : a * D.liftedCoordinate j = a)
    (hdata : SingleCrossRadicalData (K := K) a)
    (x : OpConjecture.A2Triangular.Model K) :
    CoordinateData.coordinateCharacter D j
        (D.singleCrossTriangularAlgHom hij a hL hR hdata x) = x.fst.1 := by
  rw [D.singleCrossTriangularAlgHom_apply]
  simp [CoordinateData.coordinateCharacter_liftedCoordinate_ne D hij,
    CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson
      D j hdata.a_mem_jacobson]

theorem coordinateCharacter_singleCrossTriangularAlgHom_left
    {i j : Fin 2} (hij : i ≠ j) (a : B)
    (hL : D.liftedCoordinate i * a = a)
    (hR : a * D.liftedCoordinate j = a)
    (hdata : SingleCrossRadicalData (K := K) a)
    (x : OpConjecture.A2Triangular.Model K) :
    CoordinateData.coordinateCharacter D i
        (D.singleCrossTriangularAlgHom hij a hL hR hdata x) = x.fst.2 := by
  rw [D.singleCrossTriangularAlgHom_apply]
  simp [CoordinateData.coordinateCharacter_liftedCoordinate_ne D hij.symm,
    CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson
      D i hdata.a_mem_jacobson]

/-- A nonzero cross-radical generator makes the triangular coordinate map
bijective. -/
theorem singleCrossTriangularAlgHom_bijective
    {i j : Fin 2} (hij : i ≠ j) (a : B) (ha : a ≠ 0)
    (hL : D.liftedCoordinate i * a = a)
    (hR : a * D.liftedCoordinate j = a)
    (hdata : SingleCrossRadicalData (K := K) a) :
    Function.Bijective
      (D.singleCrossTriangularAlgHom hij a hL hR hdata) := by
  constructor
  · intro x y hxy
    have hj : x.fst.1 = y.fst.1 := by
      have h := congrArg (CoordinateData.coordinateCharacter D j) hxy
      simpa only [D.coordinateCharacter_singleCrossTriangularAlgHom_right]
        using h
    have hi : x.fst.2 = y.fst.2 := by
      have h := congrArg (CoordinateData.coordinateCharacter D i) hxy
      simpa only [D.coordinateCharacter_singleCrossTriangularAlgHom_left]
        using h
    have hbase : x.fst = y.fst := Prod.ext hj hi
    have harr : x.snd.value • a = y.snd.value • a := by
      have h := hxy
      rw [D.singleCrossTriangularAlgHom_apply,
        D.singleCrossTriangularAlgHom_apply, hbase] at h
      exact add_left_cancel h
    have hsnd : x.snd = y.snd := by
      apply OpConjecture.A2Triangular.Arrow.ext
      exact smul_left_injective K ha harr
    exact TrivSqZeroExt.ext hbase hsnd
  · intro b
    let ci := CoordinateData.coordinateCharacter D i b
    let cj := CoordinateData.coordinateCharacter D j b
    let z := b - ∑ k : Fin 2,
      CoordinateData.coordinateCharacter D k b • D.liftedCoordinate k
    have hzJ : z ∈ Ring.jacobson B := D.diagonalRemainder_mem_jacobson b
    have hzSpan : z ∈ Submodule.span K {a} := by
      rw [← hdata.radical_eq_span]
      exact hzJ
    rw [Submodule.mem_span_singleton] at hzSpan
    obtain ⟨c, hc⟩ := hzSpan
    refine ⟨(((cj, ci), ⟨c⟩) : OpConjecture.A2Triangular.Model K), ?_⟩
    rw [D.singleCrossTriangularAlgHom_apply]
    change (cj • D.liftedCoordinate j + ci • D.liftedCoordinate i) +
      c • a = b
    have hsum :
        (∑ k : Fin 2,
          CoordinateData.coordinateCharacter D k b • D.liftedCoordinate k) =
          cj • D.liftedCoordinate j + ci • D.liftedCoordinate i := by
      simpa [ci, cj] using sum_eq_add_of_ne hij
        (fun k : Fin 2 ↦
          CoordinateData.coordinateCharacter D k b • D.liftedCoordinate k)
    rw [hc]
    dsimp [z]
    rw [hsum]
    abel

/-- A split two-coordinate algebra whose radical is generated by one
nonzero cross element is isomorphic to the three-dimensional triangular
algebra. -/
noncomputable def singleCrossTriangularAlgEquiv
    {i j : Fin 2} (hij : i ≠ j) (a : B) (ha : a ≠ 0)
    (hL : D.liftedCoordinate i * a = a)
    (hR : a * D.liftedCoordinate j = a)
    (hdata : SingleCrossRadicalData (K := K) a) :
    OpConjecture.A2Triangular.Model K ≃ₐ[K] B :=
  AlgEquiv.ofBijective
    (D.singleCrossTriangularAlgHom hij a hL hR hdata)
    (D.singleCrossTriangularAlgHom_bijective hij a ha hL hR hdata)

end OpConjecture.QuotientSurvival.TwoCoordinateData
