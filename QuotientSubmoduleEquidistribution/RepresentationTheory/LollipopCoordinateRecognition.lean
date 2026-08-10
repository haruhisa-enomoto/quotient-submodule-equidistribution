import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0AlgebraModel
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1AlgebraModel
import QuotientSubmoduleEquidistribution.RepresentationTheory.SingleCrossTriangularEquivalence
import QuotientSubmoduleEquidistribution.RepresentationTheory.PeirceCotangentSpanning

/-!
# Coordinate recognition of the two one-way lollipop algebras

This file proves the presentation-free carrier-recognition step in the
exceptional two-simple branch.  A split two-coordinate algebra whose radical
cotangent space is represented by a loop `x` and a cross arrow `a`, with
`x² = 0`, has radical span `{x, a, a*x}`.  It is then explicitly isomorphic
to the dead-path model when `a*x = 0`, and to the live-path model when
`a*x ≠ 0`.

The proof uses Peirce coordinates, cotangent detectors, and Artinian radical
nilpotence.  It does not use a bound-quiver presentation or a classification
of modules.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData

open QuotientSubmoduleEquidistribution.CotangentExtBridge

universe u

variable {K B : Type u}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]
  (D : QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData
    (K := K) (B := B))

private abbrev J (B : Type u) [Ring B] := Ring.jacobson B

theorem mul_eq_coordinate_smul_of_rightSupport_of_kills_jacobson
    {z : B}
    (hzR : z * D.liftedCoordinate 0 = z)
    (hkill : ∀ w : B, w ∈ J B → z * w = 0)
    (r : B) :
    z * r = CoordinateData.coordinateCharacter D 0 r • z := by
  let e0 := D.liftedCoordinate 0
  let e1 := D.liftedCoordinate 1
  have hsum : e0 + e1 = 1 := by
    simpa [e0, e1, Fin.sum_univ_two] using
      D.liftedCoordinate_complete.complete
  have hzOther : z * e1 = 0 := by
    calc
      z * e1 = (z * e0) * e1 := by rw [hzR]
      _ = z * (e0 * e1) := by rw [mul_assoc]
      _ = 0 := by
        rw [D.liftedCoordinate_complete.ortho
          (by decide : (0 : Fin 2) ≠ 1)]
        simp
  have hcoord (k : Fin 2) :
      z * (r * D.liftedCoordinate k) =
        CoordinateData.coordinateCharacter D k r •
          (z * D.liftedCoordinate k) := by
    let c := CoordinateData.coordinateCharacter D k r
    have hzero :
        z * (r * D.liftedCoordinate k -
          algebraMap K B c * D.liftedCoordinate k) = 0 :=
      hkill _
        (CoordinateData.mul_liftedCoordinate_sub_coordinate_mem_jacobson
          D k r)
    have heq :
        z * (r * D.liftedCoordinate k) =
          z * (algebraMap K B c * D.liftedCoordinate k) := by
      rw [mul_sub, sub_eq_zero] at hzero
      exact hzero
    calc
      z * (r * D.liftedCoordinate k) =
          z * (algebraMap K B c * D.liftedCoordinate k) := heq
      _ = (z * algebraMap K B c) * D.liftedCoordinate k := by
        rw [mul_assoc]
      _ = (algebraMap K B c * z) * D.liftedCoordinate k := by
        rw [← Algebra.commutes c z]
      _ = algebraMap K B c * (z * D.liftedCoordinate k) := by
        rw [mul_assoc]
      _ = c • (z * D.liftedCoordinate k) := by
        rw [Algebra.smul_def]
      _ = CoordinateData.coordinateCharacter D k r •
          (z * D.liftedCoordinate k) := rfl
  calc
    z * r = z * (r * (e0 + e1)) := by rw [hsum, mul_one]
    _ = z * (r * e0) + z * (r * e1) := by noncomm_ring
    _ = CoordinateData.coordinateCharacter D 0 r • (z * e0) +
        CoordinateData.coordinateCharacter D 1 r • (z * e1) := by
      rw [hcoord 0, hcoord 1]
    _ = CoordinateData.coordinateCharacter D 0 r • z := by
      rw [hzR, hzOther, smul_zero, add_zero]

/-- Structural hypotheses for a one-loop, one-cross-arrow coordinate
algebra after the loop-square argument. -/
structure LollipopRadicalData
    (D : QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData
      (K := K) (B := B))
    (x a : B) : Prop where
  x_mem_jacobson : x ∈ J B
  a_mem_jacobson : a ∈ J B
  x_left : D.liftedCoordinate 0 * x = x
  x_right : x * D.liftedCoordinate 0 = x
  a_left : D.liftedCoordinate 1 * a = a
  a_right : a * D.liftedCoordinate 0 = a
  x_not_square : x ∉ (J B) ^ 2
  a_not_square : a ∉ (J B) ^ 2
  x_sq : x * x = 0
  cotangent_spanned :
    QuotientSubmoduleEquidistribution.QuotientSurvival.JacobsonCotangentSpannedBy
      (K := K) x a 0

namespace LollipopRadicalData

variable
  {D : QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData
    (K := K) (B := B)}
  {x a : B}
  (L : QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData.LollipopRadicalData
    D x a)

include L in
theorem x_mul_a : x * a = 0 := by
  calc
    x * a = (x * D.liftedCoordinate 0) *
        (D.liftedCoordinate 1 * a) := by rw [L.x_right, L.a_left]
    _ = x * (D.liftedCoordinate 0 * D.liftedCoordinate 1) * a := by
      noncomm_ring
    _ = 0 := by
      rw [D.liftedCoordinate_complete.ortho
        (by decide : (0 : Fin 2) ≠ 1)]
      simp

include L in
theorem a_mul_a : a * a = 0 := by
  calc
    a * a = (a * D.liftedCoordinate 0) *
        (D.liftedCoordinate 1 * a) := by rw [L.a_right, L.a_left]
    _ = a * (D.liftedCoordinate 0 * D.liftedCoordinate 1) * a := by
      noncomm_ring
    _ = 0 := by
      rw [D.liftedCoordinate_complete.ortho
        (by decide : (0 : Fin 2) ≠ 1)]
      simp

include L in
theorem other_left_mul_x : D.liftedCoordinate 1 * x = 0 := by
  calc
    D.liftedCoordinate 1 * x =
        D.liftedCoordinate 1 * (D.liftedCoordinate 0 * x) := by rw [L.x_left]
    _ = (D.liftedCoordinate 1 * D.liftedCoordinate 0) * x := by rw [mul_assoc]
    _ = 0 := by
      rw [D.liftedCoordinate_complete.ortho
        (by decide : (1 : Fin 2) ≠ 0)]
      simp

include L in
theorem x_mul_other_right : x * D.liftedCoordinate 1 = 0 := by
  calc
    x * D.liftedCoordinate 1 =
        (x * D.liftedCoordinate 0) * D.liftedCoordinate 1 := by rw [L.x_right]
    _ = x * (D.liftedCoordinate 0 * D.liftedCoordinate 1) := by rw [mul_assoc]
    _ = 0 := by
      rw [D.liftedCoordinate_complete.ortho
        (by decide : (0 : Fin 2) ≠ 1)]
      simp

include L in
theorem other_left_mul_a : D.liftedCoordinate 0 * a = 0 := by
  calc
    D.liftedCoordinate 0 * a =
        D.liftedCoordinate 0 * (D.liftedCoordinate 1 * a) := by rw [L.a_left]
    _ = (D.liftedCoordinate 0 * D.liftedCoordinate 1) * a := by rw [mul_assoc]
    _ = 0 := by
      rw [D.liftedCoordinate_complete.ortho
        (by decide : (0 : Fin 2) ≠ 1)]
      simp

include L in
theorem a_mul_other_right : a * D.liftedCoordinate 1 = 0 := by
  calc
    a * D.liftedCoordinate 1 =
        (a * D.liftedCoordinate 0) * D.liftedCoordinate 1 := by rw [L.a_right]
    _ = a * (D.liftedCoordinate 0 * D.liftedCoordinate 1) := by rw [mul_assoc]
    _ = 0 := by
      rw [D.liftedCoordinate_complete.ortho
        (by decide : (0 : Fin 2) ≠ 1)]
      simp

include L in
theorem ax_mem_jacobson_square : a * x ∈ (J B) ^ 2 := by
  have h : a * x ∈ (J B) * (J B) :=
    Ideal.mul_mem_mul L.a_mem_jacobson L.x_mem_jacobson
  rw [Ideal.IsTwoSided.pow_succ]
  simpa [Submodule.pow_one] using h

include L in
theorem ax_left : D.liftedCoordinate 1 * (a * x) = a * x := by
  rw [← mul_assoc, L.a_left]

include L in
theorem ax_right : (a * x) * D.liftedCoordinate 0 = a * x := by
  rw [mul_assoc, L.x_right]

include L in
theorem other_left_mul_ax : D.liftedCoordinate 0 * (a * x) = 0 := by
  rw [← mul_assoc, L.other_left_mul_a, zero_mul]

include L in
theorem ax_mul_other_right : (a * x) * D.liftedCoordinate 1 = 0 := by
  rw [mul_assoc, L.x_mul_other_right, mul_zero]

include L in
theorem ax_mul_x : (a * x) * x = 0 := by
  rw [mul_assoc, L.x_sq, mul_zero]

include L in
theorem a_mul_ax : a * (a * x) = 0 := by
  rw [← mul_assoc, L.a_mul_a, zero_mul]

include L in
theorem ax_mul_a : (a * x) * a = 0 := by
  rw [mul_assoc, L.x_mul_a, mul_zero]

include L in
theorem ax_mul_ax : (a * x) * (a * x) = 0 := by
  calc
    (a * x) * (a * x) = a * ((x * a) * x) := by noncomm_ring
    _ = 0 := by rw [L.x_mul_a]; simp

include L in
theorem x_kills_jacobson (w : B) (hw : w ∈ J B) : x * w = 0 := by
  obtain ⟨rx, ra, rb, rfl⟩ :=
    (jacobsonRightGeneratedBy_of_cotangentSpanned L.cotangent_spanned) w hw
  calc
    x * (x * rx + a * ra + 0 * rb) =
        (x * x) * rx + (x * a) * ra := by noncomm_ring
    _ = 0 := by rw [L.x_sq, L.x_mul_a]; simp

include L in
theorem ax_kills_jacobson (w : B) (hw : w ∈ J B) :
    (a * x) * w = 0 := by
  rw [mul_assoc, L.x_kills_jacobson w hw, mul_zero]

include L in
theorem x_mul_eq_scalar (r : B) :
    x * r = CoordinateData.coordinateCharacter D 0 r • x :=
  mul_eq_coordinate_smul_of_rightSupport_of_kills_jacobson D
    L.x_right L.x_kills_jacobson r

include L in
theorem ax_mul_eq_scalar (r : B) :
    (a * x) * r =
      CoordinateData.coordinateCharacter D 0 r • (a * x) := by
  apply mul_eq_coordinate_smul_of_rightSupport_of_kills_jacobson D
  · rw [mul_assoc, L.x_right]
  · exact L.ax_kills_jacobson

include L in
/-- The radical is spanned by the loop, the cross arrow, and their only
potentially nonzero length-two path. -/
theorem radical_eq_span_three :
    ((J B : Submodule B B).restrictScalars K) =
      Submodule.span K {x, a, a * x} := by
  let S : Submodule K B := Submodule.span K {x, a, a * x}
  have hxS : x ∈ S := Submodule.subset_span (by simp)
  have haS : a ∈ S := Submodule.subset_span (by simp)
  have haxS : a * x ∈ S := Submodule.subset_span (by simp)
  have hmulX (r : B) : x * r ∈ S := by
    rw [L.x_mul_eq_scalar r]
    exact S.smul_mem _ hxS
  have hmulAX (r : B) : (a * x) * r ∈ S := by
    rw [L.ax_mul_eq_scalar r]
    exact S.smul_mem _ haxS
  have hmulA (r : B) : a * r ∈ S := by
    let diag : B := ∑ k : Fin 2,
      CoordinateData.coordinateCharacter D k r • D.liftedCoordinate k
    let rem : B := r - diag
    have hremJ : rem ∈ J B := by
      simpa [rem, diag] using D.diagonalRemainder_mem_jacobson r
    obtain ⟨rx, ra, rb, hrem⟩ :=
      (jacobsonRightGeneratedBy_of_cotangentSpanned L.cotangent_spanned)
        rem hremJ
    have haOther : a * D.liftedCoordinate 1 = 0 := by
      calc
        a * D.liftedCoordinate 1 =
            (a * D.liftedCoordinate 0) * D.liftedCoordinate 1 := by
          rw [L.a_right]
        _ = a * (D.liftedCoordinate 0 * D.liftedCoordinate 1) := by
          rw [mul_assoc]
        _ = 0 := by
          rw [D.liftedCoordinate_complete.ortho
            (by decide : (0 : Fin 2) ≠ 1)]
          simp
    have hdiag : a * diag =
        CoordinateData.coordinateCharacter D 0 r • a := by
      simp [diag, Fin.sum_univ_two, mul_add,
        L.a_right, haOther]
    have hremS : a * rem ∈ S := by
      rw [hrem]
      have heq :
        a * (x * rx + a * ra + 0 * rb) =
            (a * x) * rx + (a * a) * ra := by noncomm_ring
      rw [heq, L.a_mul_a]
      simpa using hmulAX rx
    have hr : r = diag + rem := by
      dsimp [rem]
      abel
    rw [hr, mul_add, hdiag]
    exact S.add_mem (S.smul_mem _ haS) hremS
  apply le_antisymm
  · intro z hz
    obtain ⟨rx, ra, rb, hzEq⟩ :=
      (jacobsonRightGeneratedBy_of_cotangentSpanned L.cotangent_spanned)
        z hz
    rw [hzEq]
    exact S.add_mem (S.add_mem (hmulX rx) (hmulA ra)) (by simp)
  · rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact L.x_mem_jacobson
    · exact L.a_mem_jacobson
    · exact (J B).mul_mem_left a L.x_mem_jacobson

end LollipopRadicalData

namespace LollipopRadicalData

open QuotientSubmoduleEquidistribution.LollipopConcrete

variable
  {D : QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData
    (K := K) (B := B)}
  {x a : B}
  (L : QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData.LollipopRadicalData
    D x a)

/-- Send the two radical coordinates of the dead-path model to the loop and
cross-arrow representatives. -/
def b0RadicalLinearMap (x a : B) : B0Radical K →ₗ[K] B where
  toFun m := m.x • x + m.a • a
  map_add' m n := by
    simp only [B0Radical.add_x, B0Radical.add_a, add_smul]
    abel
  map_smul' c m := by
    simp only [B0Radical.smul_x, B0Radical.smul_a]
    simp only [smul_add, smul_smul, RingHom.id_apply]

omit [IsArtinianRing B] in
@[simp]
theorem b0RadicalLinearMap_apply (m : B0Radical K) :
    b0RadicalLinearMap x a m = m.x • x + m.a • a := rfl

include L in
/-- The coordinate map from the dead-path lollipop model. -/
def b0AlgHom (hdead : a * x = 0) : B0Model K →ₐ[K] B := by
  refine TrivSqZeroExt.lift
    (D.diagonalAlgHom (by decide : (1 : Fin 2) ≠ 0))
    (b0RadicalLinearMap x a) ?_ ?_ ?_
  · intro m n
    rw [b0RadicalLinearMap_apply, b0RadicalLinearMap_apply]
    simp only [add_mul, mul_add, smul_mul_smul_comm]
    rw [L.x_sq, L.x_mul_a, hdead, L.a_mul_a]
    simp
  · intro r m
    apply add_left_cancel
    change
      0 + ((r.1 * m.x) • x + (r.2 * m.a) • a) =
        0 + (r.1 • D.liftedCoordinate 0 +
          r.2 • D.liftedCoordinate 1) * (m.x • x + m.a • a)
    simp only [add_mul, mul_add, smul_mul_smul_comm]
    rw [L.x_left, L.other_left_mul_a, L.other_left_mul_x, L.a_left]
    simp
  · intro r m
    apply add_left_cancel
    change
      0 + ((r.1 * m.x) • x + (r.1 * m.a) • a) =
        0 + (m.x • x + m.a • a) *
          (r.1 • D.liftedCoordinate 0 +
            r.2 • D.liftedCoordinate 1)
    simp only [mul_add, add_mul, smul_mul_smul_comm]
    rw [L.x_right, L.x_mul_other_right, L.a_right, L.a_mul_other_right]
    simp [mul_comm]

@[simp]
theorem b0AlgHom_apply (hdead : a * x = 0) (m : B0Model K) :
    L.b0AlgHom hdead m =
      (m.fst.1 • D.liftedCoordinate 0 +
        m.fst.2 • D.liftedCoordinate 1) +
      (m.snd.x • x + m.snd.a • a) := by
  rw [b0AlgHom, TrivSqZeroExt.lift_def]
  rfl

include L in
theorem b0AlgHom_bijective (hdead : a * x = 0) :
    Function.Bijective (L.b0AlgHom hdead) := by
  constructor
  · intro m n hmn
    have h0 : m.fst.1 = n.fst.1 := by
      have h := congrArg (CoordinateData.coordinateCharacter D 0) hmn
      simpa [L.b0AlgHom_apply,
        CoordinateData.coordinateCharacter_liftedCoordinate_ne D
          (by decide : (0 : Fin 2) ≠ 1),
        CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D 0
          L.x_mem_jacobson,
        CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D 0
          L.a_mem_jacobson] using h
    have h1 : m.fst.2 = n.fst.2 := by
      have h := congrArg (CoordinateData.coordinateCharacter D 1) hmn
      simpa [L.b0AlgHom_apply,
        CoordinateData.coordinateCharacter_liftedCoordinate_ne D
          (by decide : (1 : Fin 2) ≠ 0),
        CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D 1
          L.x_mem_jacobson,
        CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D 1
          L.a_mem_jacobson] using h
    have hx : m.snd.x = n.snd.x := by
      let f := D.normalizedPeirceCotangentFunctional 0 0 L.x_not_square
      have h := congrArg f hmn
      simpa [f, L.b0AlgHom_apply,
        D.normalizedPeirceCotangentFunctional_liftedCoordinate,
        D.normalizedPeirceCotangentFunctional_self 0 0
          L.x_mem_jacobson L.x_left L.x_right L.x_not_square,
        D.normalizedPeirceCotangentFunctional_eq_zero_of_corner_ne
          0 0 1 0 L.a_left L.a_right L.x_not_square (Or.inl (by decide))]
        using h
    have ha : m.snd.a = n.snd.a := by
      let f := D.normalizedPeirceCotangentFunctional 1 0 L.a_not_square
      have h := congrArg f hmn
      simpa [f, L.b0AlgHom_apply,
        D.normalizedPeirceCotangentFunctional_liftedCoordinate,
        D.normalizedPeirceCotangentFunctional_self 1 0
          L.a_mem_jacobson L.a_left L.a_right L.a_not_square,
        D.normalizedPeirceCotangentFunctional_eq_zero_of_corner_ne
          1 0 0 0 L.x_left L.x_right L.a_not_square (Or.inl (by decide))]
        using h
    apply TrivSqZeroExt.ext
    · exact Prod.ext h0 h1
    · exact B0Radical.ext K hx ha
  · intro b
    let c0 := CoordinateData.coordinateCharacter D 0 b
    let c1 := CoordinateData.coordinateCharacter D 1 b
    let z := b - ∑ k : Fin 2,
      CoordinateData.coordinateCharacter D k b • D.liftedCoordinate k
    have hzJ : z ∈ J B := D.diagonalRemainder_mem_jacobson b
    have hzSpan : z ∈ Submodule.span K {x, a} := by
      have hzTriple : z ∈ Submodule.span K {x, a, a * x} := by
        rw [← L.radical_eq_span_three]
        exact hzJ
      obtain ⟨cx, ca, cu, h⟩ := Submodule.mem_span_triple.mp hzTriple
      rw [hdead, smul_zero, add_zero] at h
      exact Submodule.mem_span_pair.mpr ⟨cx, ca, h⟩
    obtain ⟨cx, ca, hzca⟩ := Submodule.mem_span_pair.mp hzSpan
    refine ⟨(((c0, c1), ⟨cx, ca⟩) : B0Model K), ?_⟩
    rw [L.b0AlgHom_apply]
    change (c0 • D.liftedCoordinate 0 + c1 • D.liftedCoordinate 1) +
      (cx • x + ca • a) = b
    have hsum :
        (∑ k : Fin 2,
          CoordinateData.coordinateCharacter D k b • D.liftedCoordinate k) =
          c0 • D.liftedCoordinate 0 + c1 • D.liftedCoordinate 1 := by
      simp [c0, c1, Fin.sum_univ_two]
    rw [hzca]
    dsimp [z]
    rw [hsum]
    abel

/-- In the dead-path case the abstract coordinate algebra is the concrete
four-dimensional lollipop model. -/
noncomputable def b0AlgEquiv (hdead : a * x = 0) :
    B0Model K ≃ₐ[K] B :=
  AlgEquiv.ofBijective (L.b0AlgHom hdead) (L.b0AlgHom_bijective hdead)

include L in
/-- The dual-number vertex corner and the second scalar vertex, represented
inside the abstract live-path algebra. -/
def b1BaseAlgHom :
    QuotientSubmoduleEquidistribution.LollipopConcrete.B1.BaseAlgebra K →ₐ[K] B where
  toFun r :=
    r.1.fst • D.liftedCoordinate 0 + r.1.snd • x +
      r.2 • D.liftedCoordinate 1
  map_one' := by
    change
      (1 : K) • D.liftedCoordinate 0 + (0 : K) • x +
          (1 : K) • D.liftedCoordinate 1 = 1
    simpa [Fin.sum_univ_two] using D.liftedCoordinate_complete.complete
  map_mul' r s := by
    change
      (r.1.fst * s.1.fst) • D.liftedCoordinate 0 +
          (r.1.fst * s.1.snd + r.1.snd * s.1.fst) • x +
          (r.2 * s.2) • D.liftedCoordinate 1 =
        (r.1.fst • D.liftedCoordinate 0 + r.1.snd • x +
            r.2 • D.liftedCoordinate 1) *
          (s.1.fst • D.liftedCoordinate 0 + s.1.snd • x +
            s.2 • D.liftedCoordinate 1)
    simp only [add_mul, mul_add, smul_mul_smul_comm]
    rw [D.liftedCoordinate_complete.idem,
      L.x_left, L.other_left_mul_x,
      L.x_right, L.x_sq, L.x_mul_other_right,
      D.liftedCoordinate_complete.ortho (by decide : (1 : Fin 2) ≠ 0),
      D.liftedCoordinate_complete.ortho (by decide : (0 : Fin 2) ≠ 1),
      D.liftedCoordinate_complete.idem]
    module
  map_zero' := by simp
  map_add' r s := by
    change
      (r.1.fst + s.1.fst) • D.liftedCoordinate 0 +
          (r.1.snd + s.1.snd) • x +
          (r.2 + s.2) • D.liftedCoordinate 1 =
        (r.1.fst • D.liftedCoordinate 0 + r.1.snd • x +
            r.2 • D.liftedCoordinate 1) +
          (s.1.fst • D.liftedCoordinate 0 + s.1.snd • x +
            s.2 • D.liftedCoordinate 1)
    module
  commutes' c := by
    change
      c • D.liftedCoordinate 0 + (0 : K) • x +
          c • D.liftedCoordinate 1 = algebraMap K B c
    rw [zero_smul, add_zero, ← smul_add]
    have hsum : D.liftedCoordinate 0 + D.liftedCoordinate 1 = 1 := by
      simpa [Fin.sum_univ_two] using D.liftedCoordinate_complete.complete
    rw [hsum]
    simp [Algebra.smul_def]

@[simp]
theorem b1BaseAlgHom_apply
    (r : QuotientSubmoduleEquidistribution.LollipopConcrete.B1.BaseAlgebra K) :
    L.b1BaseAlgHom r =
      r.1.fst • D.liftedCoordinate 0 + r.1.snd • x +
        r.2 • D.liftedCoordinate 1 := rfl

/-- The live arrow corner maps its two coordinates to `a` and `a*x`. -/
def b1ArrowLinearMap (a x : B) :
    QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ArrowCorner K →ₗ[K] B where
  toFun m := m.fst • a + m.snd • (a * x)
  map_add' m n := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, add_smul]
    abel
  map_smul' c m := by
    simp only [TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul,
      smul_eq_mul, smul_add, smul_smul, RingHom.id_apply]

omit [IsArtinianRing B] in
@[simp]
theorem b1ArrowLinearMap_apply
    (m : QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ArrowCorner K) :
    b1ArrowLinearMap a x m = m.fst • a + m.snd • (a * x) := rfl

include L in
/-- The coordinate algebra map from the live-path model. -/
def b1AlgHom : QuotientSubmoduleEquidistribution.LollipopConcrete.B1.B1Model K →ₐ[K] B := by
  refine TrivSqZeroExt.lift L.b1BaseAlgHom
    (b1ArrowLinearMap a x) ?_ ?_ ?_
  · intro m n
    rw [b1ArrowLinearMap_apply, b1ArrowLinearMap_apply]
    simp only [add_mul, mul_add, smul_mul_smul_comm]
    rw [L.a_mul_a, L.a_mul_ax, L.ax_mul_a, L.ax_mul_ax]
    simp
  · intro r m
    have hxa : x * (a * x) = 0 := by
      rw [← mul_assoc, L.x_mul_a, zero_mul]
    change
      (r.2 * m.fst) • a + (r.2 * m.snd) • (a * x) =
        (r.1.fst • D.liftedCoordinate 0 + r.1.snd • x +
            r.2 • D.liftedCoordinate 1) *
          (m.fst • a + m.snd • (a * x))
    simp only [add_mul, mul_add, smul_mul_smul_comm]
    rw [L.other_left_mul_a, L.other_left_mul_ax,
      L.x_mul_a, hxa,
      L.a_left, L.ax_left]
    simp
  · intro r m
    change
      (r.1.fst * m.fst) • a +
          (r.1.fst * m.snd + r.1.snd * m.fst) • (a * x) =
        (m.fst • a + m.snd • (a * x)) *
          (r.1.fst • D.liftedCoordinate 0 + r.1.snd • x +
            r.2 • D.liftedCoordinate 1)
    simp only [mul_add, add_mul, smul_mul_smul_comm]
    rw [L.a_right, L.ax_right, L.ax_mul_x,
      L.a_mul_other_right, L.ax_mul_other_right]
    module

@[simp]
theorem b1AlgHom_apply
    (m : QuotientSubmoduleEquidistribution.LollipopConcrete.B1.B1Model K) :
    L.b1AlgHom m =
      (m.fst.1.fst • D.liftedCoordinate 0 + m.fst.1.snd • x +
        m.fst.2 • D.liftedCoordinate 1) +
      (m.snd.fst • a + m.snd.snd • (a * x)) := by
  rw [b1AlgHom, TrivSqZeroExt.lift_def]
  rfl

include L in
/-- A nonzero live path makes the five coordinate classes independent and
the live-model coordinate map bijective. -/
theorem b1AlgHom_bijective (hlive : a * x ≠ 0) :
    Function.Bijective L.b1AlgHom := by
  have haxJ : a * x ∈ J B :=
    Ideal.pow_le_self two_ne_zero L.ax_mem_jacobson_square
  constructor
  · intro m n hmn
    have h0 : m.fst.1.fst = n.fst.1.fst := by
      have h := congrArg (CoordinateData.coordinateCharacter D 0) hmn
      simpa [L.b1AlgHom_apply,
        CoordinateData.coordinateCharacter_liftedCoordinate_ne D
          (by decide : (0 : Fin 2) ≠ 1),
        CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D 0
          L.x_mem_jacobson,
        CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D 0
          L.a_mem_jacobson,
        CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D 0 haxJ]
        using h
    have h1 : m.fst.2 = n.fst.2 := by
      have h := congrArg (CoordinateData.coordinateCharacter D 1) hmn
      simpa [L.b1AlgHom_apply,
        CoordinateData.coordinateCharacter_liftedCoordinate_ne D
          (by decide : (1 : Fin 2) ≠ 0),
        CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D 1
          L.x_mem_jacobson,
        CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D 1
          L.a_mem_jacobson,
        CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D 1 haxJ]
        using h
    have hx : m.fst.1.snd = n.fst.1.snd := by
      let f := D.normalizedPeirceCotangentFunctional 0 0 L.x_not_square
      have h := congrArg f hmn
      simpa [f, L.b1AlgHom_apply,
        D.normalizedPeirceCotangentFunctional_liftedCoordinate,
        D.normalizedPeirceCotangentFunctional_self 0 0
          L.x_mem_jacobson L.x_left L.x_right L.x_not_square,
        D.normalizedPeirceCotangentFunctional_eq_zero_of_corner_ne
          0 0 1 0 L.a_left L.a_right L.x_not_square (Or.inl (by decide)),
        D.normalizedPeirceCotangentFunctional_vanishes_square
          0 0 L.x_not_square (a * x) L.ax_mem_jacobson_square]
        using h
    have ha : m.snd.fst = n.snd.fst := by
      let f := D.normalizedPeirceCotangentFunctional 1 0 L.a_not_square
      have h := congrArg f hmn
      simpa [f, L.b1AlgHom_apply,
        D.normalizedPeirceCotangentFunctional_liftedCoordinate,
        D.normalizedPeirceCotangentFunctional_self 1 0
          L.a_mem_jacobson L.a_left L.a_right L.a_not_square,
        D.normalizedPeirceCotangentFunctional_eq_zero_of_corner_ne
          1 0 0 0 L.x_left L.x_right L.a_not_square (Or.inl (by decide)),
        D.normalizedPeirceCotangentFunctional_vanishes_square
          1 0 L.a_not_square (a * x) L.ax_mem_jacobson_square]
        using h
    have haxSmul : m.snd.snd • (a * x) = n.snd.snd • (a * x) := by
      have h := hmn
      rw [L.b1AlgHom_apply, L.b1AlgHom_apply, h0, hx, h1, ha] at h
      exact add_left_cancel (add_left_cancel h)
    have hax : m.snd.snd = n.snd.snd :=
      smul_left_injective K hlive haxSmul
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · exact TrivSqZeroExt.ext h0 hx
      · exact h1
    · exact TrivSqZeroExt.ext ha hax
  · intro b
    let c0 := CoordinateData.coordinateCharacter D 0 b
    let c1 := CoordinateData.coordinateCharacter D 1 b
    let z := b - ∑ k : Fin 2,
      CoordinateData.coordinateCharacter D k b • D.liftedCoordinate k
    have hzJ : z ∈ J B := D.diagonalRemainder_mem_jacobson b
    have hzSpan : z ∈ Submodule.span K {x, a, a * x} := by
      rw [← L.radical_eq_span_three]
      exact hzJ
    obtain ⟨cx, ca, cu, hzEq⟩ := Submodule.mem_span_triple.mp hzSpan
    refine ⟨(((((c0, cx), c1), (ca, cu))) :
      QuotientSubmoduleEquidistribution.LollipopConcrete.B1.B1Model K), ?_⟩
    rw [L.b1AlgHom_apply]
    change
      (c0 • D.liftedCoordinate 0 + cx • x +
          c1 • D.liftedCoordinate 1) +
        (ca • a + cu • (a * x)) = b
    have hsum :
        (∑ k : Fin 2,
          CoordinateData.coordinateCharacter D k b • D.liftedCoordinate k) =
          c0 • D.liftedCoordinate 0 + c1 • D.liftedCoordinate 1 := by
      simp [c0, c1, Fin.sum_univ_two]
    calc
      (c0 • D.liftedCoordinate 0 + cx • x +
            c1 • D.liftedCoordinate 1) +
          (ca • a + cu • (a * x)) =
          (c0 • D.liftedCoordinate 0 +
              c1 • D.liftedCoordinate 1) +
            (cx • x + ca • a + cu • (a * x)) := by abel
      _ = (∑ k : Fin 2,
            CoordinateData.coordinateCharacter D k b •
              D.liftedCoordinate k) + z := by rw [hsum, hzEq]
      _ = b := by
        dsimp [z]
        abel

/-- In the live-path case the abstract coordinate algebra is the concrete
five-dimensional lollipop model. -/
noncomputable def b1AlgEquiv (hlive : a * x ≠ 0) :
    QuotientSubmoduleEquidistribution.LollipopConcrete.B1.B1Model K ≃ₐ[K] B :=
  AlgEquiv.ofBijective L.b1AlgHom (L.b1AlgHom_bijective hlive)

end LollipopRadicalData

end QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData
