import OpConjecture.RepresentationTheory.PeirceCotangentSpanning

/-!
# Radical normal form from one cross cotangent class

This file isolates the general ring-theoretic step needed by the
two-simple, cardinality-three recognition argument.  A single cross Peirce
class spanning the Jacobson cotangent space forces the radical itself to be
one-dimensional and square-zero.  No quiver presentation or module
classification is used.
-/

noncomputable section

namespace OpConjecture.QuotientSurvival

universe u

variable {K B : Type u}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]

namespace TwoCoordinateData

variable (D : TwoCoordinateData (K := K) (B := B))

private abbrev J (B : Type u) [Ring B] := Ring.jacobson B

/-- The exact structural consequences of a single cross-corner generator of
the Jacobson cotangent space. -/
structure SingleCrossRadicalData (a : B) : Prop where
  a_mem_jacobson : a ∈ J B
  a_sq : a * a = 0
  radical_eq_span :
    ((J B : Submodule B B).restrictScalars K) =
      Submodule.span K {a}
  jacobson_sq_eq_bot : (J B) ^ 2 = ⊥

omit [IsArtinianRing B] in
/-- A nonzero radical class spans `J/J²` when that cotangent space has
dimension at most one. -/
theorem jacobsonCotangentSpannedBy_single_of_finrank_le_one
    [FiniteDimensional K B]
    {a : B}
    (haJ : a ∈ J B)
    (ha2 : a ∉ (J B) ^ 2)
    (hdim : Module.finrank K
      (jacobsonCotangentSubmodule (K := K) (B := B)) ≤ 1) :
    JacobsonCotangentSpannedBy (K := K) (0 : B) a 0 := by
  let J2K := jacobsonSquareSubmodule (K := K) (B := B)
  let Q := B ⧸ J2K
  let v : Q := J2K.mkQ a
  let C : Submodule K Q :=
    jacobsonCotangentSubmodule (K := K) (B := B)
  let S : Submodule K Q := Submodule.span K {v}
  have hv0 : v ≠ 0 := by
    intro hv
    have haJ2K : a ∈ J2K := by
      rw [← Submodule.Quotient.mk_eq_zero]
      exact hv
    apply ha2
    simpa [J2K, jacobsonSquareSubmodule] using haJ2K
  have hSC : S ≤ C := by
    apply Submodule.span_le.mpr
    rw [Set.singleton_subset_iff]
    apply Submodule.mem_map.mpr
    exact ⟨a, by simpa [C] using haJ, rfl⟩
  have hSdim : Module.finrank K S = 1 := by
    simpa [S] using finrank_span_singleton hv0
  have hSCeq : S = C := by
    apply Submodule.eq_of_le_of_finrank_le hSC
    rw [hSdim]
    simpa [C] using hdim
  intro z hz
  have hzC : J2K.mkQ z ∈ C := by
    apply Submodule.mem_map.mpr
    exact ⟨z, by simpa [C] using hz, rfl⟩
  have hzS : J2K.mkQ z ∈ S := by
    rw [hSCeq]
    exact hzC
  rw [Submodule.mem_span_singleton] at hzS
  obtain ⟨c, hc⟩ := hzS
  refine ⟨0, c, 0, ?_⟩
  have hmk : J2K.mkQ z = J2K.mkQ (c • a) := by
    simpa [v] using hc.symm
  have hmemK : z - c • a ∈ J2K :=
    (Submodule.Quotient.eq J2K).mp hmk
  simpa [J2K, jacobsonSquareSubmodule] using hmemK

private theorem singleCross_a_mem_jacobson
    {a : B}
    (hL : D.liftedCoordinate 1 * a = a)
    (hR : a * D.liftedCoordinate 0 = a) :
    a ∈ J B := by
  have h := D.offDiagonal_mem_jacobson
    (by decide : (1 : Fin 2) ≠ 0) a
  rw [hL, hR] at h
  exact h

private theorem singleCross_a_sq
    {a : B}
    (hL : D.liftedCoordinate 1 * a = a)
    (hR : a * D.liftedCoordinate 0 = a) :
    a * a = 0 := by
  calc
    a * a =
        (a * D.liftedCoordinate 0) *
          (D.liftedCoordinate 1 * a) := by rw [hL, hR]
    _ = a *
        (D.liftedCoordinate 0 * D.liftedCoordinate 1) * a := by
      noncomm_ring
    _ = 0 := by
      rw [D.liftedCoordinate_complete.ortho
        (by decide : (0 : Fin 2) ≠ 1)]
      simp

private theorem singleCross_rightGenerated
    {a z : B}
    (hspan : JacobsonCotangentSpannedBy (K := K) (0 : B) a 0)
    (hz : z ∈ J B) :
    ∃ r : B, z = a * r := by
  obtain ⟨rx, ra, rb, hzEq⟩ :=
    (jacobsonRightGeneratedBy_of_cotangentSpanned hspan) z hz
  refine ⟨ra, ?_⟩
  simpa using hzEq

private theorem singleCross_a_mul_eq_zero_of_mem_jacobson
    {a z : B}
    (ha2 : a * a = 0)
    (hspan : JacobsonCotangentSpannedBy (K := K) (0 : B) a 0)
    (hz : z ∈ J B) :
    a * z = 0 := by
  obtain ⟨r, rfl⟩ := singleCross_rightGenerated hspan hz
  calc
    a * (a * r) = (a * a) * r := by rw [mul_assoc]
    _ = 0 := by rw [ha2, zero_mul]

private theorem singleCross_mul_coordinate_zero
    {a r : B}
    (ha2 : a * a = 0)
    (hspan : JacobsonCotangentSpannedBy (K := K) (0 : B) a 0)
    (j : Fin 2) :
    a *
        (r * D.liftedCoordinate j -
          algebraMap K B
            (OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter D j r) *
            D.liftedCoordinate j) = 0 := by
  apply singleCross_a_mul_eq_zero_of_mem_jacobson ha2 hspan
  exact
    OpConjecture.CotangentExtBridge.CoordinateData.mul_liftedCoordinate_sub_coordinate_mem_jacobson
      D j r

private theorem singleCross_scalar_reduce
    {a r : B}
    (hR : a * D.liftedCoordinate 0 = a)
    (ha2 : a * a = 0)
    (hspan : JacobsonCotangentSpannedBy (K := K) (0 : B) a 0) :
    a * r =
      OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter D 0 r • a := by
  let e0 := D.liftedCoordinate 0
  let e1 := D.liftedCoordinate 1
  let c0 :=
    OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter D 0 r
  let c1 :=
    OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter D 1 r
  have hsum : e0 + e1 = 1 := by
    simpa [e0, e1, Fin.sum_univ_two] using
      D.liftedCoordinate_complete.complete
  have hae1 : a * e1 = 0 := by
    calc
      a * e1 = (a * e0) * e1 := by rw [hR]
      _ = a * (e0 * e1) := by rw [mul_assoc]
      _ = 0 := by
        rw [D.liftedCoordinate_complete.ortho
          (by decide : (0 : Fin 2) ≠ 1)]
        simp
  have hkill0 :
      a * (r * e0 - algebraMap K B c0 * e0) = 0 := by
    simpa [e0, c0] using
      D.singleCross_mul_coordinate_zero ha2 hspan 0 (r := r)
  have hkill1 :
      a * (r * e1 - algebraMap K B c1 * e1) = 0 := by
    simpa [e1, c1] using
      D.singleCross_mul_coordinate_zero ha2 hspan 1 (r := r)
  have hr0 : a * (r * e0) = c0 • a := by
    have hEq :
        a * (r * e0) = a * (algebraMap K B c0 * e0) := by
      rw [mul_sub, sub_eq_zero] at hkill0
      exact hkill0
    calc
      a * (r * e0) = a * (algebraMap K B c0 * e0) := hEq
      _ = (a * algebraMap K B c0) * e0 := by rw [mul_assoc]
      _ = (algebraMap K B c0 * a) * e0 := by
        rw [← Algebra.commutes c0 a]
      _ = algebraMap K B c0 * (a * e0) := by rw [mul_assoc]
      _ = algebraMap K B c0 * a := by
        dsimp [e0]
        rw [hR]
      _ = c0 • a := by rw [Algebra.smul_def]
  have hr1 : a * (r * e1) = 0 := by
    have hEq :
        a * (r * e1) = a * (algebraMap K B c1 * e1) := by
      rw [mul_sub, sub_eq_zero] at hkill1
      exact hkill1
    calc
      a * (r * e1) = a * (algebraMap K B c1 * e1) := hEq
      _ = (a * algebraMap K B c1) * e1 := by rw [mul_assoc]
      _ = (algebraMap K B c1 * a) * e1 := by
        rw [← Algebra.commutes c1 a]
      _ = algebraMap K B c1 * (a * e1) := by rw [mul_assoc]
      _ = 0 := by rw [hae1, mul_zero]
  calc
    a * r = a * (r * (e0 + e1)) := by rw [hsum, mul_one]
    _ = a * (r * e0) + a * (r * e1) := by noncomm_ring
    _ = c0 • a := by rw [hr0, hr1, add_zero]
    _ = OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter D 0 r • a := rfl

/-- A single nonzero cross class spanning `J/J²` forces the exact
one-dimensional radical normal form and radical square zero. -/
theorem singleCrossRadicalData_of_cotangentSpanned
    {a : B}
    (hL : D.liftedCoordinate 1 * a = a)
    (hR : a * D.liftedCoordinate 0 = a)
    (hspan : JacobsonCotangentSpannedBy (K := K) (0 : B) a 0) :
    SingleCrossRadicalData (K := K) a := by
  have haJ : a ∈ J B := D.singleCross_a_mem_jacobson hL hR
  have ha2 : a * a = 0 := D.singleCross_a_sq hL hR
  have hspanEq :
      ((J B : Submodule B B).restrictScalars K) =
        Submodule.span K {a} := by
    apply le_antisymm
    · intro z hz
      obtain ⟨r, hzEq⟩ := singleCross_rightGenerated hspan hz
      rw [hzEq, D.singleCross_scalar_reduce hR ha2 hspan]
      exact Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self a)
    · intro z hz
      rw [Submodule.mem_span_singleton] at hz
      obtain ⟨c, rfl⟩ := hz
      exact ((J B : Submodule B B).restrictScalars K).smul_mem c haJ
  have hJ2 : (J B) ^ 2 = ⊥ := by
    apply le_antisymm
    · intro z hz
      have hz' : z ∈ J B * J B := by
        rw [show (2 : Nat) = 1 + 1 by omega,
          Submodule.pow_succ, Submodule.pow_one] at hz
        exact hz
      refine Submodule.mul_induction_on hz' ?_ ?_
      · intro x hx y hy
        rw [Submodule.mem_bot]
        obtain ⟨r, rfl⟩ := singleCross_rightGenerated hspan hx
        calc
          (a * r) * y = a * (r * y) := by rw [mul_assoc]
          _ = 0 := singleCross_a_mul_eq_zero_of_mem_jacobson
            ha2 hspan ((J B).mul_mem_left r hy)
      · intro x y hx hy
        rw [Submodule.mem_bot] at hx hy ⊢
        rw [hx, hy, add_zero]
    · exact bot_le
  exact ⟨haJ, ha2, hspanEq, hJ2⟩

/-- Orientation-free form of the single-cross theorem.  Any two distinct
coordinates may serve as the left and right endpoints of the surviving
cotangent class. -/
theorem singleCrossRadicalData_of_cotangentSpanned_at
    {i j : Fin 2} (hij : i ≠ j) {a : B}
    (hL : D.liftedCoordinate i * a = a)
    (hR : a * D.liftedCoordinate j = a)
    (hspan : JacobsonCotangentSpannedBy (K := K) (0 : B) a 0) :
    SingleCrossRadicalData (K := K) a := by
  classical
  let J : Ideal B := Ring.jacobson B
  have haJ : a ∈ J := by
    have h := D.offDiagonal_mem_jacobson hij a
    rw [hL, hR] at h
    exact h
  have ha2 : a * a = 0 := by
    calc
      a * a =
          (a * D.liftedCoordinate j) *
            (D.liftedCoordinate i * a) := by rw [hL, hR]
      _ = a *
          (D.liftedCoordinate j * D.liftedCoordinate i) * a := by
        noncomm_ring
      _ = 0 := by
        rw [D.liftedCoordinate_complete.ortho hij.symm]
        simp
  have hrightGenerated {z : B} (hz : z ∈ J) :
      ∃ r : B, z = a * r := by
    obtain ⟨rx, ra, rb, hzEq⟩ :=
      (jacobsonRightGeneratedBy_of_cotangentSpanned hspan) z hz
    refine ⟨ra, ?_⟩
    simpa using hzEq
  have hakill {z : B} (hz : z ∈ J) : a * z = 0 := by
    obtain ⟨r, rfl⟩ := hrightGenerated hz
    calc
      a * (a * r) = (a * a) * r := by rw [mul_assoc]
      _ = 0 := by rw [ha2, zero_mul]
  have hae (k : Fin 2) (hjk : j ≠ k) :
      a * D.liftedCoordinate k = 0 := by
    calc
      a * D.liftedCoordinate k =
          (a * D.liftedCoordinate j) * D.liftedCoordinate k := by
            rw [hR]
      _ = a *
          (D.liftedCoordinate j * D.liftedCoordinate k) := by
            rw [mul_assoc]
      _ = 0 := by
        rw [D.liftedCoordinate_complete.ortho hjk]
        simp
  have hscalar (r : B) :
      a * r =
        OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter
          D j r • a := by
    have hcoord (k : Fin 2) :
        a * (r * D.liftedCoordinate k) =
          OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter
            D k r • (a * D.liftedCoordinate k) := by
      let c :=
        OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter
          D k r
      have hkill :
          a *
            (r * D.liftedCoordinate k -
              algebraMap K B c * D.liftedCoordinate k) = 0 := by
        apply hakill
        exact
          OpConjecture.CotangentExtBridge.CoordinateData.mul_liftedCoordinate_sub_coordinate_mem_jacobson
            D k r
      have heq :
          a * (r * D.liftedCoordinate k) =
            a * (algebraMap K B c * D.liftedCoordinate k) := by
        rw [mul_sub, sub_eq_zero] at hkill
        exact hkill
      calc
        a * (r * D.liftedCoordinate k) =
            a * (algebraMap K B c * D.liftedCoordinate k) := heq
        _ = (a * algebraMap K B c) * D.liftedCoordinate k := by
          rw [mul_assoc]
        _ = (algebraMap K B c * a) * D.liftedCoordinate k := by
          rw [← Algebra.commutes c a]
        _ = algebraMap K B c * (a * D.liftedCoordinate k) := by
          rw [mul_assoc]
        _ = c • (a * D.liftedCoordinate k) := by
          rw [Algebra.smul_def]
        _ =
            OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter
              D k r • (a * D.liftedCoordinate k) := rfl
    have hrDecomp :
        r = ∑ k : Fin 2, r * D.liftedCoordinate k := by
      rw [← Finset.mul_sum]
      rw [D.liftedCoordinate_complete.complete, mul_one]
    have hsum :
        (∑ k : Fin 2,
          OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter
              D k r • (a * D.liftedCoordinate k)) =
          OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter
              D j r • (a * D.liftedCoordinate j) := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        rw [hae k hkj.symm]
        simp
      · simp
    calc
      a * r = a * (∑ k : Fin 2, r * D.liftedCoordinate k) := by
        rw [← hrDecomp]
      _ = ∑ k : Fin 2, a * (r * D.liftedCoordinate k) := by
        rw [Finset.mul_sum]
      _ = ∑ k : Fin 2,
          OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter
              D k r • (a * D.liftedCoordinate k) := by
        apply Finset.sum_congr rfl
        intro k _
        exact hcoord k
      _ =
          OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter
              D j r • (a * D.liftedCoordinate j) := hsum
      _ =
          OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter
              D j r • a := by rw [hR]
  have hspanEq :
      ((J : Submodule B B).restrictScalars K) =
        Submodule.span K {a} := by
    apply le_antisymm
    · intro z hz
      obtain ⟨r, hzEq⟩ := hrightGenerated hz
      rw [hzEq, hscalar r]
      exact Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self a)
    · intro z hz
      rw [Submodule.mem_span_singleton] at hz
      obtain ⟨c, rfl⟩ := hz
      exact ((J : Submodule B B).restrictScalars K).smul_mem c haJ
  have hJ2 : J ^ 2 = ⊥ := by
    apply le_antisymm
    · intro z hz
      have hz' : z ∈ J * J := by
        rw [show (2 : Nat) = 1 + 1 by omega,
          Submodule.pow_succ, Submodule.pow_one] at hz
        exact hz
      refine Submodule.mul_induction_on hz' ?_ ?_
      · intro x hx y hy
        rw [Submodule.mem_bot]
        obtain ⟨r, rfl⟩ := hrightGenerated hx
        calc
          (a * r) * y = a * (r * y) := by rw [mul_assoc]
          _ = 0 := hakill (J.mul_mem_left r hy)
      · intro x y hx hy
        rw [Submodule.mem_bot] at hx hy ⊢
        rw [hx, hy, add_zero]
    · exact bot_le
  exact ⟨haJ, ha2, hspanEq, hJ2⟩

end TwoCoordinateData

end OpConjecture.QuotientSurvival
