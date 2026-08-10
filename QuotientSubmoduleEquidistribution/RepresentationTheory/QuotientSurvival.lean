import QuotientSubmoduleEquidistribution.RepresentationTheory.PrincipalRightIdealSurvival
import QuotientSubmoduleEquidistribution.RepresentationTheory.SixCoordinateQuotientConstructor

/-!
# Abstract quotient survival and filtered basis detection

This file isolates two general inputs in the paper's six-class quotient
construction:

* membership of the distinguished degree-two element in the quotient ideal
  has the radical-error normal form `y = x * t + y * s`, `s ∈ J`; and
* linear detectors distinguish the two degree-zero and three degree-one
  classes.

The separate basis-level constructor still requires spanning and the finite
multiplication table.  No bound quiver algebra or module classification is
constructed here.
-/

noncomputable section

open CategoryTheory MulOpposite

namespace QuotientSubmoduleEquidistribution.QuotientSurvival

universe u v

open QuotientSubmoduleEquidistribution.Tsukamoto
open QuotientSubmoduleEquidistribution.LoopTwoCycleFamily

/-- Quotient survival from the precise normal-form input left by the
Peirce/radical calculation. -/
theorem quotient_mk_ne_zero_of_relation_normalForm
    {K : Type u} {A : Type v}
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (H : Ideal A) [H.IsTwoSided]
    {x y : A}
    (hy2 : y ∈ (Ring.jacobson A) ^ 2)
    (hx2 : x ∉ (Ring.jacobson A) ^ 2)
    (e : cyclicRightIdealFG y ≅ cyclicRightIdealFG x)
    (hnormal : y ∈ H →
      ∃ t s : A, s ∈ Ring.jacobson A ∧ y = x * t + y * s) :
    Ideal.Quotient.mk H y ≠ 0 := by
  intro hzero
  have hyH : y ∈ H := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  obtain ⟨t, s, hs, hrel⟩ := hnormal hyH
  exact
    false_of_cyclicRightIdeal_iso_of_jacobsonSquare_separation
      K e hs hrel hy2 hx2

/-- Literal scalar-square relation used in the manuscript.  Centrality of
the scalar coefficient rewrites `c • x² + x*r` as one right multiple of
`x`. -/
theorem false_of_scalarSquare_relation
    {K : Type u} {A : Type v}
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    {x y r s : A} (c : K)
    (e : cyclicRightIdealFG y ≅ cyclicRightIdealFG x)
    (hs : s ∈ Ring.jacobson A)
    (hrel : y = c • (x * x) + x * r + y * s)
    (hy2 : y ∈ (Ring.jacobson A) ^ 2)
    (hx2 : x ∉ (Ring.jacobson A) ^ 2) :
    False := by
  have hfactor :
      (algebraMap K A c) * x * x + x * r =
        x * ((algebraMap K A c) * x + r) := by
    rw [mul_add, ← mul_assoc, Algebra.commutes c x]
  apply
    false_of_cyclicRightIdeal_iso_of_jacobsonSquare_separation
      K e hs (a := y) (x := x)
  · rw [← hfactor]
    simpa only [Algebra.smul_def, mul_assoc] using hrel
  · exact hy2
  · exact hx2

/-- Quotient-survival wrapper with exactly the paper's
`c • x² + x*r + y*s` membership normal form. -/
theorem quotient_mk_ne_zero_of_scalarSquare_relation_normalForm
    {K : Type u} {A : Type v}
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (H : Ideal A) [H.IsTwoSided]
    {x y : A}
    (hy2 : y ∈ (Ring.jacobson A) ^ 2)
    (hx2 : x ∉ (Ring.jacobson A) ^ 2)
    (e : cyclicRightIdealFG y ≅ cyclicRightIdealFG x)
    (hnormal : y ∈ H →
      ∃ (c : K) (r s : A),
        s ∈ Ring.jacobson A ∧
          y = c • (x * x) + x * r + y * s) :
    Ideal.Quotient.mk H y ≠ 0 := by
  intro hzero
  have hyH : y ∈ H := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  obtain ⟨c, r, s, hs, hrel⟩ := hnormal hyH
  exact false_of_scalarSquare_relation c e hs hrel hy2 hx2

/-- Coordinate functions for the three degree-one basis vectors `x,a,b`. -/
def radicalCoordinateVector {K : Type u} [Field K] :
    SixBasisIndex → (Fin 3 → K)
  | .x => Pi.single 0 1
  | .a => Pi.single 1 1
  | .b => Pi.single 2 1
  | _ => 0

theorem sum_sixBasisIndex {M : Type u} [AddCommMonoid M]
    (f : SixBasisIndex → M) :
    ∑ i, f i =
      f .e₁ + f .e₂ + f .x + f .a + f .b + f .ab := by
  change ({.e₁, .e₂, .x, .a, .b, .ab} :
    Finset SixBasisIndex).sum f = _
  simp [Finset.sum_insert, add_assoc]

/-- A three-layer linear-independence principle for the ordered six
classes.  Degree zero detects `e₁,e₂`, degree one detects `x,a,b`, and a
final functional detects `ab`. -/
theorem six_linearIndependent_of_filtered_detectors
    {K S : Type u} [Field K] [AddCommGroup S] [Module K S]
    (w : SixBasisIndex → S)
    (degreeZero : S →ₗ[K] (Fin 2 → K))
    (degreeOne : S →ₗ[K] (Fin 3 → K))
    (degreeTwo : S →ₗ[K] K)
    (hzero : ∀ i,
      degreeZero (w i) =
        match i with
        | .e₁ => Pi.single 0 1
        | .e₂ => Pi.single 1 1
        | _ => 0)
    (hone : ∀ i, degreeOne (w i) = radicalCoordinateVector i)
    (htwo : degreeTwo (w .ab) ≠ 0) :
    LinearIndependent K w := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hcZero : ∑ i, c i • degreeZero (w i) = 0 := by
    calc
      ∑ i, c i • degreeZero (w i) =
          ∑ i, degreeZero (c i • w i) := by simp
      _ = degreeZero (∑ i, c i • w i) := by rw [map_sum]
      _ = 0 := by rw [hc, map_zero]
  have hce₁ : c .e₁ = 0 := by
    have h := congrFun hcZero 0
    simp [sum_sixBasisIndex, hzero] at h
    exact h
  have hce₂ : c .e₂ = 0 := by
    have h := congrFun hcZero 1
    simp [sum_sixBasisIndex, hzero] at h
    exact h
  have hcOne : ∑ i, c i • degreeOne (w i) = 0 := by
    calc
      ∑ i, c i • degreeOne (w i) =
          ∑ i, degreeOne (c i • w i) := by simp
      _ = degreeOne (∑ i, c i • w i) := by rw [map_sum]
      _ = 0 := by rw [hc, map_zero]
  have hcx : c .x = 0 := by
    have h := congrFun hcOne 0
    simp [sum_sixBasisIndex, hone, radicalCoordinateVector] at h
    exact h
  have hca : c .a = 0 := by
    have h := congrFun hcOne 1
    simp [sum_sixBasisIndex, hone, radicalCoordinateVector] at h
    exact h
  have hcb : c .b = 0 := by
    have h := congrFun hcOne 2
    simp [sum_sixBasisIndex, hone, radicalCoordinateVector] at h
    exact h
  have habRelation : c .ab • w .ab = 0 := by
    simpa [sum_sixBasisIndex, hce₁, hce₂, hcx, hca, hcb] using hc
  have hscalar : c .ab * degreeTwo (w .ab) = 0 := by
    have h := congrArg degreeTwo habRelation
    simpa only [map_smul, map_zero, smul_eq_mul] using h
  have hcab : c .ab = 0 :=
    (mul_eq_zero.mp hscalar).resolve_right htwo
  intro i
  cases i <;> assumption

/-- Over a field, nonvanishing of the `ab` vector supplies the last
detector automatically. -/
theorem six_linearIndependent_of_degreeZero_degreeOne_of_ab_ne_zero
    {K S : Type u} [Field K] [AddCommGroup S] [Module K S]
    (w : SixBasisIndex → S)
    (degreeZero : S →ₗ[K] (Fin 2 → K))
    (degreeOne : S →ₗ[K] (Fin 3 → K))
    (hzero : ∀ i,
      degreeZero (w i) =
        match i with
        | .e₁ => Pi.single 0 1
        | .e₂ => Pi.single 1 1
        | _ => 0)
    (hone : ∀ i, degreeOne (w i) = radicalCoordinateVector i)
    (hab : w .ab ≠ 0) :
    LinearIndependent K w := by
  obtain ⟨degreeTwo, htwo⟩ :=
    Module.Projective.exists_dual_ne_zero K hab
  exact six_linearIndependent_of_filtered_detectors
    w degreeZero degreeOne degreeTwo hzero hone htwo

/-- Quotient-class form of the filtered detector theorem.  The two
detectors are defined on the original algebra and need only vanish on the
quotient ideal. -/
theorem six_quotientClasses_linearIndependent_of_filtered_detectors
    {K A : Type u} [Field K] [Ring A] [Algebra K A]
    (H : Ideal A) [H.IsTwoSided]
    (w : SixBasisIndex → A)
    (degreeZero : A →ₗ[K] (Fin 2 → K))
    (degreeOne : A →ₗ[K] (Fin 3 → K))
    (hzero : ∀ i,
      degreeZero (w i) =
        match i with
        | .e₁ => Pi.single 0 1
        | .e₂ => Pi.single 1 1
        | _ => 0)
    (hone : ∀ i, degreeOne (w i) = radicalCoordinateVector i)
    (hzeroH : ∀ z ∈ H, degreeZero z = 0)
    (honeH : ∀ z ∈ H, degreeOne z = 0)
    (hab : Ideal.Quotient.mk H (w .ab) ≠ 0) :
    LinearIndependent K (fun i => Ideal.Quotient.mk H (w i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hsourceZero :
      Ideal.Quotient.mk H (∑ i, c i • w i) = 0 := by
    change Ideal.Quotient.mkₐ K H (∑ i, c i • w i) = 0
    rw [map_sum]
    simpa only [map_smul, Ideal.Quotient.mkₐ_eq_mk] using hc
  have hsourceMem : ∑ i, c i • w i ∈ H :=
    Ideal.Quotient.eq_zero_iff_mem.mp hsourceZero
  have hcZero : ∑ i, c i • degreeZero (w i) = 0 := by
    calc
      ∑ i, c i • degreeZero (w i) =
          ∑ i, degreeZero (c i • w i) := by simp
      _ = degreeZero (∑ i, c i • w i) := by rw [map_sum]
      _ = 0 := hzeroH _ hsourceMem
  have hce₁ : c .e₁ = 0 := by
    have h := congrFun hcZero 0
    simp [sum_sixBasisIndex, hzero] at h
    exact h
  have hce₂ : c .e₂ = 0 := by
    have h := congrFun hcZero 1
    simp [sum_sixBasisIndex, hzero] at h
    exact h
  have hcOne : ∑ i, c i • degreeOne (w i) = 0 := by
    calc
      ∑ i, c i • degreeOne (w i) =
          ∑ i, degreeOne (c i • w i) := by simp
      _ = degreeOne (∑ i, c i • w i) := by rw [map_sum]
      _ = 0 := honeH _ hsourceMem
  have hcx : c .x = 0 := by
    have h := congrFun hcOne 0
    simp [sum_sixBasisIndex, hone, radicalCoordinateVector] at h
    exact h
  have hca : c .a = 0 := by
    have h := congrFun hcOne 1
    simp [sum_sixBasisIndex, hone, radicalCoordinateVector] at h
    exact h
  have hcb : c .b = 0 := by
    have h := congrFun hcOne 2
    simp [sum_sixBasisIndex, hone, radicalCoordinateVector] at h
    exact h
  have habRelation :
      c .ab • Ideal.Quotient.mk H (w .ab) = 0 := by
    simpa [sum_sixBasisIndex, hce₁, hce₂, hcx, hca, hcb] using hc
  have hcab : c .ab = 0 :=
    (smul_eq_zero.mp habRelation).resolve_right hab
  intro i
  cases i <;> assumption

end QuotientSubmoduleEquidistribution.QuotientSurvival
