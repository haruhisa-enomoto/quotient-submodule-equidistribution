import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderTermination

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace QuotientSubmoduleEquidistribution.FactorLadder

universe u

variable {D : Type u} [Fintype D]

/-- Evaluation of a finite integer vector against an integer label weight. -/
def weightedSum (weight : D → ℤ) (v : IntVector D) : ℤ :=
  ∑ d, v d * weight d

@[simp]
theorem weightedSum_zero (weight : D → ℤ) :
    weightedSum weight (0 : IntVector D) = 0 := by
  simp [weightedSum]

theorem weightedSum_add (weight : D → ℤ) (v w : IntVector D) :
    weightedSum weight (v + w) =
      weightedSum weight v + weightedSum weight w := by
  simp [weightedSum, add_mul, Finset.sum_add_distrib]

theorem weightedSum_sub (weight : D → ℤ) (v w : IntVector D) :
    weightedSum weight (v - w) =
      weightedSum weight v - weightedSum weight w := by
  simp [weightedSum, sub_mul, Finset.sum_sub_distrib]

@[simp]
theorem weightedSum_basis (weight : D → ℤ) (x : D) :
    weightedSum weight (basis x) = weight x := by
  classical
  simp [weightedSum, basis]

theorem weightedSum_nonneg
    {weight : D → ℤ} {v : IntVector D}
    (hweight : ∀ d, 0 ≤ weight d) (hv : ∀ d, 0 ≤ v d) :
    0 ≤ weightedSum weight v := by
  exact Finset.sum_nonneg fun d _ ↦ mul_nonneg (hv d) (hweight d)

theorem weightedSum_mono
    {weight : D → ℤ} {v w : IntVector D}
    (hweight : ∀ d, 0 ≤ weight d) (hvw : ∀ d, v d ≤ w d) :
    weightedSum weight v ≤ weightedSum weight w := by
  apply Finset.sum_le_sum
  intro d _
  exact mul_le_mul_of_nonneg_right (hvw d) (hweight d)

theorem eq_sum_zsmul_basis (v : IntVector D) :
    v = ∑ d, v d • basis d := by
  classical
  funext q
  simp [basis, Finset.sum_apply]

/-- Evaluation against a label weight as an additive homomorphism. -/
def weightedSumHom (weight : D → ℤ) : IntVector D →+ ℤ where
  toFun := weightedSum weight
  map_zero' := weightedSum_zero weight
  map_add' := weightedSum_add weight

@[simp]
theorem weightedSumHom_apply (weight : D → ℤ) (v : IntVector D) :
    weightedSumHom weight v = weightedSum weight v :=
  rfl

theorem weightedSum_map_eq_sum_basis
    (weight : D → ℤ) (F : IntVector D →+ IntVector D)
    (v : IntVector D) :
    weightedSum weight (F v) =
      ∑ d, v d * weightedSum weight (F (basis d)) := by
  let W := weightedSumHom weight
  calc
    weightedSum weight (F v) = W (F v) := rfl
    _ = W (F (∑ d, v d • basis d)) := by rw [← eq_sum_zsmul_basis v]
    _ = W (∑ d, v d • F (basis d)) := by
      congr 1
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro d _
      exact F.map_zsmul (v d) (basis d)
    _ = ∑ d, W (v d • F (basis d)) :=
      map_sum W (fun d ↦ v d • F (basis d)) Finset.univ
    _ = ∑ d, v d • W (F (basis d)) := by
      apply Finset.sum_congr rfl
      intro d _
      exact W.map_zsmul (v d) (F (basis d))
    _ = ∑ d, v d * weightedSum weight (F (basis d)) := by
      rfl

theorem weightedDefect_eq_sum_basis
    (weight : D → ℤ)
    (F G : IntVector D →+ IntVector D) (v : IntVector D) :
    weightedSum weight v - weightedSum weight (F v) +
        weightedSum weight (G v) =
      ∑ d, v d *
        (weightedSum weight (basis d) -
          weightedSum weight (F (basis d)) +
            weightedSum weight (G (basis d))) := by
  rw [weightedSum_map_eq_sum_basis weight F,
    weightedSum_map_eq_sum_basis weight G, weightedSum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [weightedSum_basis]
  ring

namespace Data

/-- A positive label weight whose mesh defect vanishes away from a boundary
forces every eventually-zero nonnegative factor ladder to reach that
boundary.  The proof is a telescoping monotonicity argument which remains
valid in the presence of coefficientwise truncation. -/
theorem reachesBoundary_of_positiveWeight
    (A : Data D) (P : Set D) (x : D)
    (weight : D → ℤ)
    (hweight : ∀ d, 0 < weight d)
    (hladder : ∀ n d, 0 ≤ A.ladder x n d)
    (hdefect : ∀ d, d ∉ P →
      weightedSum weight (basis d) -
          weightedSum weight (A.theta (basis d)) +
            weightedSum weight (A.tau (basis d)) = 0)
    (heventually : A.EventuallyZero x) :
    A.ReachesBoundary P x := by
  by_contra hreach
  have havoid : A.AvoidsBoundary P x :=
    (A.avoidsBoundary_iff_not_reachesBoundary P x).2 hreach
  have hboundary_zero (n : ℕ) {p : D} (hp : p ∈ P) :
      A.ladder x n p = 0 := by
    have hnpos := havoid n p hp
    have hnneg := hladder n p
    omega
  have heuler (n : ℕ) :
      weightedSum weight (A.ladder x n) -
          weightedSum weight (A.theta (A.ladder x n)) +
            weightedSum weight (A.tau (A.ladder x n)) = 0 := by
    rw [weightedDefect_eq_sum_basis]
    apply Finset.sum_eq_zero
    intro d _
    by_cases hd : d ∈ P
    · rw [hboundary_zero n hd]
      simp
    · rw [hdefect d hd]
      simp
  have hstep (n : ℕ) :
      weightedSum weight (A.ladder x (n + 1)) -
          weightedSum weight (A.tau (A.ladder x n)) ≤
        weightedSum weight (A.ladder x (n + 2)) -
          weightedSum weight (A.tau (A.ladder x (n + 1))) := by
    have hpoint (d : D) :
        (A.theta (A.ladder x (n + 1)) -
            A.tau (A.ladder x n)) d ≤
          A.ladder x (n + 2) d := by
      rw [A.ladder_add_two]
      exact le_max_left _ _
    have hmono := weightedSum_mono
      (fun d ↦ (hweight d).le) hpoint
    rw [weightedSum_sub] at hmono
    have he := heuler (n + 1)
    omega
  have hinitial :
      weightedSum weight (A.ladder x 0) =
        weightedSum weight (A.ladder x 1) -
          weightedSum weight (A.tau (A.ladder x 0)) := by
    have he := heuler 0
    rw [A.ladder_zero] at he ⊢
    simpa only [A.ladder_one] using (eq_sub_iff_add_eq.mpr (by omega :
      weightedSum weight (basis x) +
          weightedSum weight (A.tau (basis x)) =
        weightedSum weight (A.theta (basis x))))
  have hchain_all (M : ℕ) :
      weightedSum weight (A.ladder x 1) -
          weightedSum weight (A.tau (A.ladder x 0)) ≤
        weightedSum weight (A.ladder x (M + 1)) -
          weightedSum weight (A.tau (A.ladder x M)) := by
    induction M with
    | zero => exact le_refl _
    | succ M ih => exact ih.trans (hstep M)
  obtain ⟨N, hN⟩ := heventually
  have hchain :
      weightedSum weight (A.ladder x 1) -
          weightedSum weight (A.tau (A.ladder x 0)) ≤
        weightedSum weight (A.ladder x (N + 1)) -
          weightedSum weight (A.tau (A.ladder x N)) :=
    hchain_all N
  have hnonpos : weightedSum weight (A.ladder x 0) ≤
      weightedSum weight (A.ladder x (N + 1)) -
        weightedSum weight (A.tau (A.ladder x N)) :=
    hinitial.trans_le hchain
  rw [hN N (le_refl N), hN (N + 1) (by omega), map_zero] at hnonpos
  simp only [weightedSum_zero, sub_self] at hnonpos
  rw [A.ladder_zero, weightedSum_basis] at hnonpos
  exact (not_lt_of_ge hnonpos) (hweight x)

end Data

end QuotientSubmoduleEquidistribution.FactorLadder
