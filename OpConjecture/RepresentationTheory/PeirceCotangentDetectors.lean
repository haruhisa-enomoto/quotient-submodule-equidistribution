import OpConjecture.RepresentationTheory.QuotientSurvival
import OpConjecture.RepresentationTheory.CotangentExtBridge
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Peirce-localized residue and cotangent detectors

This file removes the abstract detector hypotheses from the six-class quotient
constructor by Peirce-localized residue and cotangent maps.  No concrete bound
algebra is used.
-/

noncomputable section

namespace OpConjecture.QuotientSurvival

universe u

open OpConjecture.LoopTwoCycleFamily
open OpConjecture.CotangentExtBridge

variable {K B : Type u}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]

abbrev TwoCoordinateData :=
  OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData
    (K := K) (B := B) (I := Fin 2)

namespace TwoCoordinateData

variable (D : TwoCoordinateData (K := K) (B := B))

/-! ## The abstract two-sided relation ideal -/

/-- The relation generators from the loop-plus-two-cycle branch, expressed
in the algebra multiplication convention used by the six-coordinate table.
The entire ideal `J³` is included as a generating subset. -/
def loopTwoCycleRelationSet (x a b : B) : Set B :=
  (↑((Ring.jacobson B) ^ 3) : Set B) ∪ {x * x, a * x, x * b, a * b}

/-- The smallest two-sided ideal containing the relation generators. -/
def loopTwoCycleRelationIdeal (x a b : B) : Ideal B :=
  (TwoSidedIdeal.span (loopTwoCycleRelationSet x a b)).asIdeal

instance loopTwoCycleRelationIdeal_isTwoSided (x a b : B) :
    (loopTwoCycleRelationIdeal x a b).IsTwoSided := by
  unfold loopTwoCycleRelationIdeal
  infer_instance

omit [IsArtinianRing B] in
theorem loopTwoCycleRelationSet_subset_jacobsonSquare
    {x a b : B}
    (hxJ : x ∈ Ring.jacobson B)
    (haJ : a ∈ Ring.jacobson B)
    (hbJ : b ∈ Ring.jacobson B) :
    loopTwoCycleRelationSet x a b ⊆
      (↑((Ring.jacobson B) ^ 2) : Set B) := by
  intro z hz
  rcases hz with hz3 | hz
  · exact Ideal.pow_le_pow_right (by omega : 2 ≤ 3) hz3
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hmul {r s : B}
        (hr : r ∈ Ring.jacobson B) (hs : s ∈ Ring.jacobson B) :
        r * s ∈ (Ring.jacobson B) ^ 2 := by
      rw [show (2 : ℕ) = 1 + 1 by omega, Submodule.pow_succ,
        Submodule.pow_one]
      exact Ideal.mul_mem_mul hr hs
    rcases hz with rfl | rfl | rfl | rfl
    · exact hmul hxJ hxJ
    · exact hmul haJ hxJ
    · exact hmul hxJ hbJ
    · exact hmul haJ hbJ

omit [IsArtinianRing B] in
/-- The intended two-sided relation ideal automatically lies in `J²`; this
is the exact fact needed by the filtered detector argument. -/
theorem loopTwoCycleRelationIdeal_le_jacobsonSquare
    {x a b : B}
    (hxJ : x ∈ Ring.jacobson B)
    (haJ : a ∈ Ring.jacobson B)
    (hbJ : b ∈ Ring.jacobson B) :
    loopTwoCycleRelationIdeal x a b ≤ (Ring.jacobson B) ^ 2 := by
  let J2 : TwoSidedIdeal B := ((Ring.jacobson B) ^ 2).toTwoSided
  have hspan :
      TwoSidedIdeal.span (loopTwoCycleRelationSet x a b) ≤ J2 :=
    TwoSidedIdeal.span_le.mpr fun z hz ↦ by
      simpa [J2] using
        loopTwoCycleRelationSet_subset_jacobsonSquare hxJ haJ hbJ hz
  intro z hz
  simpa [J2] using hspan hz

/-- The two residue-field coordinates, viewed as one vector-valued linear
map. -/
def degreeZeroDetector : B →ₗ[K] (Fin 2 → K) :=
  LinearMap.pi fun i ↦
    (CoordinateData.coordinateCharacter D i).toLinearMap

omit [IsArtinianRing B] in
@[simp]
theorem degreeZeroDetector_apply (z : B) (i : Fin 2) :
    D.degreeZeroDetector z i = CoordinateData.coordinateCharacter D i z := rfl

/-- The linear Peirce projection `z ↦ eᵢ z eⱼ`. -/
def peirceLinearMap (i j : Fin 2) : B →ₗ[K] B :=
  LinearMap.mulLeftRight K (D.liftedCoordinate i, D.liftedCoordinate j)

@[simp]
theorem peirceLinearMap_apply (i j : Fin 2) (z : B) :
    D.peirceLinearMap i j z =
      D.liftedCoordinate i * z * D.liftedCoordinate j := rfl

/-- Remove the split semisimple-coordinate part of an element. -/
def radicalRemainder : B →ₗ[K] B :=
  LinearMap.id - ∑ i : Fin 2,
    LinearMap.smulRight
      (CoordinateData.coordinateCharacter D i).toLinearMap
      (D.liftedCoordinate i)

theorem radicalRemainder_eq_self_of_mem_jacobson
    {z : B} (hz : z ∈ Ring.jacobson B) :
    D.radicalRemainder z = z := by
  simp only [radicalRemainder, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hzero : ∀ i : Fin 2,
      CoordinateData.coordinateCharacter D i z = 0 := fun i ↦
    CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D i hz
  simp [hzero]

theorem radicalRemainder_liftedCoordinate (q : Fin 2) :
    D.radicalRemainder (D.liftedCoordinate q) = 0 := by
  fin_cases q <;>
    simp [radicalRemainder,
      CoordinateData.coordinateCharacter_liftedCoordinate_ne]

/-- A chosen functional which is nonzero on `c` and vanishes on `J²`. -/
def cotangentFunctional (_D : TwoCoordinateData (K := K) (B := B)) {c : B}
    (hc2 : c ∉ (Ring.jacobson B) ^ 2) : B →ₗ[K] K :=
  (CoordinateData.exists_cotangent_functional (K := K) hc2).choose

omit [IsArtinianRing B] in
theorem cotangentFunctional_ne_zero {c : B}
    (hc2 : c ∉ (Ring.jacobson B) ^ 2) :
    D.cotangentFunctional hc2 c ≠ 0 :=
  (CoordinateData.exists_cotangent_functional (K := K) hc2).choose_spec.1

omit [IsArtinianRing B] in
theorem cotangentFunctional_vanishes_square {c : B}
    (hc2 : c ∉ (Ring.jacobson B) ^ 2) :
    ∀ z ∈ (Ring.jacobson B) ^ 2,
      D.cotangentFunctional hc2 z = 0 :=
  (CoordinateData.exists_cotangent_functional (K := K) hc2).choose_spec.2

/-- Normalize a cotangent functional after restricting it to one Peirce
corner. -/
def normalizedPeirceCotangentFunctional
    (i j : Fin 2) {c : B}
    (hc2 : c ∉ (Ring.jacobson B) ^ 2) : B →ₗ[K] K :=
  (D.cotangentFunctional hc2 c)⁻¹ •
    ((D.cotangentFunctional hc2).comp D.radicalRemainder).comp
      (D.peirceLinearMap i j)

theorem normalizedPeirceCotangentFunctional_self
    (i j : Fin 2) {c : B}
    (hcJ : c ∈ Ring.jacobson B)
    (hleft : D.liftedCoordinate i * c = c)
    (hright : c * D.liftedCoordinate j = c)
    (hc2 : c ∉ (Ring.jacobson B) ^ 2) :
    D.normalizedPeirceCotangentFunctional i j hc2 c = 1 := by
  simp only [normalizedPeirceCotangentFunctional, LinearMap.smul_apply,
    LinearMap.comp_apply, peirceLinearMap_apply, hleft, hright,
    D.radicalRemainder_eq_self_of_mem_jacobson hcJ]
  exact inv_mul_cancel₀ (D.cotangentFunctional_ne_zero hc2)

theorem normalizedPeirceCotangentFunctional_vanishes_square
    (i j : Fin 2) {c : B}
    (hc2 : c ∉ (Ring.jacobson B) ^ 2) :
    ∀ z ∈ (Ring.jacobson B) ^ 2,
      D.normalizedPeirceCotangentFunctional i j hc2 z = 0 := by
  intro z hz
  have hcorner2 :
      D.liftedCoordinate i * z * D.liftedCoordinate j ∈
        (Ring.jacobson B) ^ 2 :=
    Ideal.mul_mem_right _ _
      (Ideal.mul_mem_left _ (D.liftedCoordinate i) hz)
  rw [normalizedPeirceCotangentFunctional, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, peirceLinearMap_apply,
    D.radicalRemainder_eq_self_of_mem_jacobson
      (Ideal.pow_le_self two_ne_zero hcorner2)]
  simp [D.cotangentFunctional_vanishes_square hc2 _ hcorner2]

/-- A localized cotangent detector vanishes on a representative from a
different Peirce corner. -/
theorem normalizedPeirceCotangentFunctional_eq_zero_of_corner_ne
    (i j k l : Fin 2) {c d : B}
    (hdleft : D.liftedCoordinate k * d = d)
    (hdright : d * D.liftedCoordinate l = d)
    (hc2 : c ∉ (Ring.jacobson B) ^ 2)
    (hcorner : i ≠ k ∨ j ≠ l) :
    D.normalizedPeirceCotangentFunctional i j hc2 d = 0 := by
  rcases hcorner with hik | hjl
  · have hzero : D.liftedCoordinate i * d = 0 := by
      calc
        D.liftedCoordinate i * d =
            D.liftedCoordinate i * (D.liftedCoordinate k * d) := by rw [hdleft]
        _ = (D.liftedCoordinate i * D.liftedCoordinate k) * d := by
          rw [mul_assoc]
        _ = 0 := by rw [D.liftedCoordinate_complete.ortho hik]; simp
    have hpeirce :
        D.liftedCoordinate i * d * D.liftedCoordinate j = 0 := by
      rw [hzero, zero_mul]
    simp [normalizedPeirceCotangentFunctional, peirceLinearMap, hpeirce]
  · have hzero : d * D.liftedCoordinate j = 0 := by
      calc
        d * D.liftedCoordinate j =
            (d * D.liftedCoordinate l) * D.liftedCoordinate j := by rw [hdright]
        _ = d * (D.liftedCoordinate l * D.liftedCoordinate j) := by
          rw [mul_assoc]
        _ = 0 := by
          rw [D.liftedCoordinate_complete.ortho hjl.symm]
          simp
    have hpeirce :
        D.liftedCoordinate i * d * D.liftedCoordinate j = 0 := by
      rw [mul_assoc, hzero, mul_zero]
    simp [normalizedPeirceCotangentFunctional, peirceLinearMap, hpeirce]

theorem normalizedPeirceCotangentFunctional_liftedCoordinate
    (i j q : Fin 2) {c : B}
    (hc2 : c ∉ (Ring.jacobson B) ^ 2) :
    D.normalizedPeirceCotangentFunctional i j hc2
        (D.liftedCoordinate q) = 0 := by
  by_cases hiq : i = q
  · subst i
    by_cases hjq : j = q
    · subst j
      have hpeirce :
          D.liftedCoordinate q * D.liftedCoordinate q *
              D.liftedCoordinate q = D.liftedCoordinate q := by
        rw [D.liftedCoordinate_complete.idem q,
          D.liftedCoordinate_complete.idem q]
      simp [normalizedPeirceCotangentFunctional, peirceLinearMap,
        hpeirce, D.radicalRemainder_liftedCoordinate q]
    · have hpeirce :
          D.liftedCoordinate q * D.liftedCoordinate q *
              D.liftedCoordinate j = 0 := by
        rw [D.liftedCoordinate_complete.idem q,
          D.liftedCoordinate_complete.ortho (Ne.symm hjq)]
      simp [normalizedPeirceCotangentFunctional, peirceLinearMap, hpeirce]
  · have hpeirce :
        D.liftedCoordinate i * D.liftedCoordinate q *
            D.liftedCoordinate j = 0 := by
      rw [D.liftedCoordinate_complete.ortho hiq, zero_mul]
    simp [normalizedPeirceCotangentFunctional, peirceLinearMap, hpeirce]

/-- The three cotangent detectors for a loop at vertex `0` and opposite
cross-corner representatives. -/
def degreeOneDetector
    {x a b : B}
    (hx2 : x ∉ (Ring.jacobson B) ^ 2)
    (ha2 : a ∉ (Ring.jacobson B) ^ 2)
    (hb2 : b ∉ (Ring.jacobson B) ^ 2) :
    B →ₗ[K] (Fin 3 → K) :=
  LinearMap.pi fun i ↦
    match i with
    | 0 => D.normalizedPeirceCotangentFunctional 0 0 hx2
    | 1 => D.normalizedPeirceCotangentFunctional 1 0 ha2
    | 2 => D.normalizedPeirceCotangentFunctional 0 1 hb2

/-- The ordered six elements used by the quotient argument.  The path named
`ab` in the manuscript is the algebra product `b*a` in the present
multiplication convention. -/
def sixPeirceElements (x a b : B) : SixBasisIndex → B
  | .e₁ => D.liftedCoordinate 0
  | .e₂ => D.liftedCoordinate 1
  | .x => x
  | .a => a
  | .b => b
  | .ab => b * a

theorem degreeZeroDetector_sixPeirceElements
    {x a b : B}
    (hxJ : x ∈ Ring.jacobson B)
    (haJ : a ∈ Ring.jacobson B)
    (hbJ : b ∈ Ring.jacobson B) :
    ∀ i,
      D.degreeZeroDetector (D.sixPeirceElements x a b i) =
        match i with
        | .e₁ => Pi.single 0 1
        | .e₂ => Pi.single 1 1
        | _ => 0 := by
  intro i
  funext q
  cases i
  · fin_cases q <;> simp [degreeZeroDetector, sixPeirceElements]
  · fin_cases q <;> simp [degreeZeroDetector, sixPeirceElements]
  · exact CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D q hxJ
  · exact CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D q haJ
  · exact CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D q hbJ
  · exact CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D q
      (Ideal.mul_mem_left _ b haJ)

theorem degreeOneDetector_sixPeirceElements
    {x a b : B}
    (hxJ : x ∈ Ring.jacobson B)
    (haJ : a ∈ Ring.jacobson B)
    (hbJ : b ∈ Ring.jacobson B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hbleft : D.liftedCoordinate 0 * b = b)
    (hbright : b * D.liftedCoordinate 1 = b)
    (hx2 : x ∉ (Ring.jacobson B) ^ 2)
    (ha2 : a ∉ (Ring.jacobson B) ^ 2)
    (hb2 : b ∉ (Ring.jacobson B) ^ 2) :
    ∀ i,
      D.degreeOneDetector hx2 ha2 hb2 (D.sixPeirceElements x a b i) =
        radicalCoordinateVector i := by
  intro i
  funext q
  cases i
  · fin_cases q <;>
      simpa [degreeOneDetector, radicalCoordinateVector, sixPeirceElements] using
        D.normalizedPeirceCotangentFunctional_liftedCoordinate
          (q := 0) _ _ (by assumption)
  · fin_cases q <;>
      simpa [degreeOneDetector, radicalCoordinateVector, sixPeirceElements] using
        D.normalizedPeirceCotangentFunctional_liftedCoordinate
          (q := 1) _ _ (by assumption)
  · fin_cases q
    · simpa [degreeOneDetector, radicalCoordinateVector, sixPeirceElements] using
        D.normalizedPeirceCotangentFunctional_self 0 0 hxJ hxleft hxright hx2
    · simpa [degreeOneDetector, radicalCoordinateVector, sixPeirceElements] using
        D.normalizedPeirceCotangentFunctional_eq_zero_of_corner_ne
          1 0 0 0 hxleft hxright ha2 (Or.inl (by decide))
    · simpa [degreeOneDetector, radicalCoordinateVector, sixPeirceElements] using
        D.normalizedPeirceCotangentFunctional_eq_zero_of_corner_ne
          0 1 0 0 hxleft hxright hb2 (Or.inr (by decide))
  · fin_cases q
    · simpa [degreeOneDetector, radicalCoordinateVector, sixPeirceElements] using
        D.normalizedPeirceCotangentFunctional_eq_zero_of_corner_ne
          0 0 1 0 haleft haright hx2 (Or.inl (by decide))
    · simpa [degreeOneDetector, radicalCoordinateVector, sixPeirceElements] using
        D.normalizedPeirceCotangentFunctional_self 1 0 haJ haleft haright ha2
    · simpa [degreeOneDetector, radicalCoordinateVector, sixPeirceElements] using
        D.normalizedPeirceCotangentFunctional_eq_zero_of_corner_ne
          0 1 1 0 haleft haright hb2 (Or.inl (by decide))
  · fin_cases q
    · simpa [degreeOneDetector, radicalCoordinateVector, sixPeirceElements] using
        D.normalizedPeirceCotangentFunctional_eq_zero_of_corner_ne
          0 0 0 1 hbleft hbright hx2 (Or.inr (by decide))
    · simpa [degreeOneDetector, radicalCoordinateVector, sixPeirceElements] using
        D.normalizedPeirceCotangentFunctional_eq_zero_of_corner_ne
          1 0 0 1 hbleft hbright ha2 (Or.inl (by decide))
    · simpa [degreeOneDetector, radicalCoordinateVector, sixPeirceElements] using
        D.normalizedPeirceCotangentFunctional_self 0 1 hbJ hbleft hbright hb2
  · have hba2 : b * a ∈ (Ring.jacobson B) ^ 2 := by
      rw [show (2 : ℕ) = 1 + 1 by omega, Submodule.pow_succ,
        Submodule.pow_one]
      exact Ideal.mul_mem_mul hbJ haJ
    fin_cases q <;>
      simpa [degreeOneDetector, radicalCoordinateVector, sixPeirceElements] using
        D.normalizedPeirceCotangentFunctional_vanishes_square
          _ _ (by assumption) _ hba2

/-- Split residue coordinates and the three Peirce cotangent classes provide
the degree-zero and degree-one detectors automatically.  Thus a two-sided
quotient ideal inside `J²`, together with survival of `b*a`, makes the six
named quotient classes linearly independent. -/
theorem six_quotientClasses_linearIndependent_of_peirceCotangent
    {x a b : B}
    (hxJ : x ∈ Ring.jacobson B)
    (haJ : a ∈ Ring.jacobson B)
    (hbJ : b ∈ Ring.jacobson B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hbleft : D.liftedCoordinate 0 * b = b)
    (hbright : b * D.liftedCoordinate 1 = b)
    (hx2 : x ∉ (Ring.jacobson B) ^ 2)
    (ha2 : a ∉ (Ring.jacobson B) ^ 2)
    (hb2 : b ∉ (Ring.jacobson B) ^ 2)
    (H : Ideal B) [H.IsTwoSided]
    (hH2 : H ≤ (Ring.jacobson B) ^ 2)
    (hba : Ideal.Quotient.mk H (b * a) ≠ 0) :
    LinearIndependent K
      (fun i ↦ Ideal.Quotient.mk H (D.sixPeirceElements x a b i)) := by
  apply six_quotientClasses_linearIndependent_of_filtered_detectors
    H (D.sixPeirceElements x a b)
      D.degreeZeroDetector (D.degreeOneDetector hx2 ha2 hb2)
  · exact D.degreeZeroDetector_sixPeirceElements hxJ haJ hbJ
  · exact D.degreeOneDetector_sixPeirceElements
      hxJ haJ hbJ hxleft hxright haleft haright hbleft hbright hx2 ha2 hb2
  · intro z hz
    funext q
    exact CoordinateData.coordinateCharacter_eq_zero_of_mem_jacobson D q
      (Ideal.pow_le_self two_ne_zero (hH2 hz))
  · intro z hz
    funext q
    fin_cases q <;>
      exact D.normalizedPeirceCotangentFunctional_vanishes_square
        _ _ (by assumption) z (hH2 hz)
  · simpa [sixPeirceElements] using hba

/-- For the actual abstract relation ideal generated by `J³`, `x²`, `a*x`,
`x*b`, and `a*b`, containment in `J²` is automatic.  Survival of `b*a` is
therefore the only remaining quotient-side premise for six-class linear
independence. -/
theorem six_relationQuotientClasses_linearIndependent_of_peirceCotangent
    {x a b : B}
    (hxJ : x ∈ Ring.jacobson B)
    (haJ : a ∈ Ring.jacobson B)
    (hbJ : b ∈ Ring.jacobson B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hbleft : D.liftedCoordinate 0 * b = b)
    (hbright : b * D.liftedCoordinate 1 = b)
    (hx2 : x ∉ (Ring.jacobson B) ^ 2)
    (ha2 : a ∉ (Ring.jacobson B) ^ 2)
    (hb2 : b ∉ (Ring.jacobson B) ^ 2)
    (hba : Ideal.Quotient.mk (loopTwoCycleRelationIdeal x a b) (b * a) ≠ 0) :
    LinearIndependent K
      (fun i ↦ Ideal.Quotient.mk (loopTwoCycleRelationIdeal x a b)
        (D.sixPeirceElements x a b i)) :=
  D.six_quotientClasses_linearIndependent_of_peirceCotangent
    hxJ haJ hbJ hxleft hxright haleft haright hbleft hbright
      hx2 ha2 hb2 (loopTwoCycleRelationIdeal x a b)
      (loopTwoCycleRelationIdeal_le_jacobsonSquare hxJ haJ hbJ) hba

/-- Quotient-facing endpoint with the survival normal form still exposed as
the only non-detector algebra input. -/
theorem six_quotientClasses_linearIndependent_of_peirceCotangent_of_normalForm
    [FiniteDimensional K B]
    {x a b : B}
    (hxJ : x ∈ Ring.jacobson B)
    (haJ : a ∈ Ring.jacobson B)
    (hbJ : b ∈ Ring.jacobson B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hbleft : D.liftedCoordinate 0 * b = b)
    (hbright : b * D.liftedCoordinate 1 = b)
    (hx2 : x ∉ (Ring.jacobson B) ^ 2)
    (ha2 : a ∉ (Ring.jacobson B) ^ 2)
    (hb2 : b ∉ (Ring.jacobson B) ^ 2)
    (e : OpConjecture.Tsukamoto.cyclicRightIdealFG (b * a) ≅
      OpConjecture.Tsukamoto.cyclicRightIdealFG x)
    (H : Ideal B) [H.IsTwoSided]
    (hH2 : H ≤ (Ring.jacobson B) ^ 2)
    (hnormal : b * a ∈ H →
      ∃ t s : B, s ∈ Ring.jacobson B ∧ b * a = x * t + (b * a) * s) :
    LinearIndependent K
      (fun i ↦ Ideal.Quotient.mk H (D.sixPeirceElements x a b i)) := by
  have hba2 : b * a ∈ (Ring.jacobson B) ^ 2 := by
    rw [show (2 : ℕ) = 1 + 1 by omega, Submodule.pow_succ,
      Submodule.pow_one]
    exact Ideal.mul_mem_mul hbJ haJ
  have hba : Ideal.Quotient.mk H (b * a) ≠ 0 :=
    quotient_mk_ne_zero_of_relation_normalForm
      (K := K) (A := B) H hba2 hx2 e hnormal
  exact D.six_quotientClasses_linearIndependent_of_peirceCotangent
    hxJ haJ hbJ hxleft hxright haleft haright hbleft hbright
      hx2 ha2 hb2 H hH2 hba

end TwoCoordinateData

end OpConjecture.QuotientSurvival
