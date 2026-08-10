import OpConjecture.RepresentationTheory.PeirceRadicalNormalForm
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Cotangent spanning adapters

This file uses no concrete bound algebra and no module classification.  It
isolates the exact linear-algebra seam between the maintained Peirce/Ext
support package and the radical normal-form theorem.
-/

noncomputable section

namespace OpConjecture.QuotientSurvival

universe u

variable {K B : Type u}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]

private abbrev J (B : Type u) [Ring B] := Ring.jacobson B

/-- `J^2`, regarded only as a `K`-subspace of the algebra. -/
def jacobsonSquareSubmodule : Submodule K B :=
  ((J B) ^ 2 : Submodule B B).restrictScalars K

/-- The image of `J` inside the ambient quotient `B/J^2`.  This is a
definitionally convenient model of the cotangent space `J/J^2`. -/
def jacobsonCotangentSubmodule :
    Submodule K (B ⧸ jacobsonSquareSubmodule (K := K) (B := B)) :=
  ((J B : Submodule B B).restrictScalars K).map
    (jacobsonSquareSubmodule (K := K) (B := B)).mkQ

namespace TwoCoordinateData

variable (D : TwoCoordinateData (K := K) (B := B))

/-- The exact residual premise behind cotangent exhaustion: the three
Peirce-localized functionals jointly detect every radical class modulo
`J^2`.  The reverse inclusion is already proved by the detector package. -/
def DegreeOneDetectorExactOnJacobson
    {x a b : B}
    (hx2 : x ∉ (J B) ^ 2)
    (ha2 : a ∉ (J B) ^ 2)
    (hb2 : b ∉ (J B) ^ 2) : Prop :=
  ∀ z : B, z ∈ J B →
    D.degreeOneDetector hx2 ha2 hb2 z = 0 → z ∈ (J B) ^ 2

/-- Exactness of the three maintained Peirce detectors immediately supplies
the cotangent-spanning premise consumed by `PeirceRadicalNormalForm`. -/
theorem jacobsonCotangentSpannedBy_of_degreeOneDetectorExact
    {x a b : B}
    (hxJ : x ∈ J B) (haJ : a ∈ J B) (hbJ : b ∈ J B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hbleft : D.liftedCoordinate 0 * b = b)
    (hbright : b * D.liftedCoordinate 1 = b)
    (hx2 : x ∉ (J B) ^ 2)
    (ha2 : a ∉ (J B) ^ 2)
    (hb2 : b ∉ (J B) ^ 2)
    (hexact : D.DegreeOneDetectorExactOnJacobson hx2 ha2 hb2) :
    JacobsonCotangentSpannedBy (K := K) x a b := by
  intro z hz
  let L := D.degreeOneDetector hx2 ha2 hb2
  let cx : K := L z 0
  let ca : K := L z 1
  let cb : K := L z 2
  refine ⟨cx, ca, cb, hexact _ ?_ ?_⟩
  · apply (J B).sub_mem hz
    have hcxJ : cx • x ∈ J B :=
      ((J B : Submodule B B).restrictScalars K).smul_mem cx hxJ
    have hcaJ : ca • a ∈ J B :=
      ((J B : Submodule B B).restrictScalars K).smul_mem ca haJ
    have hcbJ : cb • b ∈ J B :=
      ((J B : Submodule B B).restrictScalars K).smul_mem cb hbJ
    exact (J B).add_mem ((J B).add_mem hcxJ hcaJ) hcbJ
  · have hone := D.degreeOneDetector_sixPeirceElements
      hxJ haJ hbJ hxleft hxright haleft haright hbleft hbright
      hx2 ha2 hb2
    have hxL : L x = Pi.single 0 1 := by
      simpa [L, TwoCoordinateData.sixPeirceElements,
        radicalCoordinateVector] using hone .x
    have haL : L a = Pi.single 1 1 := by
      simpa [L, TwoCoordinateData.sixPeirceElements,
        radicalCoordinateVector] using hone .a
    have hbL : L b = Pi.single 2 1 := by
      simpa [L, TwoCoordinateData.sixPeirceElements,
        radicalCoordinateVector] using hone .b
    apply funext
    intro i
    fin_cases i <;>
      simp [L, cx, ca, cb, hxL, haL, hbL]

/-- The numerical cotangent hypothesis needed by the loop--two-cycle
branch.  The model is literally the image of `J` in `B/J^2`. -/
def CotangentDimensionAtMostThree [FiniteDimensional K B] : Prop :=
  Module.finrank K
    (jacobsonCotangentSubmodule (K := K) (B := B)) ≤ 3

/-- Three nonzero representatives in the distinct Peirce corners
`(0,0)`, `(1,0)`, `(0,1)` span `J/J^2` as soon as its dimension is at most
three.  Thus the single missing dimension bound supplies the exact spanning
premise of the quotient-survival proof. -/
theorem jacobsonCotangentSpannedBy_of_finrank_le_three
    [FiniteDimensional K B]
    {x a b : B}
    (hxJ : x ∈ J B) (haJ : a ∈ J B) (hbJ : b ∈ J B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hbleft : D.liftedCoordinate 0 * b = b)
    (hbright : b * D.liftedCoordinate 1 = b)
    (hx2 : x ∉ (J B) ^ 2)
    (ha2 : a ∉ (J B) ^ 2)
    (hb2 : b ∉ (J B) ^ 2)
    (hdim : CotangentDimensionAtMostThree (K := K) (B := B)) :
    JacobsonCotangentSpannedBy (K := K) x a b := by
  let J2K := jacobsonSquareSubmodule (K := K) (B := B)
  let Q := B ⧸ J2K
  let reps : Fin 3 → B := ![x, a, b]
  let v : Fin 3 → Q := fun i ↦ J2K.mkQ (reps i)
  let C : Submodule K Q :=
    ((J B : Submodule B B).restrictScalars K).map J2K.mkQ
  let S : Submodule K Q := Submodule.span K (Set.range v)

  have hdetSquare : J2K ≤ LinearMap.ker
      (D.degreeOneDetector hx2 ha2 hb2) := by
    intro z hz
    rw [LinearMap.mem_ker]
    have hz2 : z ∈ (J B) ^ 2 := by
      simpa [J2K, jacobsonSquareSubmodule] using hz
    apply funext
    intro i
    fin_cases i
    · exact D.normalizedPeirceCotangentFunctional_vanishes_square
        0 0 hx2 z hz2
    · exact D.normalizedPeirceCotangentFunctional_vanishes_square
        1 0 ha2 z hz2
    · exact D.normalizedPeirceCotangentFunctional_vanishes_square
        0 1 hb2 z hz2
  let detectorQ : Q →ₗ[K] (Fin 3 → K) :=
    J2K.liftQ (D.degreeOneDetector hx2 ha2 hb2) hdetSquare

  have hone := D.degreeOneDetector_sixPeirceElements
    hxJ haJ hbJ hxleft hxright haleft haright hbleft hbright
    hx2 ha2 hb2
  have hxL : D.degreeOneDetector hx2 ha2 hb2 x = Pi.single 0 1 := by
    simpa [TwoCoordinateData.sixPeirceElements,
      radicalCoordinateVector] using hone .x
  have haL : D.degreeOneDetector hx2 ha2 hb2 a = Pi.single 1 1 := by
    simpa [TwoCoordinateData.sixPeirceElements,
      radicalCoordinateVector] using hone .a
  have hbL : D.degreeOneDetector hx2 ha2 hb2 b = Pi.single 2 1 := by
    simpa [TwoCoordinateData.sixPeirceElements,
      radicalCoordinateVector] using hone .b
  have hdetectorQ_mk (z : B) :
      detectorQ (J2K.mkQ z) =
        D.degreeOneDetector hx2 ha2 hb2 z := by
    rfl

  have hvLI : LinearIndependent K v := by
    apply LinearIndependent.of_comp detectorQ
    have hcomp : detectorQ ∘ v = fun i : Fin 3 ↦ Pi.single i 1 := by
      funext i
      fin_cases i
      · change detectorQ (J2K.mkQ x) = Pi.single 0 1
        exact (hdetectorQ_mk x).trans hxL
      · change detectorQ (J2K.mkQ a) = Pi.single 1 1
        exact (hdetectorQ_mk a).trans haL
      · change detectorQ (J2K.mkQ b) = Pi.single 2 1
        exact (hdetectorQ_mk b).trans hbL
    rw [hcomp]
    have hbasisEq :
        (fun i : Fin 3 ↦ Pi.single i (1 : K)) =
          (Pi.basisFun K (Fin 3) : Fin 3 → (Fin 3 → K)) := by
      funext i
      exact (Pi.basisFun_apply K (Fin 3) i).symm
    rw [hbasisEq]
    exact (Pi.basisFun K (Fin 3)).linearIndependent

  have hSC : S ≤ C := by
    apply Submodule.span_le.mpr
    rintro q ⟨i, rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨reps i, ?_, rfl⟩
    fin_cases i
    · simpa [reps] using hxJ
    · simpa [reps] using haJ
    · simpa [reps] using hbJ

  have hSdim : Module.finrank K S = 3 := by
    simpa [S] using finrank_span_eq_card hvLI
  have hSCeq : S = C := by
    apply Submodule.eq_of_le_of_finrank_le hSC
    rw [hSdim]
    change Module.finrank K C ≤ 3 at hdim
    exact hdim

  intro z hz
  have hzC : J2K.mkQ z ∈ C := by
    apply Submodule.mem_map.mpr
    exact ⟨z, by simpa using hz, rfl⟩
  have hzS : J2K.mkQ z ∈ S := by
    rw [hSCeq]
    exact hzC
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun K).mp hzS
  refine ⟨c 0, c 1, c 2, ?_⟩
  have hmk : J2K.mkQ z =
      J2K.mkQ (c 0 • x + c 1 • a + c 2 • b) := by
    simpa [v, reps, Fin.sum_univ_succ, add_assoc] using hc.symm
  have hmemK : z - (c 0 • x + c 1 • a + c 2 • b) ∈ J2K :=
    (Submodule.Quotient.eq J2K).mp hmk
  simpa [J2K, jacobsonSquareSubmodule] using hmemK

/-- Direct paper-facing endpoint: the single cotangent-dimension bound
removes the spanning/survival premise from the six-class quotient argument. -/
theorem six_relationQuotientClasses_linearIndependent_of_finrank_le_three
    [FiniteDimensional K B]
    {x a b : B}
    (hxJ : x ∈ J B) (haJ : a ∈ J B) (hbJ : b ∈ J B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hbleft : D.liftedCoordinate 0 * b = b)
    (hbright : b * D.liftedCoordinate 1 = b)
    (hx2 : x ∉ (J B) ^ 2)
    (ha2 : a ∉ (J B) ^ 2)
    (hb2 : b ∉ (J B) ^ 2)
    (hcyclic : OpConjecture.Tsukamoto.cyclicRightIdealFG (b * a) ≅
      OpConjecture.Tsukamoto.cyclicRightIdealFG x)
    (hdim : CotangentDimensionAtMostThree (K := K) (B := B)) :
    LinearIndependent K
      (fun i ↦ Ideal.Quotient.mk (loopTwoCycleRelationIdeal x a b)
        (D.sixPeirceElements x a b i)) := by
  apply D.six_relationQuotientClasses_linearIndependent_of_cotangentSpanned
    hxJ haJ hbJ hxleft hxright haleft haright hbleft hbright
      hx2 ha2 hb2 hcyclic
  exact D.jacobsonCotangentSpannedBy_of_finrank_le_three
    hxJ haJ hbJ hxleft hxright haleft haright hbleft hbright
      hx2 ha2 hb2 hdim

end TwoCoordinateData

end OpConjecture.QuotientSurvival
