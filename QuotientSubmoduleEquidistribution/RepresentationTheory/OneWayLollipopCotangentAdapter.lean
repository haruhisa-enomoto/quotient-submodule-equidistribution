import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopCoordinateRecognition
import QuotientSubmoduleEquidistribution.RepresentationTheory.PeirceCotangentExtDimension

/-!
# From one-way Ext support to lollipop cotangent data

This file selects the loop and cross-arrow representatives in the incoming
one-way-lollipop orientation and proves that they span `J/J²`.  Exact Peirce
cotangent--Ext dimensions turn the two absent support corners into zero
corners, while no-parallelness bounds the two occupied corners by one.

The resulting carrier recognition is conditional only on the separate
module-theoretic loop-square conclusion `x² = 0`.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData

open QuotientSubmoduleEquidistribution.CotangentExtBridge

universe u v

variable {K B : Type u}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]

private abbrev J (B : Type u) [Ring B] := Ring.jacobson B

variable (D : QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData
  (K := K) (B := B))

/-- Two representatives in the loop corner `(0,0)` and cross corner `(1,0)`
span `J/J²` as soon as the whole cotangent space has dimension at most two.
The localized Peirce functionals prove their independence. -/
theorem jacobsonCotangentSpannedBy_pair_of_finrank_le_two
    [FiniteDimensional K B]
    {x a : B}
    (hxJ : x ∈ J B) (haJ : a ∈ J B)
    (hxleft : D.liftedCoordinate 0 * x = x)
    (hxright : x * D.liftedCoordinate 0 = x)
    (haleft : D.liftedCoordinate 1 * a = a)
    (haright : a * D.liftedCoordinate 0 = a)
    (hx2 : x ∉ (J B) ^ 2)
    (ha2 : a ∉ (J B) ^ 2)
    (hdim : Module.finrank K
      (jacobsonCotangentSubmodule (K := K) (B := B)) ≤ 2) :
    JacobsonCotangentSpannedBy (K := K) x a 0 := by
  let J2K := jacobsonSquareSubmodule (K := K) (B := B)
  let Q := B ⧸ J2K
  let reps : Fin 2 → B := ![x, a]
  let v : Fin 2 → Q := fun i ↦ J2K.mkQ (reps i)
  let C : Submodule K Q :=
    ((J B : Submodule B B).restrictScalars K).map J2K.mkQ
  let S : Submodule K Q := Submodule.span K (Set.range v)

  have hvLI : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsumQ :
        J2K.mkQ (c 0 • x + c 1 • a) = 0 := by
      simpa [v, reps, Fin.sum_univ_two] using hc
    have hcomb2 : c 0 • x + c 1 • a ∈ (J B) ^ 2 := by
      have hmem := (Submodule.Quotient.mk_eq_zero J2K).mp hsumQ
      simpa [J2K, jacobsonSquareSubmodule] using hmem
    have hxEval :=
      D.normalizedPeirceCotangentFunctional_vanishes_square
        0 0 hx2 (c 0 • x + c 1 • a) hcomb2
    have hcx : c 0 = 0 := by
      simpa [
        D.normalizedPeirceCotangentFunctional_self 0 0
          hxJ hxleft hxright hx2,
        D.normalizedPeirceCotangentFunctional_eq_zero_of_corner_ne
          0 0 1 0 haleft haright hx2 (Or.inl (by decide))]
        using hxEval
    have haEval :=
      D.normalizedPeirceCotangentFunctional_vanishes_square
        1 0 ha2 (c 0 • x + c 1 • a) hcomb2
    have hca : c 1 = 0 := by
      simpa [
        D.normalizedPeirceCotangentFunctional_self 1 0
          haJ haleft haright ha2,
        D.normalizedPeirceCotangentFunctional_eq_zero_of_corner_ne
          1 0 0 0 hxleft hxright ha2 (Or.inl (by decide))]
        using haEval
    intro i
    fin_cases i
    · exact hcx
    · exact hca

  have hSC : S ≤ C := by
    apply Submodule.span_le.mpr
    rintro q ⟨i, rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨reps i, ?_, rfl⟩
    fin_cases i
    · simpa [reps] using hxJ
    · simpa [reps] using haJ
  have hSdim : Module.finrank K S = 2 := by
    simpa [S] using finrank_span_eq_card hvLI
  have hSCeq : S = C := by
    apply Submodule.eq_of_le_of_finrank_le hSC
    rw [hSdim]
    change Module.finrank K C ≤ 2 at hdim
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
  refine ⟨c 0, c 1, 0, ?_⟩
  have hmk : J2K.mkQ z = J2K.mkQ (c 0 • x + c 1 • a) := by
    simpa [v, reps, Fin.sum_univ_two] using hc.symm
  have hmemK : z - (c 0 • x + c 1 • a) ∈ J2K :=
    (Submodule.Quotient.eq J2K).mp hmk
  simpa [J2K, jacobsonSquareSubmodule] using hmemK

open QuotientSubmoduleEquidistribution.GabrielArrowBridge

variable {kappa : Type v}
  [Small.{u} Bᵐᵒᵖ] [IsNoetherianRing Bᵐᵒᵖ]
  [IsArtinianRing Bᵐᵒᵖ] [Finite kappa]
  (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ kappa)

omit [IsArtinianRing Bᵐᵒᵖ] [Finite kappa] in
/-- If an aligned Ext--Gabriel support pair is empty, the corresponding
aligned `Ext¹` space has dimension zero. -/
theorem alignedExt_finrank_eq_zero_of_noArrow
    (hNoParallel : NoParallelExtSupport (K := K) tau)
    {i j : Fin 2}
    (hNoArrow : ¬ (D.alignedExtTwoVertexSupport tau hNoParallel).HasArrow i j) :
    Module.finrank K
      (ExtOne tau
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau i)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau j)) = 0 := by
  let E :=
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
      D tau
  let s := E i
  let t := E j
  letI : FiniteDimensional K (ExtOne tau s t) := (hNoParallel s t).1
  by_contra hne
  have hpos : 0 < Module.finrank K (ExtOne tau s t) :=
    Nat.pos_of_ne_zero hne
  let arrow : ExtGabrielArrowIndex (K := K) tau :=
    ⟨s, t, ⟨0, hpos⟩⟩
  apply hNoArrow
  refine ⟨arrow, ?_, ?_⟩
  · change E.symm (ExtGabrielArrowIndex.source tau arrow) = i
    exact E.symm_apply_apply i
  · change E.symm (ExtGabrielArrowIndex.target tau arrow) = j
    exact E.symm_apply_apply j

omit [IsArtinianRing Bᵐᵒᵖ] [Finite kappa] in
/-- In the orientation with a loop at `0` and the sole cross arrow in the
corner `(1,0)`, one-way support bounds the global cotangent dimension by two.
-/
theorem cotangent_finrank_le_two_of_incoming_oneWayLollipop
    [FiniteDimensional K B]
    (hNoParallel : NoParallelExtSupport (K := K) tau)
    (hShape :
      (D.alignedExtTwoVertexSupport tau hNoParallel).IsOneWayLollipopAt 0 1)
    (hIncoming :
      ¬ (D.alignedExtTwoVertexSupport tau hNoParallel).HasArrow 0 1 ∧
        (D.alignedExtTwoVertexSupport tau hNoParallel).HasArrow 1 0) :
    Module.finrank K
      (jacobsonCotangentSubmodule (K := K) (B := B)) ≤ 2 := by
  have h00 : Module.finrank K
      (D.jacobsonCotangentCornerSubmodule 0 0) ≤ 1 := by
    rw [D.finrank_jacobsonCotangentCornerSubmodule_eq_alignedExt tau]
    exact (hNoParallel
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau 0)
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau 0)).2
  have h10 : Module.finrank K
      (D.jacobsonCotangentCornerSubmodule 1 0) ≤ 1 := by
    rw [D.finrank_jacobsonCotangentCornerSubmodule_eq_alignedExt tau]
    exact (hNoParallel
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau 1)
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau 0)).2
  have h01 : Module.finrank K
      (D.jacobsonCotangentCornerSubmodule 0 1) = 0 := by
    rw [D.finrank_jacobsonCotangentCornerSubmodule_eq_alignedExt tau]
    exact alignedExt_finrank_eq_zero_of_noArrow D tau hNoParallel hIncoming.1
  have h11 : Module.finrank K
      (D.jacobsonCotangentCornerSubmodule 1 1) = 0 := by
    rw [D.finrank_jacobsonCotangentCornerSubmodule_eq_alignedExt tau]
    exact alignedExt_finrank_eq_zero_of_noArrow D tau hNoParallel
      hShape.2.2.1
  have hglobal := D.finrank_jacobsonCotangentSubmodule_le_sum_corners
  omega

/-- The exact ring data supplied by an incoming one-way Ext--Gabriel
lollipop before the manuscript's separate loop-square argument. -/
structure OneWayLollipopCotangentData where
  x : B
  a : B
  x_mem_jacobson : x ∈ J B
  a_mem_jacobson : a ∈ J B
  x_left : D.liftedCoordinate 0 * x = x
  x_right : x * D.liftedCoordinate 0 = x
  a_left : D.liftedCoordinate 1 * a = a
  a_right : a * D.liftedCoordinate 0 = a
  x_not_square : x ∉ (J B) ^ 2
  a_not_square : a ∉ (J B) ^ 2
  cotangent_spanned :
    JacobsonCotangentSpannedBy (K := K) x a 0

namespace OneWayLollipopCotangentData

variable {D : QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData
  (K := K) (B := B)}

omit [Small.{u} Bᵐᵒᵖ] [IsNoetherianRing Bᵐᵒᵖ]
    [IsArtinianRing Bᵐᵒᵖ] in
/-- Adding the separately proved loop-square relation gives precisely the
normal-form data consumed by coordinate recognition. -/
theorem toLollipopRadicalData
    (C : OneWayLollipopCotangentData D)
    (hxsq : C.x * C.x = 0) : D.LollipopRadicalData C.x C.a where
  x_mem_jacobson := C.x_mem_jacobson
  a_mem_jacobson := C.a_mem_jacobson
  x_left := C.x_left
  x_right := C.x_right
  a_left := C.a_left
  a_right := C.a_right
  x_not_square := C.x_not_square
  a_not_square := C.a_not_square
  x_sq := hxsq
  cotangent_spanned := C.cotangent_spanned

omit [Small.{u} Bᵐᵒᵖ] [IsNoetherianRing Bᵐᵒᵖ]
    [IsArtinianRing Bᵐᵒᵖ] in
/-- Once `x²=0` is known, the abstract carrier is one of the two concrete
lollipop models according as the length-two path vanishes or survives. -/
theorem algEquiv_b0_or_b1
    (C : OneWayLollipopCotangentData D)
    (hxsq : C.x * C.x = 0) :
    Nonempty (QuotientSubmoduleEquidistribution.LollipopConcrete.B0Model K ≃ₐ[K] B) ∨
      Nonempty
        (QuotientSubmoduleEquidistribution.LollipopConcrete.B1.B1Model K ≃ₐ[K] B) := by
  let L := C.toLollipopRadicalData hxsq
  by_cases hpath : C.a * C.x = 0
  · exact Or.inl ⟨L.b0AlgEquiv hpath⟩
  · exact Or.inr ⟨L.b1AlgEquiv hpath⟩

end OneWayLollipopCotangentData

variable [IsAlgClosed K]

/-- Automatic selection and cotangent exhaustion for the incoming
one-way-lollipop orientation.  The only relation not supplied here is the
separate module-theoretic conclusion `x²=0`. -/
noncomputable def incomingOneWayLollipopCotangentData
    [FiniteDimensional K B]
    (hNoParallel : NoParallelExtSupport (K := K) tau)
    (hShape :
      (D.alignedExtTwoVertexSupport tau hNoParallel).IsOneWayLollipopAt 0 1)
    (hIncoming :
      ¬ (D.alignedExtTwoVertexSupport tau hNoParallel).HasArrow 0 1 ∧
        (D.alignedExtTwoVertexSupport tau hNoParallel).HasArrow 1 0) :
    OneWayLollipopCotangentData D := by
  let E :=
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
      D tau
  let R :=
    QuotientSubmoduleEquidistribution.CoordinateGabrielRealization.automaticExtArrowCotangentRepresentativeData
      D tau
  let loopArrow := hShape.2.1.choose
  have hLoopSpec := hShape.2.1.choose_spec
  let crossArrow := hIncoming.2.choose
  have hCrossSpec := hIncoming.2.choose_spec
  have hLoopSource := hLoopSpec.1
  have hLoopTarget := hLoopSpec.2
  have hCrossSource := hCrossSpec.1
  have hCrossTarget := hCrossSpec.2
  change E.symm (ExtGabrielArrowIndex.source tau loopArrow) = 0 at hLoopSource
  change E.symm (ExtGabrielArrowIndex.target tau loopArrow) = 0 at hLoopTarget
  change E.symm (ExtGabrielArrowIndex.source tau crossArrow) = 1 at hCrossSource
  change E.symm (ExtGabrielArrowIndex.target tau crossArrow) = 0 at hCrossTarget
  let x := R.representative loopArrow
  let a := R.representative crossArrow
  have hxL : D.liftedCoordinate 0 * x = x := by
    have h := R.representative_left_fixed loopArrow
    change D.liftedCoordinate
      (E.symm (ExtGabrielArrowIndex.source tau loopArrow)) * x = x at h
    rw [hLoopSource] at h
    exact h
  have hxR : x * D.liftedCoordinate 0 = x := by
    have h := R.representative_right_fixed loopArrow
    change x * D.liftedCoordinate
      (E.symm (ExtGabrielArrowIndex.target tau loopArrow)) = x at h
    rw [hLoopTarget] at h
    exact h
  have haL : D.liftedCoordinate 1 * a = a := by
    have h := R.representative_left_fixed crossArrow
    change D.liftedCoordinate
      (E.symm (ExtGabrielArrowIndex.source tau crossArrow)) * a = a at h
    rw [hCrossSource] at h
    exact h
  have haR : a * D.liftedCoordinate 0 = a := by
    have h := R.representative_right_fixed crossArrow
    change a * D.liftedCoordinate
      (E.symm (ExtGabrielArrowIndex.target tau crossArrow)) = a at h
    rw [hCrossTarget] at h
    exact h
  have hdim := D.cotangent_finrank_le_two_of_incoming_oneWayLollipop
    tau hNoParallel hShape hIncoming
  exact
    { x := x
      a := a
      x_mem_jacobson := R.representative_mem_jacobson loopArrow
      a_mem_jacobson := R.representative_mem_jacobson crossArrow
      x_left := hxL
      x_right := hxR
      a_left := haL
      a_right := haR
      x_not_square := R.representative_not_mem_square loopArrow
      a_not_square := R.representative_not_mem_square crossArrow
      cotangent_spanned :=
        D.jacobsonCotangentSpannedBy_pair_of_finrank_le_two
          (R.representative_mem_jacobson loopArrow)
          (R.representative_mem_jacobson crossArrow)
          hxL hxR haL haR
          (R.representative_not_mem_square loopArrow)
          (R.representative_not_mem_square crossArrow) hdim }

end QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData
