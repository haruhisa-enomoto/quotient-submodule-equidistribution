import QuotientSubmoduleEquidistribution.RepresentationTheory.CoordinateReindexSupport
import QuotientSubmoduleEquidistribution.RepresentationTheory.ExtDualTransport
import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulLevelDualityTransport
import QuotientSubmoduleEquidistribution.RepresentationTheory.RingelEtaCoreCardinality

noncomputable section

open MulOpposite

namespace QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData

universe u v

variable {K B : Type u} {I : Type v}
  [Field K] [Ring B] [Algebra K B]
  [IsArtinianRing B] [IsArtinianRing Bᵐᵒᵖ]
  [Fintype I] [DecidableEq I]

omit [IsArtinianRing B] in
theorem unop_mem_jacobson_of_mem_jacobson
    {x : Bᵐᵒᵖ} (hx : x ∈ Ring.jacobson Bᵐᵒᵖ) :
    unop x ∈ Ring.jacobson B := by
  rw [← Ideal.jacobson_bot]
  rw [Ideal.mem_jacobson_iff]
  intro y
  have hnilJ : IsNilpotent (Ring.jacobson Bᵐᵒᵖ) := by
    simpa only [Ideal.jacobson_bot] using
      (IsArtinianRing.isNilpotent_jacobson_bot (R := Bᵐᵒᵖ))
  obtain ⟨n, hn⟩ := hnilJ
  have hxyJ : x * op y ∈ Ring.jacobson Bᵐᵒᵖ :=
    (Ring.jacobson Bᵐᵒᵖ).mul_mem_right _ hx
  have hpowJ : (x * op y) ^ n ∈ (Ring.jacobson Bᵐᵒᵖ) ^ n :=
    Ideal.pow_mem_pow hxyJ n
  have hpowBase : (x * op y) ^ n = 0 := by
    rw [hn] at hpowJ
    simpa using hpowJ
  have hpow : (y * unop x) ^ n = 0 := by
    change unop ((x * op y) ^ n) = 0
    simpa using congrArg unop hpowBase
  have hnil : IsNilpotent (y * unop x) := ⟨n, hpow⟩
  let U : Bˣ := hnil.isUnit_add_one.unit
  refine ⟨↑U⁻¹, ?_⟩
  rw [Submodule.mem_bot]
  calc
    ↑U⁻¹ * y * unop x + ↑U⁻¹ - 1 =
        ↑U⁻¹ * (y * unop x + 1) - 1 := by
          simp [mul_add, mul_assoc]
    _ = ↑U⁻¹ * ↑U - 1 := by
          rw [hnil.isUnit_add_one.unit_spec]
    _ = 0 := by simp

variable (D : QuotientCoordinateData (K := K) (B := B) (I := I))

def oppositeCoordinateHom : Bᵐᵒᵖ →ₐ[K] (I → K) where
  toFun b := D.quotientEquiv
    (Ideal.Quotient.mk (Ring.jacobson B) (unop b))
  map_one' := by simp
  map_mul' b c := by
    simp only [unop_mul, map_mul]
    exact mul_comm _ _
  map_zero' := by simp
  map_add' b c := by simp
  commutes' k := by simp

omit [IsArtinianRing B] [IsArtinianRing Bᵐᵒᵖ]
    [Fintype I] [DecidableEq I] in
@[simp]
theorem oppositeCoordinateHom_apply (b : Bᵐᵒᵖ) :
    D.oppositeCoordinateHom b =
      D.quotientEquiv
        (Ideal.Quotient.mk (Ring.jacobson B) (unop b)) :=
  rfl

def oppositeQuotientCoordinateHom :
    (Bᵐᵒᵖ ⧸ Ring.jacobson Bᵐᵒᵖ) →ₐ[K] (I → K) :=
  Ideal.Quotient.liftₐ (Ring.jacobson Bᵐᵒᵖ)
    D.oppositeCoordinateHom (by
      intro b hb
      change D.quotientEquiv
        (Ideal.Quotient.mk (Ring.jacobson B) (unop b)) = 0
      simpa only [map_zero] using congrArg D.quotientEquiv
        (Ideal.Quotient.eq_zero_iff_mem.mpr
          (unop_mem_jacobson_of_mem_jacobson hb)))

omit [IsArtinianRing B] [Fintype I] [DecidableEq I] in
@[simp]
theorem oppositeQuotientCoordinateHom_mk (b : Bᵐᵒᵖ) :
    D.oppositeQuotientCoordinateHom
        (Ideal.Quotient.mk (Ring.jacobson Bᵐᵒᵖ) b) =
      D.quotientEquiv
        (Ideal.Quotient.mk (Ring.jacobson B) (unop b)) := by
  rfl

omit [IsArtinianRing B] [Fintype I] [DecidableEq I] in
theorem oppositeQuotientCoordinateHom_surjective :
    Function.Surjective D.oppositeQuotientCoordinateHom := by
  intro f
  obtain ⟨q, rfl⟩ := D.quotientEquiv.surjective f
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨Ideal.Quotient.mk (Ring.jacobson Bᵐᵒᵖ) (op b), by simp⟩

omit [Fintype I] [DecidableEq I] in
theorem oppositeQuotientCoordinateHom_injective :
    Function.Injective D.oppositeQuotientCoordinateHom := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [oppositeQuotientCoordinateHom_mk] at hq
  have hb : unop b ∈ Ring.jacobson B := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact D.quotientEquiv.injective (by simpa using hq)
  rw [Ideal.Quotient.eq_zero_iff_mem]
  simpa using
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.op_mem_jacobson_of_mem_jacobson
      (B := B) hb

def oppositeQuotientEquiv :
    (Bᵐᵒᵖ ⧸ Ring.jacobson Bᵐᵒᵖ) ≃ₐ[K] (I → K) :=
  AlgEquiv.ofBijective D.oppositeQuotientCoordinateHom
    ⟨D.oppositeQuotientCoordinateHom_injective,
      D.oppositeQuotientCoordinateHom_surjective⟩

def op : QuotientCoordinateData (K := K) (B := Bᵐᵒᵖ) (I := I) where
  quotientEquiv := D.oppositeQuotientEquiv

omit [Fintype I] [DecidableEq I] in
@[simp]
theorem coordinateCharacter_op (i : I) (b : Bᵐᵒᵖ) :
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateCharacter
        D.op i b =
      QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateCharacter
        D i (unop b) := by
  rfl

omit [Fintype I] [DecidableEq I] in
@[simp]
theorem coordinateCharacterOp_op (i : I) (b : (Bᵐᵒᵖ)ᵐᵒᵖ) :
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateCharacterOp
        D.op i b =
      QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateCharacter
        D i (unop (unop b)) := by
  rfl

end QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData

namespace QuotientSubmoduleEquidistribution.OppositeCoordinateSupport

open CategoryTheory
open QuotientSubmoduleEquidistribution.GabrielArrowBridge

universe u v

variable {K B : Type u}
  [Field K] [IsAlgClosed K]
  [Ring B] [Algebra K B] [FiniteDimensional K B]
  [Small.{u} Bᵐᵒᵖ] [IsNoetherianRing Bᵐᵒᵖ]
  [IsArtinianRing B] [IsArtinianRing Bᵐᵒᵖ]
  [Small.{u} (Bᵐᵒᵖ)ᵐᵒᵖ] [IsNoetherianRing (Bᵐᵒᵖ)ᵐᵒᵖ]
  [IsArtinianRing (Bᵐᵒᵖ)ᵐᵒᵖ]
  [IsNoetherianRing ((Bᵐᵒᵖ)ᵐᵒᵖ)ᵐᵒᵖ]
  {kappa lambda : Type v}
  [Finite kappa] [Finite lambda]
  (sigma : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ kappa)
  (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} (Bᵐᵒᵖ)ᵐᵒᵖ lambda)
  (A : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedAntiEquivalence sigma tau)
  (D : QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData (K := K) (B := B))

/-- The coordinate permutation which labels the opposite coordinate simples
by the contragredient images of the original coordinate simples. -/
def dualCoordinatePermutation : Fin 2 ≃ Fin 2 :=
  (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
      D sigma).trans
    ((QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.simpleIndexEquiv
        sigma tau A).trans
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D.op tau).symm)

/-- Opposite quotient coordinates reindexed to preserve the original
coordinate names under contragredient duality. -/
def alignedOppositeCoordinateData :
    QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData
      (K := K) (B := Bᵐᵒᵖ) :=
  D.op.reindex (dualCoordinatePermutation sigma tau A D).symm

omit [IsAlgClosed K] [FiniteDimensional K B]
    [Small.{u} Bᵐᵒᵖ] [Small.{u} (Bᵐᵒᵖ)ᵐᵒᵖ]
    [IsArtinianRing (Bᵐᵒᵖ)ᵐᵒᵖ]
    [IsNoetherianRing ((Bᵐᵒᵖ)ᵐᵒᵖ)ᵐᵒᵖ]
    [Finite kappa] [Finite lambda] in
theorem coordinateSimpleIndexEquiv_alignedOpposite :
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        (alignedOppositeCoordinateData sigma tau A D) tau =
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D sigma).trans
        (QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.simpleIndexEquiv
          sigma tau A) := by
  dsimp only [alignedOppositeCoordinateData]
  rw [QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData.coordinateSimpleIndexEquiv_reindex]
  apply Equiv.ext
  intro i
  simp [dualCoordinatePermutation]

variable
  (hSigma : NoParallelExtSupport (K := K) sigma)
  (hTau : NoParallelExtSupport (K := K) tau)

/-- Contragredient duality bijects multiplicity-bearing Ext arrows. -/
def extArrowDualEquiv :
    ExtGabrielArrowIndex (K := K) sigma ≃
      ExtGabrielArrowIndex (K := K) tau :=
  (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.lengthTwoEquivExtGabrielArrow
      sigma hSigma).symm |>.trans
    ((QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.lengthTwoEquiv
      sigma tau A).trans
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.lengthTwoEquivExtGabrielArrow
        tau hTau))

omit [IsAlgClosed K] [FiniteDimensional K B] [IsArtinianRing B]
    [IsNoetherianRing ((Bᵐᵒᵖ)ᵐᵒᵖ)ᵐᵒᵖ]
    [Finite kappa] [Finite lambda] in
theorem source_extArrowDualEquiv
    (a : ExtGabrielArrowIndex (K := K) sigma) :
    ExtGabrielArrowIndex.source tau
        (extArrowDualEquiv sigma tau A hSigma hTau a) =
      QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.simpleIndexEquiv
        sigma tau A (ExtGabrielArrowIndex.target sigma a) := by
  let eSigma :=
    QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.lengthTwoEquivExtGabrielArrow
      sigma hSigma
  let eTau :=
    QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.lengthTwoEquivExtGabrielArrow
      tau hTau
  change ExtGabrielArrowIndex.source tau
      (eTau
        (QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.lengthTwoEquiv
          sigma tau A (eSigma.symm a))) = _
  rw [QuotientSubmoduleEquidistribution.ExtDualTransport.LengthTwo.source_lengthTwoEquivExtGabrielArrow]
  rw [QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.source_lengthTwoEquiv]
  apply congrArg
    (QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.simpleIndexEquiv
      sigma tau A)
  calc
    QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target sigma (eSigma.symm a) =
        ExtGabrielArrowIndex.target sigma (eSigma (eSigma.symm a)) :=
      (QuotientSubmoduleEquidistribution.ExtDualTransport.LengthTwo.target_lengthTwoEquivExtGabrielArrow
        (K := K) sigma hSigma (eSigma.symm a)).symm
    _ = ExtGabrielArrowIndex.target sigma a := by rw [eSigma.apply_symm_apply]

omit [IsAlgClosed K] [FiniteDimensional K B] [IsArtinianRing B]
    [IsNoetherianRing ((Bᵐᵒᵖ)ᵐᵒᵖ)ᵐᵒᵖ]
    [Finite kappa] [Finite lambda] in
theorem target_extArrowDualEquiv
    (a : ExtGabrielArrowIndex (K := K) sigma) :
    ExtGabrielArrowIndex.target tau
        (extArrowDualEquiv sigma tau A hSigma hTau a) =
      QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.simpleIndexEquiv
        sigma tau A (ExtGabrielArrowIndex.source sigma a) := by
  let eSigma :=
    QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.lengthTwoEquivExtGabrielArrow
      sigma hSigma
  let eTau :=
    QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.lengthTwoEquivExtGabrielArrow
      tau hTau
  change ExtGabrielArrowIndex.target tau
      (eTau
        (QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.lengthTwoEquiv
          sigma tau A (eSigma.symm a))) = _
  rw [QuotientSubmoduleEquidistribution.ExtDualTransport.LengthTwo.target_lengthTwoEquivExtGabrielArrow]
  rw [QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.target_lengthTwoEquiv]
  apply congrArg
    (QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.simpleIndexEquiv
      sigma tau A)
  calc
    QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source sigma (eSigma.symm a) =
        ExtGabrielArrowIndex.source sigma (eSigma (eSigma.symm a)) :=
      (QuotientSubmoduleEquidistribution.ExtDualTransport.LengthTwo.source_lengthTwoEquivExtGabrielArrow
        (K := K) sigma hSigma (eSigma.symm a)).symm
    _ = ExtGabrielArrowIndex.source sigma a := by rw [eSigma.apply_symm_apply]

omit [IsAlgClosed K] [FiniteDimensional K B]
    [IsNoetherianRing ((Bᵐᵒᵖ)ᵐᵒᵖ)ᵐᵒᵖ]
    [Finite kappa] [Finite lambda] in
private theorem alignedOpposite_source_extArrowDualEquiv
    (a : ExtGabrielArrowIndex (K := K) sigma) :
    (QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData.alignedExtTwoVertexSupport
        (alignedOppositeCoordinateData sigma tau A D) tau hTau).source
        (extArrowDualEquiv sigma tau A hSigma hTau a) =
      (D.alignedExtTwoVertexSupport sigma hSigma).target a := by
  change
    (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        (alignedOppositeCoordinateData sigma tau A D) tau).symm
      (ExtGabrielArrowIndex.source tau
        (extArrowDualEquiv sigma tau A hSigma hTau a)) =
    (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D sigma).symm (ExtGabrielArrowIndex.target sigma a)
  rw [source_extArrowDualEquiv]
  rw [coordinateSimpleIndexEquiv_alignedOpposite]
  simp

omit [IsAlgClosed K] [FiniteDimensional K B]
    [IsNoetherianRing ((Bᵐᵒᵖ)ᵐᵒᵖ)ᵐᵒᵖ]
    [Finite kappa] [Finite lambda] in
private theorem alignedOpposite_target_extArrowDualEquiv
    (a : ExtGabrielArrowIndex (K := K) sigma) :
    (QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData.alignedExtTwoVertexSupport
        (alignedOppositeCoordinateData sigma tau A D) tau hTau).target
        (extArrowDualEquiv sigma tau A hSigma hTau a) =
      (D.alignedExtTwoVertexSupport sigma hSigma).source a := by
  change
    (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        (alignedOppositeCoordinateData sigma tau A D) tau).symm
      (ExtGabrielArrowIndex.target tau
        (extArrowDualEquiv sigma tau A hSigma hTau a)) =
    (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D sigma).symm (ExtGabrielArrowIndex.source sigma a)
  rw [target_extArrowDualEquiv]
  rw [coordinateSimpleIndexEquiv_alignedOpposite]
  simp

omit [IsAlgClosed K] [FiniteDimensional K B]
    [IsNoetherianRing ((Bᵐᵒᵖ)ᵐᵒᵖ)ᵐᵒᵖ]
    [Finite kappa] [Finite lambda] in
/-- With coordinates aligned by simple duality, the opposite Ext support is
exactly the arrow-reversal of the original support. -/
theorem alignedOpposite_hasArrow_iff (i j : Fin 2) :
    (QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData.alignedExtTwoVertexSupport
        (alignedOppositeCoordinateData sigma tau A D) tau hTau).HasArrow j i ↔
      (D.alignedExtTwoVertexSupport sigma hSigma).HasArrow i j := by
  let e := extArrowDualEquiv sigma tau A hSigma hTau
  constructor
  · rintro ⟨b, hbSource, hbTarget⟩
    let a := e.symm b
    refine ⟨a, ?_, ?_⟩
    · have h := alignedOpposite_target_extArrowDualEquiv
        sigma tau A D hSigma hTau a
      rw [e.apply_symm_apply] at h
      exact h.symm.trans hbTarget
    · have h := alignedOpposite_source_extArrowDualEquiv
        sigma tau A D hSigma hTau a
      rw [e.apply_symm_apply] at h
      exact h.symm.trans hbSource
  · rintro ⟨a, haSource, haTarget⟩
    refine ⟨e a, ?_, ?_⟩
    · exact (alignedOpposite_source_extArrowDualEquiv
        sigma tau A D hSigma hTau a).trans haTarget
    · exact (alignedOpposite_target_extArrowDualEquiv
        sigma tau A D hSigma hTau a).trans haSource

omit [IsAlgClosed K] [FiniteDimensional K B]
    [IsNoetherianRing ((Bᵐᵒᵖ)ᵐᵒᵖ)ᵐᵒᵖ]
    [Finite kappa] [Finite lambda] in
/-- A normalized outgoing lollipop becomes a normalized incoming lollipop
on the aligned opposite coordinates. -/
theorem alignedOpposite_incoming_of_outgoing
    (hShape :
      (D.alignedExtTwoVertexSupport sigma hSigma).IsOneWayLollipopAt 0 1)
    (hOutgoing :
      (D.alignedExtTwoVertexSupport sigma hSigma).HasArrow 0 1 ∧
        ¬ (D.alignedExtTwoVertexSupport sigma hSigma).HasArrow 1 0) :
    let SOp :=
      QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData.alignedExtTwoVertexSupport
        (alignedOppositeCoordinateData sigma tau A D) tau hTau
    SOp.IsOneWayLollipopAt 0 1 ∧
      ¬ SOp.HasArrow 0 1 ∧ SOp.HasArrow 1 0 := by
  let S := D.alignedExtTwoVertexSupport sigma hSigma
  let SOp :=
    QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData.alignedExtTwoVertexSupport
      (alignedOppositeCoordinateData sigma tau A D) tau hTau
  have hArrow01 : SOp.HasArrow 1 0 :=
    (alignedOpposite_hasArrow_iff sigma tau A D hSigma hTau 0 1).2
      hOutgoing.1
  have hNoArrow10 : ¬ SOp.HasArrow 0 1 := fun h ↦
    hOutgoing.2
      ((alignedOpposite_hasArrow_iff sigma tau A D hSigma hTau 1 0).1 h)
  have hLoop0 : SOp.HasLoopAt 0 :=
    (alignedOpposite_hasArrow_iff sigma tau A D hSigma hTau 0 0).2
      hShape.2.1
  have hNoLoop1 : ¬ SOp.HasLoopAt 1 := fun h ↦
    hShape.2.2.1
      ((alignedOpposite_hasArrow_iff sigma tau A D hSigma hTau 1 1).1 h)
  exact ⟨⟨hShape.1, hLoop0, hNoLoop1, Or.inr ⟨hNoArrow10, hArrow01⟩⟩,
    hNoArrow10, hArrow01⟩

omit [IsAlgClosed K] [Finite kappa] in
/-- The outgoing lollipop orientation is recognized over the opposite
algebra by dualizing the skeleton and aligning the opposite coordinates. -/
theorem algEquiv_b0_or_b1_of_outgoingOneWayLollipop
    (BD : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedBiduality sigma tau)
    (hTau : NoParallelExtSupport (K := K) tau)
    (hShape :
      (D.alignedExtTwoVertexSupport sigma hSigma).IsOneWayLollipopAt 0 1)
    (hOutgoing :
      (D.alignedExtTwoVertexSupport sigma hSigma).HasArrow 0 1 ∧
        ¬ (D.alignedExtTwoVertexSupport sigma hSigma).HasArrow 1 0)
    (hRingel :
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.RingelCoreCardinality
        sigma)
    (hRank :
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.projectiveRank
        sigma = 2)
    (hCore :
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.quotientCore sigma :
        Set kappa).ncard = 3) :
    Nonempty (QuotientSubmoduleEquidistribution.LollipopConcrete.B0Model K ≃ₐ[K] Bᵐᵒᵖ) ∨
      Nonempty (QuotientSubmoduleEquidistribution.LollipopConcrete.B1.B1Model K ≃ₐ[K] Bᵐᵒᵖ) := by
  have hIncoming := alignedOpposite_incoming_of_outgoing
    sigma tau BD.forward D hSigma hTau hShape hOutgoing
  have hTwoSigma : Nat.card sigma.SimpleIndex = 2 :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank.ncard_projectiveLabels_eq_natCard_simpleIndex
      sigma).symm.trans hRank
  have hTwoTau : Nat.card tau.SimpleIndex = 2 := by
    calc
      Nat.card tau.SimpleIndex = Nat.card sigma.SimpleIndex :=
        Nat.card_congr
          (QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.simpleIndexEquiv
            sigma tau BD.forward).symm
      _ = 2 := hTwoSigma
  have hRankTau :
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.projectiveRank
        tau = 2 :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank.ncard_projectiveLabels_eq_natCard_simpleIndex
      tau).trans hTwoTau
  have hCoreTau :
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.quotientCore tau :
        Set lambda).ncard = 3 := by
    calc
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.quotientCore tau :
          Set lambda).ncard =
          (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.submoduleCore sigma :
            Set kappa).ncard :=
        (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedBiduality.submoduleCore_ncard_eq_quotientCore
          sigma tau BD).symm
      _ =
          (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.quotientCore sigma :
            Set kappa).ncard := hRingel.symm
      _ = 3 := hCore
  have hRingelTau :
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.RingelCoreCardinality
        tau :=
    QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
      tau K
  exact
    QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData.algEquiv_b0_or_b1_of_incomingOneWayLollipop
      (K := K) (B := Bᵐᵒᵖ) (kappa := lambda)
      (alignedOppositeCoordinateData sigma tau BD.forward D) tau hTau
      hIncoming.1 hIncoming.2 hRingelTau hRankTau hCoreTau

omit [IsAlgClosed K] in
/-- Every one-way lollipop is recognized by a dead/live model either on the
original algebra or on its opposite. -/
theorem algEquiv_b0_or_b1_direct_or_opposite_of_oneWayLollipop
    (BD : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedBiduality sigma tau)
    (hTau : NoParallelExtSupport (K := K) tau)
    {i j : Fin 2}
    (hShape :
      (D.alignedExtTwoVertexSupport sigma hSigma).IsOneWayLollipopAt i j)
    (hRingel :
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.RingelCoreCardinality
        sigma)
    (hRank :
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.projectiveRank
        sigma = 2)
    (hCore :
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.quotientCore sigma :
        Set kappa).ncard = 3) :
    ((Nonempty (QuotientSubmoduleEquidistribution.LollipopConcrete.B0Model K ≃ₐ[K] B) ∨
        Nonempty (QuotientSubmoduleEquidistribution.LollipopConcrete.B1.B1Model K ≃ₐ[K] B)) ∨
      (Nonempty (QuotientSubmoduleEquidistribution.LollipopConcrete.B0Model K ≃ₐ[K] Bᵐᵒᵖ) ∨
        Nonempty (QuotientSubmoduleEquidistribution.LollipopConcrete.B1.B1Model K ≃ₐ[K] Bᵐᵒᵖ))) := by
  rcases
      QuotientSubmoduleEquidistribution.QuotientSurvival.TwoCoordinateData.algEquiv_b0_or_b1_or_normalizedOutgoing_of_oneWayLollipop
        (K := K) (B := B) (kappa := kappa)
        D sigma hSigma hShape hRingel hRank hCore with
    hDirect | ⟨D', hShape', hOutgoing⟩
  · exact Or.inl hDirect
  · exact Or.inr
      (algEquiv_b0_or_b1_of_outgoingOneWayLollipop
        sigma tau D' hSigma BD hTau
        hShape' hOutgoing hRingel hRank hCore)

end QuotientSubmoduleEquidistribution.OppositeCoordinateSupport
