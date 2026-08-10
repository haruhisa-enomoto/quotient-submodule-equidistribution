import OpConjecture.RepresentationTheory.LollipopModelMoritaTransport
import OpConjecture.RepresentationTheory.LoopFreeBasicizedProfile
import OpConjecture.RepresentationTheory.LoopTwoCycleExclusion
import OpConjecture.RepresentationTheory.OppositeCoordinateSupport

noncomputable section

open CategoryTheory Set

namespace OpConjecture.BottomLevels.FiniteDimensionalRecurrence

universe u v

open OpConjecture.GabrielArrowBridge
open OpConjecture.IndecomposableSkeleton.FaithfulCore
open OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore
open OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank
open OpConjecture.LollipopConcrete.ModelTransport
open OpConjecture.MoritaBasicizationInterface

variable {K : Type u} [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in
/-- Coordinate reindexing carries a loop--two-cycle support to the renamed
vertices. -/
theorem isLoopTwoCycleAt_reindex
    {B0 : Type u} [Ring B0] [Algebra K B0] [IsArtinianRing B0]
    {kappa : Type v} [IsNoetherianRing B0ᵐᵒᵖ]
    (D : OpConjecture.QuotientSurvival.TwoCoordinateData
      (K := K) (B := B0))
    (tau : OpConjecture.IndecomposableSkeleton.{u, v, u}
      B0ᵐᵒᵖ kappa)
    (hNoParallel : NoParallelExtSupport (K := K) tau)
    (p : Fin 2 ≃ Fin 2)
    {i j : Fin 2}
    (hShape :
      (OpConjecture.QuotientSurvival.TwoCoordinateData.alignedExtTwoVertexSupport
        D tau hNoParallel).IsLoopTwoCycleAt i j) :
    (OpConjecture.QuotientSurvival.TwoCoordinateData.alignedExtTwoVertexSupport
      (D.reindex p) tau hNoParallel).IsLoopTwoCycleAt (p i) (p j) := by
  refine ⟨fun h ↦ hShape.1 (p.injective h), ?_, ?_, ?_, ?_⟩
  · exact
      (OpConjecture.QuotientSurvival.TwoCoordinateData.hasLoopAt_reindex_iff
        D tau hNoParallel p i).2 hShape.2.1
  · intro h
    exact hShape.2.2.1
      ((OpConjecture.QuotientSurvival.TwoCoordinateData.hasLoopAt_reindex_iff
        D tau hNoParallel p j).1 h)
  · exact
      (OpConjecture.QuotientSurvival.TwoCoordinateData.hasArrow_reindex_iff
        D tau hNoParallel p i j).2 hShape.2.2.2.1
  · exact
      (OpConjecture.QuotientSurvival.TwoCoordinateData.hasArrow_reindex_iff
        D tau hNoParallel p j i).2 hShape.2.2.2.2

omit [IsAlgClosed K] in
/-- Faithful level equality transports along a Morita equivalence of algebra
nodes. -/
theorem faithfulLevelCount_eq_of_morita
    (B C : AlgebraNode K)
    (m : MoritaEquivalence K B.Carrier C.Carrier)
    (n : ℕ)
    (hC : AlgebraNode.faithfulQCount K C n =
      AlgebraNode.faithfulSCount K C n) :
    AlgebraNode.faithfulQCount K B n =
      AlgebraNode.faithfulSCount K B n := by
  letI : IsArtinianRing B.Carrier := IsArtinianRing.of_finite K _
  letI : IsArtinianRing C.Carrier := IsArtinianRing.of_finite K _
  let E := MoritaEquivalence.alignedFgEquivalence
    m B.skeleton C.skeleton
  have hq :
      AlgebraNode.faithfulQCount K B n =
        AlgebraNode.faithfulQCount K C n :=
    OpConjecture.IndecomposableSkeleton.AlignedEquivalence.quotientFaithfulLevelCount_eq
      B.skeleton C.skeleton E
      (closedFaithfulNormalForm (K := K) B.skeleton)
      (closedFaithfulNormalForm (K := K) C.skeleton)
      (OpConjecture.AnnihilatorInflation.isFaithfulSupport_monotone
        B.skeleton.obj)
      (OpConjecture.AnnihilatorInflation.isFaithfulSupport_monotone
        C.skeleton.obj) n
  have hs :
      AlgebraNode.faithfulSCount K B n =
        AlgebraNode.faithfulSCount K C n :=
    OpConjecture.IndecomposableSkeleton.AlignedEquivalence.submoduleFaithfulLevelCount_eq
      B.skeleton C.skeleton E
      (closedFaithfulNormalForm (K := K) B.skeleton)
      (closedFaithfulNormalForm (K := K) C.skeleton)
      (OpConjecture.AnnihilatorInflation.isFaithfulSupport_monotone
        B.skeleton.obj)
      (OpConjecture.AnnihilatorInflation.isFaithfulSupport_monotone
        C.skeleton.obj) n
  exact hq.trans (hC.trans hs.symm)

/-- The exceptional connected two-simple/core-three branch has the exact
degree-four equality needed by the bottom recurrence. -/
theorem twoSimpleCoreThree_four
    (B : AlgebraNode K)
    (hConnected : OpConjecture.BlockDecomposition.Node.IsBlockConnected K B)
    (hProjective : projectiveCount K B = 2)
    (hCore : coreSize K B = 3) :
    (AlgebraNode.faithfulQCount K B 4 =
        AlgebraNode.faithfulSCount K B 4) ∨
      (AlgebraNode.qClosure K B).levelCount 4 =
        (AlgebraNode.sClosure K B).levelCount 4 := by
  letI : IsArtinianRing B.Carrier :=
    IsArtinianRing.of_finite K B.Carrier
  let P :=
    OpConjecture.TwoSimpleCoreThreeBasicization.chosenBasicModel
      (K := K) B.Carrier
  letI : Ring P.Carrier := P.ring
  letI : Algebra K P.Carrier := P.algebra
  letI : FiniteDimensional K P.Carrier := P.finiteDimensional
  letI : IsNoetherianRing P.Carrier :=
    IsNoetherianRing.of_finite K P.Carrier
  letI : IsNoetherianRing P.Carrierᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K P.Carrier
  letI : IsNoetherianRing P.Carrierᵐᵒᵖᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K P.Carrierᵐᵒᵖ
  letI : IsNoetherianRing P.Carrierᵐᵒᵖᵐᵒᵖᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional
      K P.Carrierᵐᵒᵖᵐᵒᵖ
  letI : IsArtinianRing P.Carrier :=
    IsArtinianRing.of_finite K P.Carrier
  letI : IsArtinianRing P.Carrierᵐᵒᵖ :=
    OpConjecture.isArtinianRing_op_of_finiteDimensional K P.Carrier
  letI : IsArtinianRing P.Carrierᵐᵒᵖᵐᵒᵖ :=
    OpConjecture.isArtinianRing_op_of_finiteDimensional K P.Carrierᵐᵒᵖ
  let rho :=
    OpConjecture.BlockDecomposition.Node.canonicalLeftSkeleton K P.Carrier
  let E := MoritaEquivalence.alignedFgEquivalence
    P.morita B.skeleton rho
  letI : Finite
      (OpConjecture.CanonicalIndecomposableIndex.{u, u} P.Carrier) :=
    E.labelEquiv.finite_iff.mp inferInstance
  let tau :=
    OpConjecture.rightIndecomposableSkeleton.{u, u, u} K P.Carrier
  let dual :=
    OpConjecture.Contragredient.alignedBiduality K P.Carrier rho tau
  letI : Finite
      (OpConjecture.CanonicalIndecomposableIndex.{u, u} P.Carrierᵐᵒᵖ) :=
    dual.forward.labelEquiv.finite_iff.mp inferInstance
  have hTwoB : Nat.card B.skeleton.SimpleIndex = 2 :=
    (ncard_projectiveLabels_eq_natCard_simpleIndex B.skeleton).symm.trans
      hProjective
  have hTwoP : Nat.card rho.SimpleIndex = 2 :=
    (Nat.card_congr
      (OpConjecture.HereditaryTwoSimpleBoundary.simpleIndexEquiv
        B.skeleton rho E)).symm.trans hTwoB
  have hTwoTau : Nat.card tau.SimpleIndex = 2 := by
    calc
      Nat.card tau.SimpleIndex = Nat.card rho.SimpleIndex :=
        Nat.card_congr
          (OpConjecture.ExtDualTransport.AlignedAntiEquivalence.simpleIndexEquiv
            rho tau dual.forward).symm
      _ = 2 := hTwoP
  let hRank : projectiveRank tau = 2 :=
    (ncard_projectiveLabels_eq_natCard_simpleIndex tau).trans hTwoTau
  let D :=
    OpConjecture.BasicTwoCoordinateData.twoCoordinateDataOfIsBasicAlgebra
      tau P.basic hRank
  let G :=
    OpConjecture.CoordinateGabrielRealization.ExtArrowCotangentRepresentativeData.automaticSplitBasicGabrielArrowRealization
      (K := K) (B := P.Carrier) (I := Fin 2)
      (kappa := OpConjecture.CanonicalIndecomposableIndex.{u, u}
        P.Carrierᵐᵒᵖ)
      (D := D) (tau := tau)
  let e :=
    (OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
      D tau).symm
  let hNoParallelTau : NoParallelExtSupport (K := K) tau :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport tau
  let hNoParallelRho : NoParallelExtSupport (K := K) rho :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport rho
  let S := SplitBasicExtGabrielArrowRealization.twoVertexSupport
    tau G e hNoParallelTau
  have hTri :
      FullProfileEquality K B ∨
        (∃ i j, S.IsOneWayLollipopAt i j) ∨
        ∃ i j, S.IsLoopTwoCycleAt i j :=
    OpConjecture.LoopFreeBasicizedProfile.support_trichotomy_with_loopFree_profile
      B hConnected hProjective hCore
  rcases hTri with hProfile | hOneWay | hLoopTwoCycle
  · right
    rw [← OpConjecture.SetClosure.levelPolynomial_coeff,
      hProfile, OpConjecture.SetClosure.levelPolynomial_coeff]
  · left
    obtain ⟨i, j, hRaw⟩ := hOneWay
    have hCoreB :
        (quotientCore B.skeleton : Set B.Index).ncard = 3 := by
      simpa [coreSize, AlgebraNode.quotientCoreData,
        concreteQuotientCoreData] using hCore
    have hCoreRho :
        (quotientCore rho : Set
          (OpConjecture.CanonicalIndecomposableIndex.{u, u}
            P.Carrier)).ncard = 3 :=
      (OpConjecture.IndecomposableSkeleton.AlignedEquivalence.quotientCore_ncard_eq
        B.skeleton rho E).symm.trans hCoreB
    have hRingelRho : RingelCoreCardinality rho :=
      OpConjecture.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
        rho K
    have hCoreTau :
        (quotientCore tau : Set
          (OpConjecture.CanonicalIndecomposableIndex.{u, u}
            P.Carrierᵐᵒᵖ)).ncard = 3 := by
      calc
        (quotientCore tau : Set
            (OpConjecture.CanonicalIndecomposableIndex.{u, u}
              P.Carrierᵐᵒᵖ)).ncard =
            (submoduleCore rho : Set
              (OpConjecture.CanonicalIndecomposableIndex.{u, u}
                P.Carrier)).ncard :=
          (OpConjecture.IndecomposableSkeleton.AlignedBiduality.submoduleCore_ncard_eq_quotientCore
            rho tau dual).symm
        _ = (quotientCore rho : Set
            (OpConjecture.CanonicalIndecomposableIndex.{u, u}
              P.Carrier)).ncard := hRingelRho.symm
        _ = 3 := hCoreRho
    have hRingelTau : RingelCoreCardinality tau :=
      OpConjecture.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
        tau K
    let tauOp :=
      OpConjecture.rightIndecomposableSkeleton.{u, u, u}
        K P.Carrierᵐᵒᵖ
    let dualRight :=
      OpConjecture.Contragredient.alignedBiduality
        K P.Carrierᵐᵒᵖ tau tauOp
    letI : Finite
        (OpConjecture.CanonicalIndecomposableIndex.{u, u}
          P.Carrierᵐᵒᵖᵐᵒᵖ) :=
      dualRight.forward.labelEquiv.finite_iff.mp inferInstance
    let hNoParallelTauOp : NoParallelExtSupport (K := K) tauOp :=
      OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport tauOp
    have hShape :
        (OpConjecture.QuotientSurvival.TwoCoordinateData.alignedExtTwoVertexSupport
          D tau hNoParallelTau).IsOneWayLollipopAt
          i j := by
      dsimp [S, e] at hRaw
      rw [OpConjecture.QuotientSurvival.TwoCoordinateData.splitBasic_twoVertexSupport_eq_aligned
        D tau hNoParallelTau G] at hRaw
      exact hRaw
    have hModels :=
      OpConjecture.OppositeCoordinateSupport.algEquiv_b0_or_b1_direct_or_opposite_of_oneWayLollipop
        (K := K) (B := P.Carrier)
        (kappa := OpConjecture.CanonicalIndecomposableIndex.{u, u}
          P.Carrierᵐᵒᵖ)
        (lambda := OpConjecture.CanonicalIndecomposableIndex.{u, u}
          P.Carrierᵐᵒᵖᵐᵒᵖ)
        tau tauOp D hNoParallelTau dualRight hNoParallelTauOp hShape
        hRingelTau hRank hCoreTau
    let BP :=
      OpConjecture.LocalNakayamaBranch.algebraNodeMoritaTarget B P.morita
    have transport (hBP :
        AlgebraNode.faithfulQCount K BP 4 =
          AlgebraNode.faithfulSCount K BP 4) :
        AlgebraNode.faithfulQCount K B 4 =
          AlgebraNode.faithfulSCount K B 4 :=
      faithfulLevelCount_eq_of_morita B BP P.morita 4 hBP
    rcases hModels with (hB0 | hB1) | (hB0op | hB1op)
    · exact transport
        (faithfulLevelCount_four_eq_of_b0AlgEquiv BP hB0.some)
    · exact transport
        (faithfulLevelCount_four_eq_of_b1AlgEquiv BP hB1.some)
    · exact transport
        (faithfulLevelCount_four_eq_of_b0OppositeAlgEquiv BP hB0op.some)
    · exact transport
        (faithfulLevelCount_four_eq_of_b1OppositeAlgEquiv BP hB1op.some)
  · exfalso
    have hCoreB :
        (quotientCore B.skeleton : Set B.Index).ncard = 3 := by
      simpa [coreSize, AlgebraNode.quotientCoreData,
        concreteQuotientCoreData] using hCore
    have hCoreRho :
        (quotientCore rho : Set
          (OpConjecture.CanonicalIndecomposableIndex.{u, u}
            P.Carrier)).ncard = 3 :=
      (OpConjecture.IndecomposableSkeleton.AlignedEquivalence.quotientCore_ncard_eq
        B.skeleton rho E).symm.trans hCoreB
    have hRingelRho : RingelCoreCardinality rho :=
      OpConjecture.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
        rho K
    have hCoreTau :
        (quotientCore tau : Set
          (OpConjecture.CanonicalIndecomposableIndex.{u, u}
            P.Carrierᵐᵒᵖ)).ncard = 3 := by
      calc
        (quotientCore tau : Set
            (OpConjecture.CanonicalIndecomposableIndex.{u, u}
              P.Carrierᵐᵒᵖ)).ncard =
            (submoduleCore rho : Set
              (OpConjecture.CanonicalIndecomposableIndex.{u, u}
                P.Carrier)).ncard :=
          (OpConjecture.IndecomposableSkeleton.AlignedBiduality.submoduleCore_ncard_eq_quotientCore
            rho tau dual).symm
        _ = (quotientCore rho : Set
            (OpConjecture.CanonicalIndecomposableIndex.{u, u}
              P.Carrier)).ncard := hRingelRho.symm
        _ = 3 := hCoreRho
    have hRingelTau : RingelCoreCardinality tau :=
      OpConjecture.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
        tau K
    obtain ⟨i, j, hRaw⟩ := hLoopTwoCycle
    dsimp [S, e] at hRaw
    rw [OpConjecture.QuotientSurvival.TwoCoordinateData.splitBasic_twoVertexSupport_eq_aligned
      D tau hNoParallelTau G] at hRaw
    obtain ⟨p, hpi, hpj⟩ :
        ∃ p : Fin 2 ≃ Fin 2, p i = 0 ∧ p j = 1 := by
      fin_cases i <;> fin_cases j
      · exact (hRaw.1 rfl).elim
      · exact ⟨Equiv.refl _, rfl, rfl⟩
      · exact ⟨Equiv.swap 0 1, by simp, by simp⟩
      · exact (hRaw.1 rfl).elim
    let D' := D.reindex p
    have hShape :
        (OpConjecture.QuotientSurvival.TwoCoordinateData.alignedExtTwoVertexSupport
          D' tau hNoParallelTau).IsLoopTwoCycleAt 0 1 := by
      have hReindexed :=
        isLoopTwoCycleAt_reindex D tau hNoParallelTau p hRaw
      simpa only [D', hpi, hpj] using hReindexed
    exact OpConjecture.QuotientSurvival.TwoCoordinateData.false_of_loopTwoCycleSupport
      (K := K) (B := P.Carrier)
      (kappa := OpConjecture.CanonicalIndecomposableIndex.{u, u}
        P.Carrierᵐᵒᵖ)
      D' tau hNoParallelTau hShape hRingelTau hRank hCoreTau

end OpConjecture.BottomLevels.FiniteDimensionalRecurrence
