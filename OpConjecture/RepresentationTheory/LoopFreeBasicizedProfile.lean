import OpConjecture.RepresentationTheory.LoopFreeTwoVertexSerialBridge
import OpConjecture.RepresentationTheory.NakayamaProductFormula
import OpConjecture.RepresentationTheory.TwoSimpleCoreThreeBasicization

/-!
# Profile transport from a loop-free basic Morita model

A loop-free two-vertex support on the right skeleton of a basic Morita model
forces that skeleton to be Nakayama.  The Nakayama product formula gives
equality of its quotient and submodule level polynomials.  Biduality moves
this equality to the model's left skeleton, and Morita alignment moves it to
the original algebra node.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.LoopFreeBasicizedProfile

universe u v

open OpConjecture.BottomLevels.FiniteDimensionalRecurrence
open OpConjecture.GabrielArrowBridge
open OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

variable {K A : Type u} [Field K] [IsAlgClosed K]
  [Ring A] [Algebra K A] [FiniteDimensional K A]
  [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
  [IsNoetherianRing Aᵐᵒᵖᵐᵒᵖ]
  [IsArtinianRing A] [IsArtinianRing Aᵐᵒᵖ]
  {iota kappa : Type v} [Finite iota] [Finite kappa]
  (B : AlgebraNode K)
  (rho : IndecomposableSkeleton.{u, v, u} A iota)
  (tau : IndecomposableSkeleton.{u, v, u} Aᵐᵒᵖ kappa)

omit [IsAlgClosed K] [IsArtinianRing A] [IsArtinianRing Aᵐᵒᵖ] in
/-- Loop-free support on the right skeleton of a Morita model implies the
full quotient--submodule profile equality on the original node. -/
theorem fullProfileEquality_of_noLoops
    (E : IndecomposableSkeleton.AlignedEquivalence B.skeleton rho)
    (dual : IndecomposableSkeleton.AlignedBiduality rho tau)
    (G : SplitBasicExtGabrielArrowRealization.Data (K := K) tau)
    (e : tau.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) tau)
    (hDualNoParallel : NoParallelExtSupport (K := K) rho)
    (hNoLoops :
      (SplitBasicExtGabrielArrowRealization.twoVertexSupport
        tau G e hNoParallel).NoLoops) :
    FullProfileEquality K B := by
  have hNakayama :
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton tau :=
    OpConjecture.NoLoopNakayamaReduction.isNakayamaSkeleton_of_twoVertexSupport_noLoops_of_serialBoundary
      tau rho dual.backward
      (SplitBasicExtGabrielArrowRealization.exceptionalData tau G)
      e hNoParallel hDualNoParallel hNoLoops
  let dualSwap : IndecomposableSkeleton.AlignedBiduality tau rho :=
    { forward := dual.backward
      backward := dual.forward
      backward_label := by
        rw [dual.backward_label]
        exact dual.forward.labelEquiv.symm_symm }
  have hTauProduct :=
    OpConjecture.NakayamaProductFormula.levelPolynomials_eq_fixedTopChainPolynomial_of_alignedBiduality
      tau rho dualSwap hNakayama
  have hTau :
      tau.qClosure.levelPolynomial = tau.sClosure.levelPolynomial :=
    hTauProduct.1.trans hTauProduct.2.symm
  have hRhoQToTauS :
      rho.qClosure.levelPolynomial = tau.sClosure.levelPolynomial :=
    IndecomposableSkeleton.AlignedBiduality.quotientToSubmoduleLevelPolynomial_eq
      rho tau dual
  have hRhoSToTauQ :
      rho.sClosure.levelPolynomial = tau.qClosure.levelPolynomial :=
    IndecomposableSkeleton.AlignedBiduality.submoduleToQuotientLevelPolynomial_eq
      rho tau dual
  have hRho :
      rho.qClosure.levelPolynomial = rho.sClosure.levelPolynomial :=
    hRhoQToTauS.trans (hTau.symm.trans hRhoSToTauQ.symm)
  have hq :
      B.skeleton.qClosure.levelPolynomial = rho.qClosure.levelPolynomial :=
    IndecomposableSkeleton.AlignedEquivalence.quotientLevelPolynomial_eq
      B.skeleton rho E
  have hs :
      B.skeleton.sClosure.levelPolynomial = rho.sClosure.levelPolynomial :=
    IndecomposableSkeleton.AlignedEquivalence.submoduleLevelPolynomial_eq
      B.skeleton rho E
  exact hq.trans (hRho.trans hs.symm)

universe z

open OpConjecture.IndecomposableSkeleton.FaithfulCore
open OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank
open OpConjecture.MoritaBasicizationInterface

variable {F : Type z} [Field F] [IsAlgClosed F]

/-- In the automatic basicized support trichotomy, the loop-free branch is
already the full profile-equality branch on the original algebra node. -/
theorem support_trichotomy_with_loopFree_profile
    (B : AlgebraNode F)
    (hConnected : OpConjecture.BlockDecomposition.Node.IsBlockConnected F B)
    (hProjective : projectiveCount F B = 2)
    (hCore : coreSize F B = 3) :
    letI : IsArtinianRing B.Carrier :=
      IsArtinianRing.of_finite F B.Carrier
    let P :=
      OpConjecture.TwoSimpleCoreThreeBasicization.chosenBasicModel
        (K := F) B.Carrier
    letI : Ring P.Carrier := P.ring
    letI : Algebra F P.Carrier := P.algebra
    letI : FiniteDimensional F P.Carrier := P.finiteDimensional
    letI : IsNoetherianRing P.Carrier :=
      IsNoetherianRing.of_finite F P.Carrier
    letI : IsNoetherianRing P.Carrierᵐᵒᵖ :=
      OpConjecture.isNoetherianRing_op_of_finiteDimensional F P.Carrier
    letI : IsArtinianRing P.Carrier :=
      IsArtinianRing.of_finite F P.Carrier
    letI : IsArtinianRing P.Carrierᵐᵒᵖ :=
      OpConjecture.isArtinianRing_op_of_finiteDimensional F P.Carrier
    let rho :=
      OpConjecture.BlockDecomposition.Node.canonicalLeftSkeleton F P.Carrier
    let E := MoritaEquivalence.alignedFgEquivalence
      P.morita B.skeleton rho
    letI : Finite
        (OpConjecture.CanonicalIndecomposableIndex.{z, z} P.Carrier) :=
      E.labelEquiv.finite_iff.mp inferInstance
    let tau :=
      OpConjecture.rightIndecomposableSkeleton.{z, z, z} F P.Carrier
    let dual :=
      OpConjecture.Contragredient.alignedBiduality F P.Carrier rho tau
    letI : Finite
        (OpConjecture.CanonicalIndecomposableIndex.{z, z} P.Carrierᵐᵒᵖ) :=
      dual.forward.labelEquiv.finite_iff.mp inferInstance
    let hRank : projectiveRank tau = 2 := by
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
      exact (ncard_projectiveLabels_eq_natCard_simpleIndex tau).trans hTwoTau
    let D :=
      OpConjecture.BasicTwoCoordinateData.twoCoordinateDataOfIsBasicAlgebra
        tau P.basic hRank
    let G :=
      OpConjecture.CoordinateGabrielRealization.ExtArrowCotangentRepresentativeData.automaticSplitBasicGabrielArrowRealization
        (K := F) (B := P.Carrier) (I := Fin 2)
        (kappa := OpConjecture.CanonicalIndecomposableIndex.{z, z}
          P.Carrierᵐᵒᵖ)
        (D := D) (tau := tau)
    let e :=
      (OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau).symm
    let S := SplitBasicExtGabrielArrowRealization.twoVertexSupport
      tau G e
        (OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport tau)
    FullProfileEquality F B ∨
      (∃ i j, S.IsOneWayLollipopAt i j) ∨
      ∃ i j, S.IsLoopTwoCycleAt i j := by
  dsimp only
  letI : IsArtinianRing B.Carrier :=
    IsArtinianRing.of_finite F B.Carrier
  let P :=
    OpConjecture.TwoSimpleCoreThreeBasicization.chosenBasicModel
      (K := F) B.Carrier
  letI : Ring P.Carrier := P.ring
  letI : Algebra F P.Carrier := P.algebra
  letI : FiniteDimensional F P.Carrier := P.finiteDimensional
  letI : IsNoetherianRing P.Carrier :=
    IsNoetherianRing.of_finite F P.Carrier
  letI : IsNoetherianRing P.Carrierᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional F P.Carrier
  letI : IsNoetherianRing P.Carrierᵐᵒᵖᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional F P.Carrierᵐᵒᵖ
  letI : IsArtinianRing P.Carrier :=
    IsArtinianRing.of_finite F P.Carrier
  letI : IsArtinianRing P.Carrierᵐᵒᵖ :=
    OpConjecture.isArtinianRing_op_of_finiteDimensional F P.Carrier
  let rho :=
    OpConjecture.BlockDecomposition.Node.canonicalLeftSkeleton F P.Carrier
  let E := MoritaEquivalence.alignedFgEquivalence
    P.morita B.skeleton rho
  letI : Finite
      (OpConjecture.CanonicalIndecomposableIndex.{z, z} P.Carrier) :=
    E.labelEquiv.finite_iff.mp inferInstance
  let tau :=
    OpConjecture.rightIndecomposableSkeleton.{z, z, z} F P.Carrier
  let dual :=
    OpConjecture.Contragredient.alignedBiduality F P.Carrier rho tau
  letI : Finite
      (OpConjecture.CanonicalIndecomposableIndex.{z, z} P.Carrierᵐᵒᵖ) :=
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
      (K := F) (B := P.Carrier) (I := Fin 2)
      (kappa := OpConjecture.CanonicalIndecomposableIndex.{z, z}
        P.Carrierᵐᵒᵖ)
      (D := D) (tau := tau)
  let e :=
    (OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
      D tau).symm
  let hNoParallelTau : NoParallelExtSupport (K := F) tau :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport tau
  let hNoParallelRho : NoParallelExtSupport (K := F) rho :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport rho
  let S := SplitBasicExtGabrielArrowRealization.twoVertexSupport
    tau G e hNoParallelTau
  have hTri :
      S.NoLoops ∨
        (∃ i j, S.IsOneWayLollipopAt i j) ∨
        ∃ i j, S.IsLoopTwoCycleAt i j :=
    OpConjecture.TwoSimpleCoreThreeBasicization.support_trichotomy
      B hConnected hProjective hCore
  rcases hTri with hNoLoops | hExceptional
  · left
    exact fullProfileEquality_of_noLoops
      B rho tau E dual G e hNoParallelTau hNoParallelRho hNoLoops
  · exact Or.inr hExceptional

end OpConjecture.LoopFreeBasicizedProfile
