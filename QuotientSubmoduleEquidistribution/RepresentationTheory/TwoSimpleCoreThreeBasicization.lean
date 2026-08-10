import QuotientSubmoduleEquidistribution.RepresentationTheory.ConnectedSmallCoreAssembly
import QuotientSubmoduleEquidistribution.RepresentationTheory.CoordinateTwoVertexTrichotomy
import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulLevelDualityTransport
import QuotientSubmoduleEquidistribution.RepresentationTheory.FullIdempotentConnectedness
import QuotientSubmoduleEquidistribution.RepresentationTheory.HereditaryTwoSimpleBoundary

/-!
# Basicized support at the two-simple, core-three boundary

This file carries the numerical exceptional branch to the split-basic
two-coordinate support used in the paper.  Basicization is performed by a
chosen full idempotent.  The full-corner connectedness theorem keeps the
block hypothesis, Morita equivalence transports the simple and quotient-core
counts, and contragredient duality turns the transported quotient-core count
into the required right-module quotient-core count.

The resulting trichotomy is entirely structural: no concrete algebra or
module classification is used.
-/

noncomputable section

open CategoryTheory Set

namespace QuotientSubmoduleEquidistribution.TwoSimpleCoreThreeBasicization

universe u

open QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence
open QuotientSubmoduleEquidistribution.GabrielArrowBridge
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank
open QuotientSubmoduleEquidistribution.MoritaBasicizationInterface

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- A fixed full-idempotent basicization witness.  Keeping this witness
visible, instead of choosing only an abstract Morita-basic model, lets us
transport block connectedness to its carrier. -/
noncomputable def chosenBasicizingFullIdempotent
    (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A] :
    BasicizingFullIdempotent (K := K) (A := A) :=
  (exists_basicizingFullIdempotent K A).some

/-- The basic Morita model made from the chosen full idempotent. -/
noncomputable def chosenBasicModel
    (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A] :
    MoritaBasicModel (K := K) (A := A) :=
  MoritaBasicModel.ofBasicizingFullIdempotent
    (QuotientSubmoduleEquidistribution.FullIdempotentMorita.fullIdempotentMoritaBridge
      (K := K) (A := A))
    (chosenBasicizingFullIdempotent (K := K) A)

/-- Block connectedness passes from an algebra to the carrier of the chosen
full-idempotent basicization. -/
theorem chosenBasicModel_isBlockConnected
    (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hConnected : ∀ z : A, IsIdempotentElem z → IsMulCentral z →
      z = 0 ∨ z = 1) :
    let P := chosenBasicModel (K := K) A
    ∀ z : P.Carrier, IsIdempotentElem z → IsMulCentral z →
      z = 0 ∨ z = 1 := by
  change ∀ z :
      (chosenBasicizingFullIdempotent (K := K) A).idem.Corner,
    IsIdempotentElem z → IsMulCentral z → z = 0 ∨ z = 1
  exact
    QuotientSubmoduleEquidistribution.FullIdempotentMorita.fullCorner_isBlockConnected
      (chosenBasicizingFullIdempotent (K := K) A).idem
      (QuotientSubmoduleEquidistribution.FullIdempotentMorita.FullFrame.ofFull
        (chosenBasicizingFullIdempotent (K := K) A).full)
      hConnected

/-- A block-connected node in the exceptional numerical branch has, after
the canonical full-idempotent basicization and passage to right modules,
exactly one of the three two-vertex support shapes used in the paper. -/
theorem support_trichotomy
    (B : AlgebraNode K)
    (hConnected : QuotientSubmoduleEquidistribution.BlockDecomposition.Node.IsBlockConnected K B)
    (hProjective : projectiveCount K B = 2)
    (hCore : coreSize K B = 3) :
    letI : IsArtinianRing B.Carrier :=
      IsArtinianRing.of_finite K B.Carrier
    let P := chosenBasicModel (K := K) B.Carrier
    letI : Ring P.Carrier := P.ring
    letI : Algebra K P.Carrier := P.algebra
    letI : FiniteDimensional K P.Carrier := P.finiteDimensional
    letI : IsNoetherianRing P.Carrier :=
      IsNoetherianRing.of_finite K P.Carrier
    letI : IsNoetherianRing P.Carrierᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K P.Carrier
    letI : IsArtinianRing P.Carrier :=
      IsArtinianRing.of_finite K P.Carrier
    letI : IsArtinianRing P.Carrierᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K P.Carrier
    let rho :=
      QuotientSubmoduleEquidistribution.BlockDecomposition.Node.canonicalLeftSkeleton K P.Carrier
    let E := MoritaEquivalence.alignedFgEquivalence
      P.morita B.skeleton rho
    letI : Finite
        (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} P.Carrier) :=
      E.labelEquiv.finite_iff.mp inferInstance
    let tau :=
      QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K P.Carrier
    let dual :=
      QuotientSubmoduleEquidistribution.Contragredient.alignedBiduality K P.Carrier rho tau
    letI : Finite
        (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} P.Carrierᵐᵒᵖ) :=
      dual.forward.labelEquiv.finite_iff.mp inferInstance
    let hRank : projectiveRank tau = 2 := by
      have hTwoB : Nat.card B.skeleton.SimpleIndex = 2 :=
        (ncard_projectiveLabels_eq_natCard_simpleIndex B.skeleton).symm.trans
          hProjective
      have hTwoP : Nat.card rho.SimpleIndex = 2 :=
        (Nat.card_congr
          (QuotientSubmoduleEquidistribution.HereditaryTwoSimpleBoundary.simpleIndexEquiv
            B.skeleton rho E)).symm.trans hTwoB
      have hTwoTau : Nat.card tau.SimpleIndex = 2 := by
        calc
          Nat.card tau.SimpleIndex = Nat.card rho.SimpleIndex :=
            Nat.card_congr
              (QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.simpleIndexEquiv
                rho tau dual.forward).symm
          _ = 2 := hTwoP
      exact (ncard_projectiveLabels_eq_natCard_simpleIndex tau).trans hTwoTau
    let D :=
      QuotientSubmoduleEquidistribution.BasicTwoCoordinateData.twoCoordinateDataOfIsBasicAlgebra
        tau P.basic hRank
    let G :=
      QuotientSubmoduleEquidistribution.CoordinateGabrielRealization.ExtArrowCotangentRepresentativeData.automaticSplitBasicGabrielArrowRealization
        (K := K) (B := P.Carrier) (I := Fin 2)
        (kappa := QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
          P.Carrierᵐᵒᵖ)
        (D := D) (tau := tau)
    let e :=
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau).symm
    let S := SplitBasicExtGabrielArrowRealization.twoVertexSupport
      tau G e
        (QuotientSubmoduleEquidistribution.FiniteDimensionalNoParallelExt.noParallelExtSupport tau)
    S.NoLoops ∨
      (∃ i j, S.IsOneWayLollipopAt i j) ∨
      ∃ i j, S.IsLoopTwoCycleAt i j := by
  dsimp only
  letI : IsArtinianRing B.Carrier :=
    IsArtinianRing.of_finite K B.Carrier
  let P := chosenBasicModel (K := K) B.Carrier
  letI : Ring P.Carrier := P.ring
  letI : Algebra K P.Carrier := P.algebra
  letI : FiniteDimensional K P.Carrier := P.finiteDimensional
  letI : IsNoetherianRing P.Carrier :=
    IsNoetherianRing.of_finite K P.Carrier
  letI : IsNoetherianRing P.Carrierᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K P.Carrier
  letI : IsArtinianRing P.Carrier :=
    IsArtinianRing.of_finite K P.Carrier
  letI : IsArtinianRing P.Carrierᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K P.Carrier
  let rho :=
    QuotientSubmoduleEquidistribution.BlockDecomposition.Node.canonicalLeftSkeleton K P.Carrier
  let E := MoritaEquivalence.alignedFgEquivalence
    P.morita B.skeleton rho
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} P.Carrier) :=
    E.labelEquiv.finite_iff.mp inferInstance
  have hTwoB : Nat.card B.skeleton.SimpleIndex = 2 :=
    (ncard_projectiveLabels_eq_natCard_simpleIndex B.skeleton).symm.trans
      hProjective
  have hTwoP : Nat.card rho.SimpleIndex = 2 :=
    (Nat.card_congr
      (QuotientSubmoduleEquidistribution.HereditaryTwoSimpleBoundary.simpleIndexEquiv
        B.skeleton rho E)).symm.trans hTwoB
  have hCoreB :
      (quotientCore B.skeleton : Set B.Index).ncard = 3 := by
    simpa [coreSize, AlgebraNode.quotientCoreData,
      concreteQuotientCoreData] using hCore
  have hCoreRho :
      (quotientCore rho : Set
        (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} P.Carrier)).ncard =
          3 :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.quotientCore_ncard_eq
      B.skeleton rho E).symm.trans hCoreB
  let tau :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K P.Carrier
  let dual :=
    QuotientSubmoduleEquidistribution.Contragredient.alignedBiduality K P.Carrier rho tau
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} P.Carrierᵐᵒᵖ) :=
    dual.forward.labelEquiv.finite_iff.mp inferInstance
  have hTwoTau : Nat.card tau.SimpleIndex = 2 := by
    calc
      Nat.card tau.SimpleIndex = Nat.card rho.SimpleIndex :=
        Nat.card_congr
          (QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.simpleIndexEquiv
            rho tau dual.forward).symm
      _ = 2 := hTwoP
  have hRank : projectiveRank tau = 2 :=
    (ncard_projectiveLabels_eq_natCard_simpleIndex tau).trans hTwoTau
  have hRingelRho : RingelCoreCardinality rho :=
    QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
      rho K
  letI : IsNoetherianRing P.Carrierᵐᵒᵖᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K P.Carrierᵐᵒᵖ
  have hCoreTau :
      (quotientCore tau : Set
        (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
          P.Carrierᵐᵒᵖ)).ncard = 3 := by
    calc
      (quotientCore tau : Set
          (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
            P.Carrierᵐᵒᵖ)).ncard =
          (submoduleCore rho : Set
            (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
              P.Carrier)).ncard :=
        (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedBiduality.submoduleCore_ncard_eq_quotientCore
          rho tau dual).symm
      _ = (quotientCore rho : Set
          (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
            P.Carrier)).ncard := hRingelRho.symm
      _ = 3 := hCoreRho
  have hRingelTau : RingelCoreCardinality tau :=
    QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
      tau K
  have hNoParallel : NoParallelExtSupport (K := K) tau :=
    QuotientSubmoduleEquidistribution.FiniteDimensionalNoParallelExt.noParallelExtSupport tau
  have hBasicConnected :
      ∀ z : P.Carrier, IsIdempotentElem z → IsMulCentral z →
        z = 0 ∨ z = 1 :=
    chosenBasicModel_isBlockConnected (K := K) B.Carrier hConnected
  exact
    QuotientSubmoduleEquidistribution.CoordinateTwoVertexTrichotomy.trichotomy_of_basic_of_blockConnected
      tau P.basic hRingelTau hRank hCoreTau hNoParallel hBasicConnected

end QuotientSubmoduleEquidistribution.TwoSimpleCoreThreeBasicization
