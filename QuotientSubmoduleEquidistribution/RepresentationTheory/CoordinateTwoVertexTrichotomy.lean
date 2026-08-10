import QuotientSubmoduleEquidistribution.RepresentationTheory.ConnectedSmallCoreExceptionalArrowSupport
import QuotientSubmoduleEquidistribution.RepresentationTheory.CoordinateGabrielRealization
import QuotientSubmoduleEquidistribution.RepresentationTheory.BasicTwoCoordinateData

/-!
# Automatic coordinate two-vertex trichotomy

This file composes the tracked coordinate Gabriel realization
and coordinate-simple alignment with the exceptional-support trichotomy.  It
contains no concrete algebra, quiver, or module classification.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.CoordinateTwoVertexTrichotomy

universe u v

open QuotientSubmoduleEquidistribution.GabrielArrowBridge
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

variable {K B : Type u} {kappa : Type v}
  [Field K] [IsAlgClosed K]
  [Ring B] [Algebra K B]
  [Small.{u} Bᵐᵒᵖ] [IsNoetherianRing Bᵐᵒᵖ]
  [IsArtinianRing B] [IsArtinianRing Bᵐᵒᵖ]
  [Finite kappa]
  (D : QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData
    (K := K) (B := B) (I := Fin 2))
  (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ kappa)

omit [IsAlgClosed K] [IsArtinianRing Bᵐᵒᵖ] in
/-- For a split-basic coordinate algebra with two simple coordinates, the
tracked automatic Ext-Gabriel realization and Peirce/Ext detection package
remove both auxiliary premises from the block-connected support trichotomy. -/
theorem trichotomy_of_blockConnected
    (hRingel : RingelCoreCardinality tau)
    (hRank : projectiveRank tau = 2)
    (hCore : (quotientCore tau : Set kappa).ncard = 3)
    (hNoParallel : NoParallelExtSupport (K := K) tau)
    (hBlockConnected :
      ∀ z : B, IsIdempotentElem z → IsMulCentral z → z = 0 ∨ z = 1) :
    let G :=
      QuotientSubmoduleEquidistribution.CoordinateGabrielRealization.ExtArrowCotangentRepresentativeData.automaticSplitBasicGabrielArrowRealization
        (K := K) (B := B) (I := Fin 2) (kappa := kappa)
        (D := D) (tau := tau)
    let e :=
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau).symm
    let S := SplitBasicExtGabrielArrowRealization.twoVertexSupport
      tau G e hNoParallel
    S.NoLoops ∨
      (∃ i j, S.IsOneWayLollipopAt i j) ∨
      ∃ i j, S.IsLoopTwoCycleAt i j := by
  let G :=
    QuotientSubmoduleEquidistribution.CoordinateGabrielRealization.ExtArrowCotangentRepresentativeData.automaticSplitBasicGabrielArrowRealization
      (K := K) (B := B) (I := Fin 2) (kappa := kappa)
      (D := D) (tau := tau)
  let e := (D.coordinateSimpleIndexEquiv tau).symm
  exact
    SplitBasicExtGabrielArrowRealization.trichotomy_of_blockConnected
      tau G hRingel hRank hCore e hNoParallel
        (D.twoVertexPeirceExtData tau) hBlockConnected

omit [IsArtinianRing Bᵐᵒᵖ] in
/-- Conventional basicness and projective rank two automatically supply the
split coordinates in the block-connected support trichotomy. -/
theorem trichotomy_of_basic_of_blockConnected
    [FiniteDimensional K B]
    (hBasic : QuotientSubmoduleEquidistribution.BasicnessWrapper.IsBasicAlgebra K B)
    (hRingel : RingelCoreCardinality tau)
    (hRank : projectiveRank tau = 2)
    (hCore : (quotientCore tau : Set kappa).ncard = 3)
    (hNoParallel : NoParallelExtSupport (K := K) tau)
    (hBlockConnected :
      ∀ z : B, IsIdempotentElem z → IsMulCentral z → z = 0 ∨ z = 1) :
    let D :=
      QuotientSubmoduleEquidistribution.BasicTwoCoordinateData.twoCoordinateDataOfIsBasicAlgebra
        tau hBasic hRank
    let G :=
      QuotientSubmoduleEquidistribution.CoordinateGabrielRealization.ExtArrowCotangentRepresentativeData.automaticSplitBasicGabrielArrowRealization
        (K := K) (B := B) (I := Fin 2) (kappa := kappa)
        (D := D) (tau := tau)
    let e :=
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau).symm
    let S := SplitBasicExtGabrielArrowRealization.twoVertexSupport
      tau G e hNoParallel
    S.NoLoops ∨
      (∃ i j, S.IsOneWayLollipopAt i j) ∨
      ∃ i j, S.IsLoopTwoCycleAt i j := by
  let D :=
    QuotientSubmoduleEquidistribution.BasicTwoCoordinateData.twoCoordinateDataOfIsBasicAlgebra
      tau hBasic hRank
  exact
    trichotomy_of_blockConnected D tau hRingel hRank hCore hNoParallel
      hBlockConnected

end QuotientSubmoduleEquidistribution.CoordinateTwoVertexTrichotomy
