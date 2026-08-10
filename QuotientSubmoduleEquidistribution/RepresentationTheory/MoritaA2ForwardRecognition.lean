import QuotientSubmoduleEquidistribution.RepresentationTheory.BasicTwoCoordinateData
import QuotientSubmoduleEquidistribution.RepresentationTheory.HereditaryCardThreeTriangularRecognition
import QuotientSubmoduleEquidistribution.RepresentationTheory.HereditaryMoritaTransport
import QuotientSubmoduleEquidistribution.RepresentationTheory.MoritaTriangularRecognition
import QuotientSubmoduleEquidistribution.RepresentationTheory.MoritaA2Boundary

/-!
# Forward Morita recognition at the two-simple cardinality-three boundary

This file discharges the forward Morita-recognition premise left in the
level-three boundary.  A two-simple node with three indecomposable objects
and equality of projective rank with faithful-core size is basicized.  Morita
transport, contragredient duality, and the unique-Ext triangular recognition
then identify its basic carrier with the abstract triangular algebra.

The factor-facing theorem composes this result with a supplied identification
of the abstract triangular algebra with the carrier of the fixed `A₂` node.
The fixed node's simple count, indecomposable count, and core size remain
explicit inputs to the existing boundary assembly.  No concrete module
classification or quiver presentation is used here.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.MoritaTriangularRecognition

universe u

open QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank
open QuotientSubmoduleEquidistribution.MoritaBasicizationInterface

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- A two-simple, three-indecomposable node at projective/core equality is
Morita equivalent to the abstract triangular algebra. -/
theorem moritaEquivalence_triangular_of_twoSimples_of_cardThree_of_projectiveCount_eq_coreSize
    (B : AlgebraNode K)
    (hTwo : Nat.card B.skeleton.SimpleIndex = 2)
    (hThree : Nat.card B.Index = 3)
    (hvd : projectiveCount K B = coreSize K B) :
    Nonempty (MoritaEquivalence K B.Carrier
      (QuotientSubmoduleEquidistribution.A2Triangular.Model K)) := by
  let P : MoritaBasicModel (K := K) (A := B.Carrier) :=
    (QuotientSubmoduleEquidistribution.FullIdempotentMorita.finiteDimensionalMoritaBasicization
      K B.Carrier).some
  letI : Ring P.Carrier := P.ring
  letI : Algebra K P.Carrier := P.algebra
  letI : FiniteDimensional K P.Carrier := P.finiteDimensional
  letI : IsNoetherianRing P.Carrier :=
    IsNoetherianRing.of_finite K P.Carrier
  letI : IsNoetherianRing P.Carrierᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K P.Carrier
  letI : IsArtinianRing B.Carrier := IsArtinianRing.of_finite K B.Carrier
  letI : IsArtinianRing P.Carrier := IsArtinianRing.of_finite K P.Carrier
  letI : IsArtinianRing P.Carrierᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K P.Carrier
  let rho :=
    QuotientSubmoduleEquidistribution.BlockDecomposition.Node.canonicalLeftSkeleton K P.Carrier
  let E := MoritaEquivalence.alignedFgEquivalence
    P.morita B.skeleton rho
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} P.Carrier) :=
    E.labelEquiv.finite_iff.mp inferInstance
  have hTwoP : Nat.card rho.SimpleIndex = 2 :=
    (Nat.card_congr
      (QuotientSubmoduleEquidistribution.HereditaryTwoSimpleBoundary.simpleIndexEquiv
        B.skeleton rho E)).symm.trans hTwo
  have hThreeP :
      Nat.card
        (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} P.Carrier) = 3 :=
    (Nat.card_congr E.labelEquiv).symm.trans hThree
  have hHereditaryB : FinitelyGeneratedLeftHereditary B.Carrier :=
    QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.finitelyGeneratedLeftHereditary_of_projectiveCount_eq_coreSize
      K B hvd
  have hHereditaryP : FinitelyGeneratedLeftHereditary P.Carrier :=
    QuotientSubmoduleEquidistribution.HereditaryMoritaTransport.finitelyGeneratedLeftHereditary_of_fgEquivalence
      P.morita.finiteDimensionalFgEquivalence hHereditaryB
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
  have hRankTau : projectiveRank tau = 2 := by
    calc
      projectiveRank tau = Nat.card tau.SimpleIndex :=
        ncard_projectiveLabels_eq_natCard_simpleIndex tau
      _ = 2 := hTwoTau
  let D :=
    QuotientSubmoduleEquidistribution.BasicTwoCoordinateData.twoCoordinateDataOfIsBasicAlgebra
      tau P.basic hRankTau
  have hNakayama :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton rho :=
    QuotientSubmoduleEquidistribution.HereditaryTwoSimpleBoundary.isNakayamaSkeleton_of_twoSimples_of_finitelyGeneratedLeftHereditary
      (K := K) (R := P.Carrier) (S := P.Carrierᵐᵒᵖ)
      rho tau dual.forward hHereditaryP hTwoP
  have hRecognize : Nonempty
      (QuotientSubmoduleEquidistribution.A2Triangular.Model K ≃ₐ[K] P.Carrier) :=
    QuotientSubmoduleEquidistribution.HereditaryTwoSimpleCardThreeShape.nonempty_singleCrossTriangularAlgEquiv_of_alignedAntiEquivalence
      rho tau dual.forward D hNakayama hHereditaryP hTwoP hThreeP
  exact moritaEquivalence_triangular_of_basicModel P hRecognize

end QuotientSubmoduleEquidistribution.MoritaTriangularRecognition

namespace QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary

universe u

open QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence
open QuotientSubmoduleEquidistribution.AnnihilatorInflation
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank

variable (K : Type u) [Field K] [IsAlgClosed K]
  {R : Type u} [Ring R] [Algebra K R]
  [IsArtinianRing R] [IsNoetherianRing Rᵐᵒᵖ]

variable (A₂ : AlgebraNode K)
  {iota : Type (u + 1)}
  (sigma : IndecomposableSkeleton.{u, u + 1, u} R iota)

omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- A core-two factor with two simples and three indecomposables is Morita
equivalent to the fixed node as soon as that node's carrier is identified
with the abstract triangular algebra. -/
theorem isMoritaA2Factor_of_twoSimples_of_cardThree
    [FiniteDimensional K R] [Finite iota]
    (hModel : Nonempty
      (QuotientSubmoduleEquidistribution.A2Triangular.Model K ≃ₐ[K] A₂.Carrier))
    (I : CoreTwoFactorIdeal (R := R))
    (hTwo : factorSimpleCount K sigma I.1 = 2)
    (hThree : factorIndecomposableCount (R := R) I.1 = 3) :
    IsMoritaA2Factor K A₂ I.1 := by
  let B := factorNode K sigma I.1
  have hTwoB : Nat.card B.skeleton.SimpleIndex = 2 := by
    simpa [B] using hTwo
  have hThreeB : Nat.card B.Index = 3 := by
    simpa [factorIndecomposableCount, B, factorNode] using hThree
  have hcore : coreSize K B = 2 := by
    simpa [B, factorNode, coreSize, AlgebraNode.quotientCoreData,
      concreteQuotientCoreData] using I.2
  have hvd : projectiveCount K B = coreSize K B := by
    calc
      projectiveCount K B = Nat.card B.skeleton.SimpleIndex :=
        ncard_projectiveLabels_eq_natCard_simpleIndex B.skeleton
      _ = 2 := hTwoB
      _ = coreSize K B := hcore.symm
  obtain ⟨m⟩ :=
    QuotientSubmoduleEquidistribution.MoritaTriangularRecognition.moritaEquivalence_triangular_of_twoSimples_of_cardThree_of_projectiveCount_eq_coreSize
      B hTwoB hThreeB hvd
  obtain ⟨e⟩ := hModel
  exact ⟨MoritaEquivalence.trans K m
    (MoritaEquivalence.ofAlgEquiv e)⟩

variable (duality : ∀ I : TwoSidedIdeal R,
  ArtinDuality.Data (Quotient.Factor I))

include sigma duality in
/-- The two-simple residual fiber no longer needs a separate forward
Morita-classification premise once the fixed carrier is identified with the
abstract triangular algebra. -/
theorem FiberData.ofTriangularRecognition
    [FiniteDimensional K R] [Finite iota]
    (hA₂card : Nat.card A₂.Index = 3)
    (hModel : Nonempty
      (QuotientSubmoduleEquidistribution.A2Triangular.Model K ≃ₐ[K] A₂.Carrier))
    (I : CoreTwoFactorIdeal (R := R))
    (hTwo : factorSimpleCount K sigma I.1 = 2) :
    FiberData K A₂ I := by
  exact FiberData.ofCardThreeMorita
    K A₂ sigma duality hA₂card I hTwo
      (fun hThree ↦
        isMoritaA2Factor_of_twoSimples_of_cardThree
          K A₂ sigma hModel I hTwo hThree)

/-- Complete rank-branch assembly with the former `hmorita` argument
discharged by intrinsic triangular recognition.  Facts about the fixed node
remain explicit and independent of this forward implication. -/
def ClassificationData.ofTriangularRecognition
    [FiniteDimensional K R] [Finite iota]
    (hA₂card : Nat.card A₂.Index = 3)
    (hA₂simple : Nat.card A₂.skeleton.SimpleIndex = 2)
    (hModel : Nonempty
      (QuotientSubmoduleEquidistribution.A2Triangular.Model K ≃ₐ[K] A₂.Carrier))
    (coreTwo : ∀ I : TwoSidedIdeal R,
      IsMoritaA2Factor K A₂ I →
        (quotientCore (ArtinBottomThree.factorSkeleton (R := R) I) :
          Set (CanonicalIndecomposableIndex.{u, u}
            (Quotient.Factor I))).ncard = 2) :
    ClassificationData K A₂ (R := R) :=
  ClassificationData.ofCardThreeMorita K A₂ sigma duality
    hA₂card hA₂simple
    (fun I hTwo hThree ↦
      isMoritaA2Factor_of_twoSimples_of_cardThree
        K A₂ sigma hModel I hTwo hThree)
    coreTwo

end QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary
