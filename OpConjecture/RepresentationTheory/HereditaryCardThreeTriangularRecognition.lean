import OpConjecture.RepresentationTheory.HereditaryTwoSimpleCardThreeEndpoints
import OpConjecture.RepresentationTheory.UniqueExtTriangularRecognition

/-!
# Triangular recognition at the hereditary two-simple boundary

A hereditary Nakayama skeleton with two simple objects and three
indecomposable objects has exactly one object of composition length two.
Contragredient duality transports that object to the right-module skeleton,
where the resulting unique cross Ext arrow recognizes the algebra as the
abstract three-dimensional triangular algebra.

The argument is intrinsic.  It uses no quiver presentation and no
classification of modules over a concrete algebra.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.HereditaryTwoSimpleCardThreeShape

open OpConjecture.GabrielArrowBridge
open OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

universe u v

variable {K B : Type u} {iota kappa : Type v}
  [Field K] [IsAlgClosed K]
  [Ring B] [Small.{u} B] [Algebra K B]
  [FiniteDimensional K B]
  [IsNoetherianRing B] [IsNoetherianRing Bᵐᵒᵖ]
  [Finite iota] [Finite kappa]

variable
  (sigma : OpConjecture.IndecomposableSkeleton.{u, v, u} B iota)
  (tau : OpConjecture.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ kappa)
  (A : OpConjecture.IndecomposableSkeleton.AlignedAntiEquivalence sigma tau)
  (D : OpConjecture.QuotientSurvival.TwoCoordinateData
    (K := K) (B := B))

include tau A D in
/-- An aligned right-module skeleton and two split coordinates recognize a
hereditary two-simple, three-indecomposable Nakayama algebra as the abstract
triangular algebra. -/
theorem nonempty_singleCrossTriangularAlgEquiv_of_alignedAntiEquivalence
    (hNakayama : OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton sigma)
    (hHereditary : FinitelyGeneratedLeftHereditary B)
    (hTwo : Nat.card sigma.SimpleIndex = 2)
    (hThree : Nat.card iota = 3) :
    Nonempty (OpConjecture.A2Triangular.Model K ≃ₐ[K] B) := by
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI : IsArtinianRing Bᵐᵒᵖ := IsArtinianRing.of_finite K Bᵐᵒᵖ
  let hNoParallelSigma : NoParallelExtSupport (K := K) sigma :=
    OpConjecture.HereditaryTwoSimpleBoundary.noParallelExtSupport_of_finiteDimensional
      sigma
  let hNoParallelTau : NoParallelExtSupport (K := K) tau :=
    OpConjecture.HereditaryTwoSimpleBoundary.noParallelExtSupport_of_finiteDimensional
      tau
  let eDual : sigma.LengthTwoIndex ≃ tau.LengthTwoIndex :=
    OpConjecture.ExtDualTransport.AlignedAntiEquivalence.lengthTwoEquiv
      sigma tau A
  have hSigmaLengthCard : Nat.card sigma.LengthTwoIndex = 1 :=
    natCard_lengthTwoIndex_eq_one sigma hNakayama hTwo hThree
  have hTauLengthCard : Nat.card tau.LengthTwoIndex = 1 := by
    calc
      Nat.card tau.LengthTwoIndex = Nat.card sigma.LengthTwoIndex :=
        Nat.card_congr eDual.symm
      _ = 1 := hSigmaLengthCard
  have hTauArrowCard :
      Nat.card (ExtGabrielArrowIndex (K := K) tau) = 1 := by
    calc
      Nat.card (ExtGabrielArrowIndex (K := K) tau) =
          Nat.card tau.LengthTwoIndex :=
        (LengthTwo.natCard_lengthTwoIndex_eq_extGabrielArrowIndex
          tau hNoParallelTau).symm
      _ = 1 := hTauLengthCard
  obtain ⟨aTau⟩ := (Nat.card_eq_one_iff_unique.mp hTauArrowCard).2
  let eTau : tau.LengthTwoIndex ≃ ExtGabrielArrowIndex (K := K) tau :=
    LengthTwo.lengthTwoEquivExtGabrielArrow tau hNoParallelTau
  let xTau : tau.LengthTwoIndex := eTau.symm aTau
  let xSigma : sigma.LengthTwoIndex := eDual.symm xTau
  let eSigma : sigma.LengthTwoIndex ≃
      ExtGabrielArrowIndex (K := K) sigma :=
    LengthTwo.lengthTwoEquivExtGabrielArrow sigma hNoParallelSigma
  let aSigma : ExtGabrielArrowIndex (K := K) sigma := eSigma xSigma
  have hNoSelf : ∀ s : sigma.SimpleIndex,
      Subsingleton (ExtOne sigma s s) := fun s ↦
    OpConjecture.HereditaryNoSelfExt.selfExtOne_subsingleton_of_finitelyGeneratedLeftHereditary
      (K := K) sigma hHereditary s
  have hSigmaCrossArrow :
      ExtGabrielArrowIndex.source sigma aSigma ≠
        ExtGabrielArrowIndex.target sigma aSigma := by
    intro hst
    rcases aSigma with ⟨s, t, n⟩
    change s = t at hst
    subst t
    letI : Subsingleton (ExtOne sigma s s) := hNoSelf s
    have hzero : Module.finrank K (ExtOne sigma s s) = 0 :=
      Module.finrank_zero_of_subsingleton
    have hpos : 0 < Module.finrank K (ExtOne sigma s s) :=
      lt_of_le_of_lt (Nat.zero_le n.1) n.2
    omega
  have hSigmaCrossLength :
      LengthTwo.source sigma xSigma ≠ LengthTwo.target sigma xSigma := by
    simpa only [aSigma, eSigma,
      OpConjecture.ExtDualTransport.LengthTwo.source_lengthTwoEquivExtGabrielArrow,
      OpConjecture.ExtDualTransport.LengthTwo.target_lengthTwoEquivExtGabrielArrow]
      using hSigmaCrossArrow
  have hTauCross :
      ExtGabrielArrowIndex.source tau aTau ≠
        ExtGabrielArrowIndex.target tau aTau := by
    intro hst
    have hTauLengthEq :
        LengthTwo.source tau xTau = LengthTwo.target tau xTau := by
      calc
        LengthTwo.source tau xTau =
            ExtGabrielArrowIndex.source tau (eTau xTau) :=
          (OpConjecture.ExtDualTransport.LengthTwo.source_lengthTwoEquivExtGabrielArrow
            tau hNoParallelTau xTau).symm
        _ = ExtGabrielArrowIndex.source tau aTau := by
          rw [show eTau xTau = aTau from eTau.apply_symm_apply aTau]
        _ = ExtGabrielArrowIndex.target tau aTau := hst
        _ = ExtGabrielArrowIndex.target tau (eTau xTau) := by
          rw [show eTau xTau = aTau from eTau.apply_symm_apply aTau]
        _ = LengthTwo.target tau xTau :=
          OpConjecture.ExtDualTransport.LengthTwo.target_lengthTwoEquivExtGabrielArrow
            tau hNoParallelTau xTau
    let E : sigma.SimpleIndex ≃ tau.SimpleIndex :=
      OpConjecture.ExtDualTransport.AlignedAntiEquivalence.simpleIndexEquiv
        sigma tau A
    have hEndpoints :
        E (LengthTwo.target sigma xSigma) =
          E (LengthTwo.source sigma xSigma) := by
      calc
        E (LengthTwo.target sigma xSigma) =
            LengthTwo.source tau (eDual xSigma) :=
          (OpConjecture.ExtDualTransport.AlignedAntiEquivalence.source_lengthTwoEquiv
            sigma tau A xSigma).symm
        _ = LengthTwo.source tau xTau := by
          rw [show eDual xSigma = xTau from eDual.apply_symm_apply xTau]
        _ = LengthTwo.target tau xTau := hTauLengthEq
        _ = LengthTwo.target tau (eDual xSigma) := by
          rw [show eDual xSigma = xTau from eDual.apply_symm_apply xTau]
        _ = E (LengthTwo.source sigma xSigma) :=
          OpConjecture.ExtDualTransport.AlignedAntiEquivalence.target_lengthTwoEquiv
            sigma tau A xSigma
    exact hSigmaCrossLength (E.injective hEndpoints).symm
  exact
    OpConjecture.QuotientSurvival.TwoCoordinateData.uniqueCrossExtArrow_singleCrossTriangularAlgEquiv
      (K := K) (B := B) (kappa := kappa)
      D tau aTau hTauArrowCard hTauCross

end OpConjecture.HereditaryTwoSimpleCardThreeShape
