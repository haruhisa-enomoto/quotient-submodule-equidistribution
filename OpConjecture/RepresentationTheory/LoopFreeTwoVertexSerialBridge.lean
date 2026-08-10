import OpConjecture.RepresentationTheory.NoLoopNakayamaReduction
import OpConjecture.RepresentationTheory.SerialBoundaryTheorem

/-!
# Loop-free two-vertex serial bridge

This file packages the general loop-free two-vertex support input into the
maintained two-sided serial boundary theorem.  No concrete algebra or module classification occurs.
-/

noncomputable section

namespace OpConjecture.NoLoopNakayamaReduction

open OpConjecture.GabrielArrowBridge
open OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

universe u v

variable
    {K R S : Type u}
    [Field K] [IsAlgClosed K]
    [Ring R] [Small.{u} R] [Algebra K R] [FiniteDimensional K R]
    [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
    [Ring S] [Small.{u} S] [Algebra K S] [FiniteDimensional K S]
    [IsNoetherianRing S]
    {ι κ : Type v} [Finite ι] [Finite κ]
    (σ : IndecomposableSkeleton.{u, v, u} R ι)
    (τ : IndecomposableSkeleton.{u, v, u} S κ)

omit [IsAlgClosed K] [Finite ι] [Finite κ] in
/-- A loop-free two-vertex Ext support has both degree-one conditions.
Aligned duality turns incoming degree one into the missing outgoing serial
boundary, so the only residual general module-theoretic premise is the exact
pointwise simple-top-or-simple-socle alternative. -/
theorem isNakayamaSkeleton_of_twoVertexSupport_noLoops_of_simpleTopOrSocle
    (D : IndecomposableSkeleton.AlignedAntiEquivalence σ τ)
    (G : ExceptionalExtGabrielArrowIdealData.Data (K := K) σ)
    (e : σ.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) σ)
    (hDualNoParallel : NoParallelExtSupport (K := K) τ)
    (hNoLoops :
      (ExceptionalExtGabrielArrowIdealData.twoVertexSupport
        σ G e hNoParallel).NoLoops)
    (hEndpoint : SerialRingBridge.HasSimpleTopOrSocle σ) :
    LocalNakayamaBranch.IsNakayamaSkeleton σ := by
  let hFinite :
      ExtDegreeNakayamaReduction.FiniteExtOneSupport (K := K) σ :=
    fun s t => (hNoParallel s t).1
  let hDualFinite :
      ExtDegreeNakayamaReduction.FiniteExtOneSupport (K := K) τ :=
    fun s t => (hDualNoParallel s t).1
  apply
    SerialRingBridge.isNakayamaSkeleton_of_extSourceTarget_injective_of_simpleTopOrSocle
      (K := K) σ τ D hFinite hDualFinite hNoParallel hDualNoParallel
  · exact
      extSource_injective_of_twoVertexSupport_noLoops
        σ G e hNoParallel hNoLoops
  · exact
      extTarget_injective_of_twoVertexSupport_noLoops
        σ G e hNoParallel hNoLoops
  · exact hEndpoint

omit [IsAlgClosed K] [Finite ι] [Finite κ] in
/-- A loop-free two-vertex Ext support forces the full Nakayama skeleton.
The source and target degree-one conditions give the projective and injective
uniserial boundaries, and the abstract two-sided serial theorem closes the
former simple-top-or-simple-socle seam. -/
theorem isNakayamaSkeleton_of_twoVertexSupport_noLoops_of_serialBoundary
    (D : IndecomposableSkeleton.AlignedAntiEquivalence σ τ)
    (G : ExceptionalExtGabrielArrowIdealData.Data (K := K) σ)
    (e : σ.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) σ)
    (hDualNoParallel : NoParallelExtSupport (K := K) τ)
    (hNoLoops :
      (ExceptionalExtGabrielArrowIdealData.twoVertexSupport
        σ G e hNoParallel).NoLoops) :
    LocalNakayamaBranch.IsNakayamaSkeleton σ := by
  letI : IsArtinianRing R := IsArtinianRing.of_finite K R
  letI : IsArtinianRing S := IsArtinianRing.of_finite K S
  let hFinite :
      ExtDegreeNakayamaReduction.FiniteExtOneSupport (K := K) σ :=
    fun s t ↦ (hNoParallel s t).1
  let hDualFinite :
      ExtDegreeNakayamaReduction.FiniteExtOneSupport (K := K) τ :=
    fun s t ↦ (hDualNoParallel s t).1
  have hSource :
      Function.Injective
        (ExtGabrielArrowIndex.source (K := K) σ) :=
    extSource_injective_of_twoVertexSupport_noLoops
      σ G e hNoParallel hNoLoops
  have hTarget :
      Function.Injective
        (ExtGabrielArrowIndex.target (K := K) σ) :=
    extTarget_injective_of_twoVertexSupport_noLoops
      σ G e hNoParallel hNoLoops
  have hProjective :
      LocalNakayamaBranch.IsProjectiveNakayamaSkeleton σ :=
    SerialRingBridge.projectiveNakayamaSkeleton_of_extSource_injective
      σ hFinite hSource
  have hDualSource :
      Function.Injective
        (ExtGabrielArrowIndex.source (K := K) τ) :=
    OpConjecture.ExtDualTransport.AlignedAntiEquivalence.dualExtSource_injective_of_extTarget_injective
      σ τ D hNoParallel hDualNoParallel hTarget
  have hDualProjective :
      LocalNakayamaBranch.IsProjectiveNakayamaSkeleton τ :=
    SerialRingBridge.projectiveNakayamaSkeleton_of_extSource_injective
      τ hDualFinite hDualSource
  have hInjective :
      SerialRingBridge.IsInjectiveNakayamaSkeleton σ :=
    SerialRingBridge.injectiveNakayamaSkeleton_of_dual_projectiveNakayama
      σ τ D hDualProjective
  exact
    SerialEndpointReduction.isNakayamaSkeleton_of_projective_and_injective_boundaries
      (K := K) σ hProjective hInjective

end OpConjecture.NoLoopNakayamaReduction
