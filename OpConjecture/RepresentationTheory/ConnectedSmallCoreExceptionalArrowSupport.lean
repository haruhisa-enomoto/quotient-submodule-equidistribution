import OpConjecture.RepresentationTheory.ConnectedSmallCoreExceptionalArrowIdeals
import OpConjecture.RepresentationTheory.GabrielArrowBridge
import OpConjecture.RepresentationTheory.SplitBasicGabrielArrowRealization
import OpConjecture.RepresentationTheory.TwoVertexArrowSupport
import OpConjecture.RepresentationTheory.TwoVertexGabrielConnectedness

/-!
# Exceptional two-vertex arrow support

This file transports the exceptional cyclic-arrow-ideal reduction to the
finite support combinatorics on `Fin 2`.  It does not assert that Ext-Gabriel
arrows have already been realized by algebra elements: the endpoint
injectivity and connectedness hypotheses remain explicit.
-/

noncomputable section

namespace OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

open Set CategoryTheory
open OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Finite ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

namespace ExceptionalArrowIdealData

variable {Arrow : Type w}
  {source target : Arrow → σ.SimpleIndex}
  (D : ExceptionalArrowIdealData σ source target)

/-- Relabel a pair-injective two-simple arrow family by the fixed vertex set
`Fin 2`.  Pair injectivity is the exact finite-support form of the
no-parallel-arrow bound. -/
def twoVertexSupport
    (_D : ExceptionalArrowIdealData σ source target)
    (e : σ.SimpleIndex ≃ Fin 2)
    (hPair : Function.Injective fun a : Arrow ↦ (source a, target a)) :
    OpConjecture.TwoVertexArrowSupport.Data Arrow where
  source a := e (source a)
  target a := e (target a)
  pair_injective := by
    intro a b hab
    apply hPair
    apply Prod.ext
    · apply e.injective
      exact congrArg Prod.fst hab
    · apply e.injective
      exact congrArg Prod.snd hab

/-- The module-theoretic fact that all loop ideals are the unique exceptional
module becomes uniqueness of the loop vertex in the relabelled support. -/
theorem twoVertexSupport_loopsAtMostOneVertex
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3)
    (e : σ.SimpleIndex ≃ Fin 2)
    (hPair : Function.Injective fun a : Arrow ↦ (source a, target a)) :
    (twoVertexSupport σ D e hPair).LoopsAtMostOneVertex := by
  rintro ⟨⟨a, hSourceA, hTargetA⟩, ⟨b, hSourceB, hTargetB⟩⟩
  have hLoopA : source a = target a := by
    apply e.injective
    exact hSourceA.trans hTargetA.symm
  have hLoopB : source b = target b := by
    apply e.injective
    exact hSourceB.trans hTargetB.symm
  have hVertices : source a = source b :=
    loop_vertices_eq σ D hRingel hRank hCore hLoopA hLoopB
  have hZeroOne : (0 : Fin 2) = 1 :=
    hSourceA.symm.trans <| (congrArg e hVertices).trans hSourceB
  exact (by decide : (0 : Fin 2) ≠ 1) hZeroOne

/-- General exceptional-support trichotomy.  Once a future Gabriel
realization supplies pair injectivity and connectedness, the support is
loop-free, a one-way lollipop, or the forbidden loop-plus-two-cycle shape. -/
theorem twoVertexSupport_trichotomy
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3)
    (e : σ.SimpleIndex ≃ Fin 2)
    (hPair : Function.Injective fun a : Arrow ↦ (source a, target a))
    (hConnected : (twoVertexSupport σ D e hPair).UnderlyingConnected) :
    (twoVertexSupport σ D e hPair).NoLoops ∨
      (∃ i j,
        (twoVertexSupport σ D e hPair).IsOneWayLollipopAt i j) ∨
      ∃ i j,
        (twoVertexSupport σ D e hPair).IsLoopTwoCycleAt i j :=
  OpConjecture.TwoVertexArrowSupport.Data.noLoops_or_oneWayLollipop_or_loopTwoCycle
      (twoVertexSupport σ D e hPair) hConnected
      (twoVertexSupport_loopsAtMostOneVertex σ D
        hRingel hRank hCore e hPair)

end ExceptionalArrowIdealData

namespace ExceptionalExtGabrielArrowIdealData

variable {K A : Type u}
  [Field K] [IsAlgClosed K]
  [Ring A] [Small.{u} A] [IsNoetherianRing A] [IsArtinianRing A]
  [Algebra K A]
  {κ : Type v} [Finite κ]
  (τ : IndecomposableSkeleton.{u, v, u} A κ)

open OpConjecture.GabrielArrowBridge

/-- Exceptional arrow-ideal data indexed by the actual multiplicity-bearing
Ext-Gabriel arrows. -/
abbrev Data :=
  ExceptionalArrowIdealData τ
    (ExtGabrielArrowIndex.source (K := K) τ)
    (ExtGabrielArrowIndex.target (K := K) τ)

/-- Relabel the Ext-Gabriel arrow endpoints by `Fin 2`.  The no-parallel
theorem discharges pair injectivity automatically. -/
def twoVertexSupport
    (D : Data (K := K) τ)
    (e : τ.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) τ) :
    OpConjecture.TwoVertexArrowSupport.Data
      (ExtGabrielArrowIndex (K := K) τ) :=
  ExceptionalArrowIdealData.twoVertexSupport τ D e
    (ExtGabrielArrowIndex.source_target_injective τ hNoParallel)

omit [IsAlgClosed K] [IsArtinianRing A] [Finite κ] in
/-- A nonzero cross `Ext¹` group produces the literal cross-arrow required by
the multiplicity-bearing Ext-Gabriel support. -/
theorem underlyingConnected_of_hasCrossExt
    (D : Data (K := K) τ)
    (e : τ.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) τ)
    (hCross :
      OpConjecture.TwoVertexGabrielConnectedness.HasCrossExt τ e) :
    (twoVertexSupport τ D e hNoParallel).UnderlyingConnected := by
  rcases hCross with hForward | hBackward
  · left
    let s := e.symm 0
    let t := e.symm 1
    letI : FiniteDimensional K (ExtOne τ s t) :=
      (hNoParallel s t).1
    letI : Nontrivial (ExtOne τ s t) := hForward
    let a : ExtGabrielArrowIndex (K := K) τ :=
      ⟨s, t, ⟨0, Module.finrank_pos⟩⟩
    refine ⟨a, ?_, ?_⟩
    · simp [twoVertexSupport,
        ExceptionalArrowIdealData.twoVertexSupport,
        ExtGabrielArrowIndex.source, a, s]
    · simp [twoVertexSupport,
        ExceptionalArrowIdealData.twoVertexSupport,
        ExtGabrielArrowIndex.target, a, t]
  · right
    let s := e.symm 1
    let t := e.symm 0
    letI : FiniteDimensional K (ExtOne τ s t) :=
      (hNoParallel s t).1
    letI : Nontrivial (ExtOne τ s t) := hBackward
    let a : ExtGabrielArrowIndex (K := K) τ :=
      ⟨s, t, ⟨0, Module.finrank_pos⟩⟩
    refine ⟨a, ?_, ?_⟩
    · simp [twoVertexSupport,
        ExceptionalArrowIdealData.twoVertexSupport,
        ExtGabrielArrowIndex.source, a, s]
    · simp [twoVertexSupport,
        ExceptionalArrowIdealData.twoVertexSupport,
        ExtGabrielArrowIndex.target, a, t]

omit [IsAlgClosed K] [IsArtinianRing A] [Finite κ] in
/-- The minimal Peirce/cotangent detection datum plus block connectedness
supplies connected Ext-Gabriel support.  The presentation ring `Peirce` is
kept separate from the module ring `A`, allowing the right-module
instantiation `A = Peirceᵐᵒᵖ`. -/
theorem underlyingConnected_of_blockConnected
    {Peirce : Type u} [Ring Peirce] [IsArtinianRing Peirce]
    (D : Data (K := K) τ)
    (e : τ.SimpleIndex ≃ Fin 2)
    (P :
      OpConjecture.TwoVertexGabrielConnectedness.TwoVertexPeirceExtData
        (Peirce := Peirce) τ e)
    (hConnected : ∀ z : Peirce,
      IsIdempotentElem z → IsMulCentral z → z = 0 ∨ z = 1)
    (hNoParallel : NoParallelExtSupport (K := K) τ) :
    (twoVertexSupport τ D e hNoParallel).UnderlyingConnected :=
  underlyingConnected_of_hasCrossExt τ D e hNoParallel
    (OpConjecture.TwoVertexGabrielConnectedness.TwoVertexPeirceExtData.hasCrossExt_of_blockConnected
      τ e P hConnected)

omit [IsAlgClosed K] [IsArtinianRing A] in
/-- Ext-Gabriel form of the general exceptional-support trichotomy.  The
remaining connectedness premise is deliberately explicit: it belongs to
the future theorem relating block connectedness to Gabriel support. -/
theorem trichotomy
    (D : Data (K := K) τ)
    (hRingel : RingelCoreCardinality τ)
    (hRank : projectiveRank τ = 2)
    (hCore : (quotientCore τ : Set κ).ncard = 3)
    (e : τ.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) τ)
    (hConnected :
      (twoVertexSupport τ D e hNoParallel).UnderlyingConnected) :
    (twoVertexSupport τ D e hNoParallel).NoLoops ∨
      (∃ i j,
        (twoVertexSupport τ D e hNoParallel).IsOneWayLollipopAt i j) ∨
      ∃ i j,
        (twoVertexSupport τ D e hNoParallel).IsLoopTwoCycleAt i j :=
  ExceptionalArrowIdealData.twoVertexSupport_trichotomy τ D
    hRingel hRank hCore e
    (ExtGabrielArrowIndex.source_target_injective τ hNoParallel)
    hConnected

end ExceptionalExtGabrielArrowIdealData

namespace SplitBasicExtGabrielArrowRealization

variable {K B : Type u}
  [Field K] [IsAlgClosed K]
  [Ring B]
  [Small.{u} Bᵐᵒᵖ] [IsNoetherianRing Bᵐᵒᵖ]
  [IsArtinianRing Bᵐᵒᵖ] [Algebra K Bᵐᵒᵖ]
  {κ : Type v} [Finite κ]
  (τ : IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ κ)

open OpConjecture.GabrielArrowBridge

/-- Concrete split-basic data indexed by the multiplicity-bearing
Ext-Gabriel arrow type. -/
abbrev Data :=
  SplitBasicGabrielArrowRealization τ
    (ExtGabrielArrowIndex.source (K := K) τ)
    (ExtGabrielArrowIndex.target (K := K) τ)

/-- The exceptional arrow-ideal interface constructed from the concrete
split-basic realization. -/
noncomputable def exceptionalData (G : Data (K := K) τ) :
    ExceptionalExtGabrielArrowIdealData.Data (K := K) τ :=
  G.toExceptionalArrowIdealData

/-- The relabelled two-vertex Ext-Gabriel support attached to a concrete
realization. -/
noncomputable def twoVertexSupport
    (G : Data (K := K) τ)
    (e : τ.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) τ) :
    OpConjecture.TwoVertexArrowSupport.Data
      (ExtGabrielArrowIndex (K := K) τ) :=
  ExceptionalExtGabrielArrowIdealData.twoVertexSupport τ
    (exceptionalData τ G) e hNoParallel

omit [IsAlgClosed K] [IsArtinianRing Bᵐᵒᵖ] in
/-- The complete support-shape reduction from operational data indexed by
Ext-Gabriel arrows: under rank two, core size three,
no-parallelness, and connected support, the quiver is loop-free, a one-way
lollipop, or a loop plus two-cycle. -/
theorem trichotomy
    (G : Data (K := K) τ)
    (hRingel : RingelCoreCardinality τ)
    (hRank : projectiveRank τ = 2)
    (hCore : (quotientCore τ : Set κ).ncard = 3)
    (e : τ.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) τ)
    (hConnected :
      (twoVertexSupport τ G e hNoParallel).UnderlyingConnected) :
    (twoVertexSupport τ G e hNoParallel).NoLoops ∨
      (∃ i j,
        (twoVertexSupport τ G e hNoParallel).IsOneWayLollipopAt i j) ∨
      ∃ i j,
        (twoVertexSupport τ G e hNoParallel).IsLoopTwoCycleAt i j :=
  ExceptionalExtGabrielArrowIdealData.trichotomy τ
    (exceptionalData τ G) hRingel hRank hCore e hNoParallel hConnected

omit [IsAlgClosed K] [IsArtinianRing Bᵐᵒᵖ] in
/-- Block-connected form of the complete exceptional support reduction.
The `TwoVertexPeirceExtData` premise is the minimal remaining split-basic
input: a nonzero cross class in `J(B) / J(B)²` must give a nonzero cross
`Ext¹` group, in either orientation. -/
theorem trichotomy_of_blockConnected
    [IsArtinianRing B]
    (G : Data (K := K) τ)
    (hRingel : RingelCoreCardinality τ)
    (hRank : projectiveRank τ = 2)
    (hCore : (quotientCore τ : Set κ).ncard = 3)
    (e : τ.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) τ)
    (P :
      OpConjecture.TwoVertexGabrielConnectedness.TwoVertexPeirceExtData
        (Peirce := B) τ e)
    (hBlockConnected :
      ∀ z : B, IsIdempotentElem z → IsMulCentral z → z = 0 ∨ z = 1) :
    (twoVertexSupport τ G e hNoParallel).NoLoops ∨
      (∃ i j,
        (twoVertexSupport τ G e hNoParallel).IsOneWayLollipopAt i j) ∨
      ∃ i j,
        (twoVertexSupport τ G e hNoParallel).IsLoopTwoCycleAt i j := by
  apply trichotomy τ G hRingel hRank hCore e hNoParallel
  exact ExceptionalExtGabrielArrowIdealData.underlyingConnected_of_blockConnected
    τ (exceptionalData τ G) e P hBlockConnected hNoParallel

end SplitBasicExtGabrielArrowRealization

end OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore
