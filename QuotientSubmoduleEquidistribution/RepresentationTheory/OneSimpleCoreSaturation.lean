import QuotientSubmoduleEquidistribution.RepresentationTheory.ArtinFaithfulTriples
import QuotientSubmoduleEquidistribution.RepresentationTheory.NakayamaProductFormula
import QuotientSubmoduleEquidistribution.RepresentationTheory.SerialBoundaryTheorem

/-!
# Saturation of the Ringel core in the one-simple Nakayama branch

This file closes the one-simple part of the core-size-two analysis without
using a one-loop presentation or classifying modules over a concrete algebra.
An aligned biduality supplies fixed-socle chains.  When there is only one
simple module, every indecomposable lies below the chosen indecomposable
projective in that chain, because the latter epimorphically covers every
uniserial indecomposable.  Hence every indecomposable is torsionless and the
submodule Ringel core is the whole skeleton.
-/

noncomputable section

open Set CategoryTheory

namespace QuotientSubmoduleEquidistribution.OneSimpleCoreSaturation

universe u v

open QuotientSubmoduleEquidistribution.GabrielArrowBridge
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank

variable
    {R S : Type u} [Ring R] [IsNoetherianRing R]
    [Ring S] [IsNoetherianRing S]
    {ι κ : Type v} [Finite ι] [Finite κ]
    (σ : IndecomposableSkeleton.{u, v, u} R ι)
    (τ : IndecomposableSkeleton.{u, v, u} S κ)
    (B : IndecomposableSkeleton.AlignedBiduality σ τ)

omit [Finite ι] in
include τ B in
/-- In a one-simple uniserial skeleton with an aligned biduality, every
indecomposable embeds into the chosen indecomposable projective with its
simple top. -/
theorem inSub_projectiveLabels_of_oneSimple_of_uniserial
    (hOne : LocalNakayamaBranch.OneSimple σ)
    (hσ : LocalNakayamaBranch.IsNakayamaSkeleton σ)
    (i : ι) :
    σ.InSub (projectiveLabels σ) (σ.obj i) := by
  let hτ : ∀ j : κ, IsUniserialModule S (τ.obj j) := fun j ↦
    DualFixedSocleTransport.isUniserialModule_of_image
      τ σ B.backward j (hσ (B.backward.labelEquiv j))
  letI : Finite τ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite σ.SimpleIndex :=
    Finite.of_equiv τ.SimpleIndex
      (DualFixedSocleTransport.simpleIndexEquiv σ τ B.forward).symm
  letI : Fintype σ.SimpleIndex := Fintype.ofFinite σ.SimpleIndex
  letI : Fintype τ.SimpleIndex := Fintype.ofFinite τ.SimpleIndex
  have hτOne : Nat.card τ.SimpleIndex = 1 := by
    calc
      Nat.card τ.SimpleIndex = Nat.card σ.SimpleIndex :=
        Nat.card_congr
          (DualFixedSocleTransport.simpleIndexEquiv σ τ B.forward).symm
      _ = 1 := hOne
  letI : Subsingleton τ.SimpleIndex :=
    (Nat.card_eq_one_iff_unique.mp hτOne).1
  let Qτ := NakayamaFixedTopChains.fixedTopChainData τ hτ
  let Sσ :=
    DualFixedSocleTransport.fixedSocleChainDataOfFixedTop
      σ τ B.forward Qτ
  let j :=
    NakayamaProjectiveQuotients.uniserialTopIndex σ i (hσ i)
  let p : ι := projectiveLabelOfSimple σ j
  obtain ⟨e, he⟩ :=
    NakayamaProjectiveQuotients.exists_epi_projectiveLabelOfSimple_of_top_iso
      σ i (hσ i) j
        (NakayamaProjectiveQuotients.uniserialTopIso σ i (hσ i))
  letI : Epi e := he
  have hlength : σ.compositionLength i ≤ σ.compositionLength p :=
    σ.compositionLength_le_of_epi e
  have hSLength : ∀ q,
      σ.compositionLength (Sσ.labelEquiv q) = (q.2 : ℕ) + 1 := by
    intro q
    change
      σ.compositionLength
          (B.forward.labelEquiv.symm (Qτ.labelEquiv q)) =
        (q.2 : ℕ) + 1
    rw [← LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.compositionLength_eq
      σ τ B.forward]
    simp only [Equiv.apply_symm_apply]
    exact
      NakayamaFixedTopChains.fixedTopLabel_compositionLength τ hτ q
  have hcoord :
      (((Sσ.labelEquiv).symm i).2 : ℕ) ≤
        (((Sσ.labelEquiv).symm p).2 : ℕ) := by
    have hi := hSLength ((Sσ.labelEquiv).symm i)
    have hp := hSLength ((Sσ.labelEquiv).symm p)
    rw [Sσ.labelEquiv.apply_symm_apply] at hi hp
    omega
  have hchain :
      (Sσ.labelEquiv).symm i ∈
        NakayamaCombinatorics.chainClosure
          (NakayamaFixedTopChains.fixedTopCapacity τ)
          ({(Sσ.labelEquiv).symm p} : Set _) := by
    rw [NakayamaFixedTopChains.mem_chainClosure_singleton_iff]
    exact ⟨Subsingleton.elim _ _, hcoord⟩
  obtain ⟨m, hm⟩ := (Sσ.mono_iff i p).2 hchain
  letI : Mono m := hm
  apply σ.inSub_of_mono
    (σ.subset_sSet (projectiveLabels σ)
      (projective_projectiveLabelOfSimple σ j)) m

omit [Finite ι] in
include τ B in
/-- The torsionless/submodule Ringel core of a one-simple uniserial
skeleton is the whole indecomposable skeleton. -/
theorem submoduleCore_eq_univ_of_oneSimple_of_uniserial
    (hOne : LocalNakayamaBranch.OneSimple σ)
    (hσ : LocalNakayamaBranch.IsNakayamaSkeleton σ) :
    (submoduleCore σ : Set ι) = Set.univ := by
  ext i
  constructor
  · intro _
    trivial
  · intro _
    exact inSub_projectiveLabels_of_oneSimple_of_uniserial
      σ τ B hOne hσ i

section NoParallel

variable {K : Type u} [Field K]
  [Small.{u} R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing Rᵐᵒᵖ]
  [Small.{u} S] [Algebra K S]

include B in
omit [Finite ι] [Finite κ] in
/-- One simple and no parallel Ext arrows on the two sides of an aligned
biduality force every source indecomposable to be uniserial.  This replaces
the former one-loop-presentation classification seam. -/
theorem isNakayamaSkeleton_of_oneSimple_of_noParallel
    (hOne : LocalNakayamaBranch.OneSimple σ)
    (hNoParallel : NoParallelExtSupport (K := K) σ)
    (hDualNoParallel : NoParallelExtSupport (K := K) τ) :
    LocalNakayamaBranch.IsNakayamaSkeleton σ := by
  letI : IsArtinianRing R := IsArtinianRing.of_finite K R
  have hDualOne : LocalNakayamaBranch.OneSimple τ := by
    unfold LocalNakayamaBranch.OneSimple at hOne ⊢
    calc
      Nat.card τ.SimpleIndex = Nat.card σ.SimpleIndex :=
        Nat.card_congr
          (ExtDualTransport.AlignedAntiEquivalence.simpleIndexEquiv
            σ τ B.forward).symm
      _ = 1 := hOne
  have hSource : Function.Injective
      (ExtGabrielArrowIndex.source (K := K) σ) := by
    letI : Subsingleton (ExtGabrielArrowIndex (K := K) σ) :=
      LocalNakayamaBranch.extGabrielArrowIndex_subsingleton (K := K)
        σ hOne hNoParallel
    intro a b _
    exact Subsingleton.elim a b
  have hDualSource : Function.Injective
      (ExtGabrielArrowIndex.source (K := K) τ) := by
    letI : Subsingleton (ExtGabrielArrowIndex (K := K) τ) :=
      LocalNakayamaBranch.extGabrielArrowIndex_subsingleton (K := K)
        τ hDualOne hDualNoParallel
    intro a b _
    exact Subsingleton.elim a b
  have hProjective :
      LocalNakayamaBranch.IsProjectiveNakayamaSkeleton σ :=
    SerialRingBridge.projectiveNakayamaSkeleton_of_extSource_injective
      σ (fun s t => (hNoParallel s t).1) hSource
  have hDualProjective :
      LocalNakayamaBranch.IsProjectiveNakayamaSkeleton τ :=
    SerialRingBridge.projectiveNakayamaSkeleton_of_extSource_injective
      τ (fun s t => (hDualNoParallel s t).1) hDualSource
  have hInjective : SerialRingBridge.IsInjectiveNakayamaSkeleton σ :=
    SerialRingBridge.injectiveNakayamaSkeleton_of_dual_projectiveNakayama
      σ τ B.forward hDualProjective
  exact
    SerialEndpointReduction.isNakayamaSkeleton_of_projective_and_injective_boundaries
      (K := K) σ hProjective hInjective

omit [Finite ι] in
include B in
/-- Therefore the one-simple no-parallel branch has total submodule core,
without presenting the algebra by a quiver with relations. -/
theorem submoduleCore_eq_univ_of_oneSimple_of_noParallel
    (hOne : LocalNakayamaBranch.OneSimple σ)
    (hNoParallel : NoParallelExtSupport (K := K) σ)
    (hDualNoParallel : NoParallelExtSupport (K := K) τ) :
    (submoduleCore σ : Set ι) = Set.univ :=
  submoduleCore_eq_univ_of_oneSimple_of_uniserial σ τ B hOne
    (isNakayamaSkeleton_of_oneSimple_of_noParallel
      σ τ B hOne hNoParallel hDualNoParallel)

end NoParallel

omit [Finite ι] [Finite κ] in
/-- Once the submodule Ringel core is total, Ringel core cardinality
identifies the size of the whole complete skeleton with the quotient-core
size. -/
theorem natCard_eq_quotientCore_ncard_of_submoduleCore_eq_univ
    (hRingel : RingelCoreCardinality σ)
    (hSaturation : (submoduleCore σ : Set ι) = Set.univ) :
    Nat.card ι = (quotientCore σ : Set ι).ncard := by
  rw [← Set.ncard_univ, ← hSaturation]
  simpa [RingelCoreCardinality] using hRingel.symm

omit [Finite ι] [Finite κ] in
/-- Once the submodule core is total, Ringel core size two forces the whole
complete skeleton to have exactly two labels. -/
theorem natCard_eq_two_of_coreTwo_of_submoduleCore_eq_univ
    (hRingel : RingelCoreCardinality σ)
    (hCore : (quotientCore σ : Set ι).ncard = 2)
    (hSaturation : (submoduleCore σ : Set ι) = Set.univ) :
    Nat.card ι = 2 := by
  exact
    (natCard_eq_quotientCore_ncard_of_submoduleCore_eq_univ
      σ hRingel hSaturation).trans hCore

omit [Finite κ] in
/-- A two-label skeleton has no quotient-closed support of cardinality
three. -/
theorem isEmpty_qLevel_three_of_natCard_eq_two
    (hι : Nat.card ι = 2) :
    IsEmpty (ArtinQLevel σ 3) := by
  constructor
  intro C
  have hle : (C.1 : Set ι).ncard ≤ Set.univ.ncard :=
    Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  rw [C.2, Set.ncard_univ, hι] at hle
  omega

omit [Finite κ] in
/-- The identical terminal cardinality obstruction on the submodule side. -/
theorem isEmpty_sLevel_three_of_natCard_eq_two
    (hι : Nat.card ι = 2) :
    IsEmpty (ArtinSLevel σ 3) := by
  constructor
  intro C
  have hle : (C.1 : Set ι).ncard ≤ Set.univ.ncard :=
    Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  rw [C.2, Set.ncard_univ, hι] at hle
  omega

end QuotientSubmoduleEquidistribution.OneSimpleCoreSaturation
