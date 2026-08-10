import OpConjecture.ConvexGeometry.CofiniteTwoCardinal
import OpConjecture.RepresentationTheory.ArtinFiniteTypeAlmostSplit
import OpConjecture.RepresentationTheory.LocalARBoundaryFiniteness
import OpConjecture.RepresentationTheory.ProjectiveBoundaryAlmostSplit
import OpConjecture.RepresentationTheory.TwoSidedLocalARData

/-!
# Cofinite two on an arbitrary indecomposable skeleton

This file proves the representation-infinite counting mechanism in
Proposition `prop:cofinite-two`.  The ambient complete indecomposable skeleton
may be infinite.  Finiteness is proved only for the projective/injective
boundary and the adjacent irreducible-pair types.

The exact remaining representation-theoretic input is packaged by
`TwoSidedLocalARData`: local minimal right and left almost-split maps and the
usual projective--injective boundary equivalence.  No algebra presentation or
classification of modules is used.
-/

noncomputable section

open Set CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

open OpConjecture.IndecomposableSkeleton.FaithfulCore
open OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank

universe uk uR uι

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι}
  (σ : IndecomposableSkeleton.{uR, uι, uR} R ι)

namespace TwoSidedLocalARData

variable (D : σ.TwoSidedLocalARData)

include D

/-- A chosen minimal right almost-split decomposition at every label.  At a
projective label this is the canonical `rad P ⟶ P`; at a nonprojective label
it is the supplied local AR decomposition. -/
def chosenRightARAt (i : ι) :
    σ.MinimalRightAlmostSplitDecomposition i := by
  classical
  by_cases hi : Projective (σ.obj i)
  · exact σ.projectiveBoundaryMinimalRightAlmostSplitDecomposition i hi
  · exact D.chosenRightAR σ ⟨i, hi⟩

/-- The quotient irreducible boundary is finite although the ambient
indecomposable skeleton may be infinite. -/
theorem finite_QIrreducibleBoundaryPair :
    Finite σ.QIrreducibleBoundaryPair :=
  FiniteARTranslationData.finite_QIrreducibleBoundaryPair_of_projectiveRightAR
    σ D.toFiniteARTranslationData (fun p ↦
      σ.projectiveBoundaryMinimalRightAlmostSplitDecomposition p.1 p.2)

/-- The submodule irreducible boundary is finite although the ambient
indecomposable skeleton may be infinite. -/
theorem finite_SIrreducibleBoundaryPair :
    Finite σ.SIrreducibleBoundaryPair :=
  FiniteARTranslationData.finite_SIrreducibleBoundaryPair_of_injectiveRightAR
    σ D.toFiniteARTranslationData (fun i ↦ D.chosenRightARAt σ i.1)

/-- The literal quotient-side `rad / rad²` boundary is finite. -/
theorem finite_QRadicalQuotientBoundaryPair :
    Finite σ.QRadicalQuotientBoundaryPair := by
  letI : Finite σ.QIrreducibleBoundaryPair :=
    D.finite_QIrreducibleBoundaryPair σ
  exact Finite.of_equiv σ.QIrreducibleBoundaryPair
    σ.qRadicalQuotientBoundaryPairEquivQIrreducibleBoundaryPair.symm

/-- The literal submodule-side `rad / rad²` boundary is finite. -/
theorem finite_SRadicalQuotientBoundaryPair :
    Finite σ.SRadicalQuotientBoundaryPair := by
  letI : Finite σ.SIrreducibleBoundaryPair :=
    D.finite_SIrreducibleBoundaryPair σ
  exact Finite.of_equiv σ.SIrreducibleBoundaryPair
    σ.sRadicalQuotientBoundaryPairEquivSIrreducibleBoundaryPair.symm

section ArtinianEnds

variable [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]

omit D in
/-- On an arbitrary skeleton, the quotient-side top extreme set is exactly
the finite set of indecomposable projective labels. -/
theorem qTopExtremeSet_eq_projectiveLabels :
    σ.qClosure.topExtremeSet = projectiveLabels σ := by
  ext i
  change σ.qClosure.IsTopExtreme i ↔ Projective (σ.obj i)
  calc
    σ.qClosure.IsTopExtreme i ↔
        σ.IsRelativeSplitProjective Set.univ i := by
      change
        i ∈ σ.qClosure.extremePoints Set.univ ↔
          σ.IsRelativeSplitProjective Set.univ i
      rw [qExtremePoints_eq_relativeSplitProjectives σ]
      simp
    _ ↔ Projective (σ.obj i) :=
      (σ.projective_iff_isRelativeSplitProjective_univ).symm

omit D in
/-- On an arbitrary skeleton, the submodule-side top extreme set is exactly
the finite set of indecomposable injective labels. -/
theorem sTopExtremeSet_eq_injectiveLabels :
    σ.sClosure.topExtremeSet = injectiveLabels σ := by
  ext i
  change σ.sClosure.IsTopExtreme i ↔ Injective (σ.obj i)
  calc
    σ.sClosure.IsTopExtreme i ↔
        σ.IsRelativeSplitInjective Set.univ i := by
      change
        i ∈ σ.sClosure.extremePoints Set.univ ↔
          σ.IsRelativeSplitInjective Set.univ i
      rw [sExtremePoints_eq_relativeSplitInjectives σ]
      simp
    _ ↔ Injective (σ.obj i) :=
      (σ.injective_iff_isRelativeSplitInjective_univ).symm

omit [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))] in
/-- The injective boundary is finite, transported from the finite projective
boundary by the supplied Artin-duality equivalence. -/
theorem finite_injectiveLabels :
    (injectiveLabels σ).Finite := by
  rw [← Set.finite_coe_iff]
  letI : Finite {i : ι // Projective (σ.obj i)} :=
    Set.finite_coe_iff.mpr
      (OpConjecture.NakayamaRepresentationFiniteBridge.finite_projectiveLabels σ)
  exact Finite.of_equiv {i : ι // Projective (σ.obj i)} D.boundary

omit [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))] in
/-- The injective boundary has the same cardinality as the simple-label
type, without assuming representation finiteness. -/
theorem ncard_injectiveLabels_eq_natCard_simpleIndex :
    (injectiveLabels σ).ncard = Nat.card σ.SimpleIndex := by
  calc
    (injectiveLabels σ).ncard =
        Nat.card {i : ι // Injective (σ.obj i)} :=
      (Nat.card_coe_set_eq (injectiveLabels σ)).symm
    _ = Nat.card {i : ι // Projective (σ.obj i)} :=
      (Nat.card_congr D.boundary).symm
    _ = (projectiveLabels σ).ncard :=
      Nat.card_coe_set_eq (projectiveLabels σ)
    _ = Nat.card σ.SimpleIndex :=
      ncard_projectiveLabels_eq_natCard_simpleIndex σ

/-- The quotient-side two-deletion set is genuinely finite, even when the
ambient indecomposable skeleton is infinite. -/
theorem finite_qCofiniteTwoDeletionSet :
    σ.qClosure.cofiniteTwoDeletionSet.Finite := by
  letI : Finite σ.QIrreducibleBoundaryPair :=
    D.finite_QIrreducibleBoundaryPair σ
  letI : Finite σ.qClosure.MixedBoundaryPair :=
    Finite.of_equiv σ.QIrreducibleBoundaryPair
      (D.qMixedBoundaryPairEquivQIrreducibleBoundaryPair σ).symm
  have htop : σ.qClosure.topExtremeSet.Finite := by
    rw [qTopExtremeSet_eq_projectiveLabels σ]
    exact
      OpConjecture.NakayamaRepresentationFiniteBridge.finite_projectiveLabels σ
  exact
    OpConjecture.SetClosure.finite_cofiniteTwoDeletionSet
      σ.qClosure (qClosure_isAntiExchange σ) htop

/-- The submodule-side two-deletion set is genuinely finite, even when the
ambient indecomposable skeleton is infinite. -/
theorem finite_sCofiniteTwoDeletionSet :
    σ.sClosure.cofiniteTwoDeletionSet.Finite := by
  letI : Finite σ.SIrreducibleBoundaryPair :=
    D.finite_SIrreducibleBoundaryPair σ
  letI : Finite σ.sClosure.MixedBoundaryPair :=
    Finite.of_equiv σ.SIrreducibleBoundaryPair
      (D.sMixedBoundaryPairEquivSIrreducibleBoundaryPair σ).symm
  have htop : σ.sClosure.topExtremeSet.Finite := by
    rw [sTopExtremeSet_eq_injectiveLabels σ]
    exact D.finite_injectiveLabels σ
  exact
    OpConjecture.SetClosure.finite_cofiniteTwoDeletionSet
      σ.sClosure (sClosure_isAntiExchange σ) htop

/-- Both finite-set assertions accompanying the arbitrary-representation-type
cofinite-two formulas. -/
theorem cofiniteTwoDeletionSets_finite :
    σ.qClosure.cofiniteTwoDeletionSet.Finite ∧
      σ.sClosure.cofiniteTwoDeletionSet.Finite :=
  ⟨D.finite_qCofiniteTwoDeletionSet σ,
    D.finite_sCofiniteTwoDeletionSet σ⟩

/-- Quotient-side form of `prop:cofinite-two` on a possibly infinite
indecomposable skeleton.  The left side counts two-element deletion subsets
whose complement is quotient-closed; the right boundary is the manuscript's
literal nonzero `rad / rad²` type. -/
theorem qCofiniteTwoNcard_eq_choose_simpleIndex_add_radicalBoundary :
    σ.qClosure.cofiniteTwoDeletionSet.ncard =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.QRadicalQuotientBoundaryPair := by
  letI : Finite σ.QIrreducibleBoundaryPair :=
    D.finite_QIrreducibleBoundaryPair σ
  letI : Finite σ.qClosure.MixedBoundaryPair :=
    Finite.of_equiv σ.QIrreducibleBoundaryPair
      (D.qMixedBoundaryPairEquivQIrreducibleBoundaryPair σ).symm
  have htop : σ.qClosure.topExtremeSet.Finite := by
    rw [qTopExtremeSet_eq_projectiveLabels σ]
    exact
      OpConjecture.NakayamaRepresentationFiniteBridge.finite_projectiveLabels σ
  calc
    σ.qClosure.cofiniteTwoDeletionSet.ncard =
        Nat.choose σ.qClosure.topExtremeSet.ncard 2 +
          Nat.card σ.qClosure.MixedBoundaryPair :=
      OpConjecture.SetClosure.ncard_cofiniteTwoDeletionSet_eq_choose_add
        σ.qClosure (qClosure_isAntiExchange σ) htop
    _ = Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.QIrreducibleBoundaryPair := by
      rw [qTopExtremeSet_eq_projectiveLabels σ,
        ncard_projectiveLabels_eq_natCard_simpleIndex σ,
        Nat.card_congr
          (D.qMixedBoundaryPairEquivQIrreducibleBoundaryPair σ)]
    _ = Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.QRadicalQuotientBoundaryPair := by
      rw [σ.natCard_QRadicalQuotientBoundaryPair_eq_natCard_QIrreducibleBoundaryPair]

/-- Submodule-side form of `prop:cofinite-two` on a possibly infinite
indecomposable skeleton. -/
theorem sCofiniteTwoNcard_eq_choose_simpleIndex_add_radicalBoundary :
    σ.sClosure.cofiniteTwoDeletionSet.ncard =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.SRadicalQuotientBoundaryPair := by
  letI : Finite σ.SIrreducibleBoundaryPair :=
    D.finite_SIrreducibleBoundaryPair σ
  letI : Finite σ.sClosure.MixedBoundaryPair :=
    Finite.of_equiv σ.SIrreducibleBoundaryPair
      (D.sMixedBoundaryPairEquivSIrreducibleBoundaryPair σ).symm
  have htop : σ.sClosure.topExtremeSet.Finite := by
    rw [sTopExtremeSet_eq_injectiveLabels σ]
    exact D.finite_injectiveLabels σ
  calc
    σ.sClosure.cofiniteTwoDeletionSet.ncard =
        Nat.choose σ.sClosure.topExtremeSet.ncard 2 +
          Nat.card σ.sClosure.MixedBoundaryPair :=
      OpConjecture.SetClosure.ncard_cofiniteTwoDeletionSet_eq_choose_add
        σ.sClosure (sClosure_isAntiExchange σ) htop
    _ = Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.SIrreducibleBoundaryPair := by
      rw [sTopExtremeSet_eq_injectiveLabels σ,
        D.ncard_injectiveLabels_eq_natCard_simpleIndex σ,
        Nat.card_congr
          (D.sMixedBoundaryPairEquivSIrreducibleBoundaryPair σ)]
    _ = Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.SRadicalQuotientBoundaryPair := by
      rw [σ.natCard_SRadicalQuotientBoundaryPair_eq_natCard_SIrreducibleBoundaryPair]

/-- The two exact arbitrary-representation-type formulas, bundled in the
orientation and literal radical-quotient language of the manuscript. -/
theorem literalRadicalQuotientCofiniteTwo_formulas :
    σ.qClosure.cofiniteTwoDeletionSet.ncard =
        Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.QRadicalQuotientBoundaryPair ∧
      σ.sClosure.cofiniteTwoDeletionSet.ncard =
        Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.SRadicalQuotientBoundaryPair :=
  ⟨D.qCofiniteTwoNcard_eq_choose_simpleIndex_add_radicalBoundary σ,
    D.sCofiniteTwoNcard_eq_choose_simpleIndex_add_radicalBoundary σ⟩

end ArtinianEnds

end TwoSidedLocalARData

section ArtinDualityAdapter

variable [IsNoetherianRing Rᵐᵒᵖ]

/-- Assemble the exact two-sided local input from finite-module Artin duality
and the classical local right/left almost-split existence statements. -/
def TwoSidedLocalARData.ofArtinDuality
    (A : OpConjecture.ArtinDuality.Data R)
    (rightAR : ∀ z : σ.NonprojectiveLabel,
      Nonempty (σ.MinimalRightAlmostSplitDecomposition z.1))
    (leftAR : ∀ z : σ.NoninjectiveLabel,
      Nonempty (σ.MinimalLeftAlmostSplitDecomposition z.1)) :
    σ.TwoSidedLocalARData where
  rightAR_nonempty := rightAR
  leftAR_nonempty := leftAR
  boundary := by
    simpa [OpConjecture.RingelStable.projectiveSet,
      OpConjecture.RingelStable.injectiveSet] using
      OpConjecture.ArtinDuality.projectiveInjectiveLabelEquiv A σ

end ArtinDualityAdapter

section ModuleFiniteArtinAlgebra

variable {k : Type uk} [CommRing k] [IsArtinianRing k]
  [Algebra k R] [Module.Finite k R] [IsNoetherianRing Rᵐᵒᵖ]

include k

/-- Paper-facing finiteness assertion accompanying
Proposition `prop:cofinite-two`, relative to the same classical local and
duality inputs as the numerical formulas below. -/
theorem moduleFiniteArtin_cofiniteTwoDeletionSets_finite
    (A : OpConjecture.ArtinDuality.Data R)
    (rightAR : ∀ z : σ.NonprojectiveLabel,
      Nonempty (σ.MinimalRightAlmostSplitDecomposition z.1))
    (leftAR : ∀ z : σ.NoninjectiveLabel,
      Nonempty (σ.MinimalLeftAlmostSplitDecomposition z.1)) :
    σ.qClosure.cofiniteTwoDeletionSet.Finite ∧
      σ.sClosure.cofiniteTwoDeletionSet.Finite := by
  letI (i : ι) : Module k (σ.obj i) :=
    Module.restrictScalars k R (σ.obj i)
  letI (i : ι) : IsScalarTower k R (σ.obj i) :=
    IsScalarTower.restrictScalars k R (σ.obj i)
  letI (i : ι) : Module.Finite k (σ.obj i) :=
    Module.Finite.trans R (σ.obj i)
  letI (i : ι) : IsArtinianRing (Module.End R (σ.obj i)) :=
    σ.isArtinianRing_moduleEnd_of_moduleFinite_artinianBase
      (k := k) i
  exact
    TwoSidedLocalARData.cofiniteTwoDeletionSets_finite
      σ (TwoSidedLocalARData.ofArtinDuality σ A rightAR leftAR)

/-- Paper-facing module-finite Artin-algebra form of
Proposition `prop:cofinite-two`, relative precisely to finite-module Artin
duality and the two local almost-split existence theorems not yet supplied by
the pinned libraries. -/
theorem moduleFiniteArtin_literalRadicalQuotientCofiniteTwo_formulas
    (A : OpConjecture.ArtinDuality.Data R)
    (rightAR : ∀ z : σ.NonprojectiveLabel,
      Nonempty (σ.MinimalRightAlmostSplitDecomposition z.1))
    (leftAR : ∀ z : σ.NoninjectiveLabel,
      Nonempty (σ.MinimalLeftAlmostSplitDecomposition z.1)) :
    σ.qClosure.cofiniteTwoDeletionSet.ncard =
        Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.QRadicalQuotientBoundaryPair ∧
      σ.sClosure.cofiniteTwoDeletionSet.ncard =
        Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.SRadicalQuotientBoundaryPair := by
  letI (i : ι) : Module k (σ.obj i) :=
    Module.restrictScalars k R (σ.obj i)
  letI (i : ι) : IsScalarTower k R (σ.obj i) :=
    IsScalarTower.restrictScalars k R (σ.obj i)
  letI (i : ι) : Module.Finite k (σ.obj i) :=
    Module.Finite.trans R (σ.obj i)
  letI (i : ι) : IsArtinianRing (Module.End R (σ.obj i)) :=
    σ.isArtinianRing_moduleEnd_of_moduleFinite_artinianBase
      (k := k) i
  exact
    TwoSidedLocalARData.literalRadicalQuotientCofiniteTwo_formulas
      σ (TwoSidedLocalARData.ofArtinDuality σ A rightAR leftAR)

end ModuleFiniteArtinAlgebra

end OpConjecture.IndecomposableSkeleton
