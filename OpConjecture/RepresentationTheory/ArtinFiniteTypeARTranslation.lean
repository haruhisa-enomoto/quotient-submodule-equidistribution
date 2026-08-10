import OpConjecture.RepresentationTheory.ArtinFiniteTypeAlmostSplit
import OpConjecture.RepresentationTheory.FiniteARTranslationCofinite

/-!
# Auslander--Reiten colevel two over an Artinian base

This file assembles the non-field finite-type construction.  Finite-generator
radical evaluation supplies right almost-split decompositions, while the
abstract finite-module Artin duality supplies the projective--injective
boundary equivalence.  The field-free AR translation and cofinite-two layers
then prove the manuscript's literal `rad / rad²` boundary equality and
`N - 2` formula.

The only input not constructed here is `ArtinDuality.Data R`, the standard
anti-equivalence of finite module categories.  It is kept explicit because
the pinned Mathlib and project-foundation versions do not yet construct it over an arbitrary
commutative Artinian base.
-/

noncomputable section

namespace OpConjecture.IndecomposableSkeleton

universe uk uR uι

section FiniteScalarModules

variable {k : Type uk} [CommRing k] [IsArtinianRing k]
  {R : Type uR} [Ring R] [Algebra k R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
  {ι : Type uι} [Fintype ι]
  (σ : IndecomposableSkeleton.{uR, uι, uR} R ι)
  [∀ i : ι, Module k (σ.obj i)]
  [∀ i : ι, IsScalarTower k R (σ.obj i)]
  [∀ i : ι, Module.Finite k (σ.obj i)]
  (A : OpConjecture.ArtinDuality.Data R)

/-- Finite-generator right AR existence and abstract Artin duality assemble
the exact field-free finite AR translation input. -/
def artinianBaseARTranslationData : σ.FiniteARTranslationData :=
  FiniteARTranslationData.ofArtinDuality σ A fun z ↦
    σ.minimalRightAlmostSplitDecomposition_nonempty_of_artinianBase
      (k := k) z.1

include k A in
/-- The literal `rad / rad²` boundary terms agree over a commutative
Artinian base equipped with finite-module duality. -/
theorem
    artinianBase_natCard_QRadicalQuotientBoundaryPair_eq_natCard_SRadicalQuotientBoundaryPair :
    Nat.card σ.QRadicalQuotientBoundaryPair =
      Nat.card σ.SRadicalQuotientBoundaryPair :=
  FiniteARTranslationData.natCard_QRadicalQuotientBoundaryPair_eq_natCard_SRadicalQuotientBoundaryPair
    σ (artinianBaseARTranslationData (k := k) σ A)

include k A in
/-- Representation-finite Artin-base form of the manuscript's colevel-two
corollary, relative only to the standard finite-module duality interface. -/
theorem artinianBase_literalRadicalQuotientCofiniteTwo_formula
    (hcard : 2 ≤ Nat.card ι) :
    Nat.card σ.QRadicalQuotientBoundaryPair =
        Nat.card σ.SRadicalQuotientBoundaryPair ∧
      σ.literalQuotientLevelCount (Nat.card ι - 2) =
          σ.literalSubobjectLevelCount (Nat.card ι - 2) ∧
        σ.literalQuotientLevelCount (Nat.card ι - 2) =
          Nat.choose (Nat.card σ.SimpleIndex) 2 +
            Nat.card σ.QRadicalQuotientBoundaryPair := by
  letI : DecidableEq ι := Classical.decEq ι
  letI (i : ι) : IsArtinianRing (Module.End R (σ.obj i)) :=
    σ.isArtinianRing_moduleEnd_of_moduleFinite_artinianBase
      (k := k) i
  exact
    FiniteARTranslationData.literalRadicalQuotientCofiniteTwo_formula_of_finiteAR
      σ (artinianBaseARTranslationData (k := k) σ A) hcard

end FiniteScalarModules

section ModuleFiniteAlgebra

variable {k : Type uk} [CommRing k] [IsArtinianRing k]
  {R : Type uR} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
  {ι : Type uι} [Fintype ι]
  (σ : IndecomposableSkeleton.{uR, uι, uR} R ι)
  (A : OpConjecture.ArtinDuality.Data R)

include k A in
/-- Paper-facing module-finite Artin-algebra wrapper.  Finiteness of every
skeleton representative over the scalar base is automatic by transitivity. -/
theorem moduleFiniteArtin_literalRadicalQuotientCofiniteTwo_formula
    (hcard : 2 ≤ Nat.card ι) :
    Nat.card σ.QRadicalQuotientBoundaryPair =
        Nat.card σ.SRadicalQuotientBoundaryPair ∧
      σ.literalQuotientLevelCount (Nat.card ι - 2) =
          σ.literalSubobjectLevelCount (Nat.card ι - 2) ∧
        σ.literalQuotientLevelCount (Nat.card ι - 2) =
          Nat.choose (Nat.card σ.SimpleIndex) 2 +
            Nat.card σ.QRadicalQuotientBoundaryPair := by
  letI (i : ι) : Module k (σ.obj i) :=
    Module.restrictScalars k R (σ.obj i)
  letI (i : ι) : IsScalarTower k R (σ.obj i) :=
    IsScalarTower.restrictScalars k R (σ.obj i)
  letI (i : ι) : Module.Finite k (σ.obj i) :=
    Module.Finite.trans R (σ.obj i)
  exact
    σ.artinianBase_literalRadicalQuotientCofiniteTwo_formula
      (k := k) A hcard

end ModuleFiniteAlgebra

end OpConjecture.IndecomposableSkeleton
